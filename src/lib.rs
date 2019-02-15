#![feature(rustc_private, never_type, decl_macro)]
#![allow(intra_doc_link_resolution_failure)]

extern crate log;
extern crate rustc;
extern crate rustc_allocator;
extern crate rustc_codegen_ssa;
extern crate rustc_codegen_utils;
extern crate rustc_data_structures;
extern crate rustc_fs_util;
extern crate rustc_incremental;
extern crate rustc_mir;
extern crate rustc_target;
extern crate syntax;

use std::any::Any;
use std::ffi::CString;
use std::fs::File;
use std::os::raw::{c_char, c_int};
use std::sync::mpsc;

use rustc::dep_graph::DepGraph;
use rustc::middle::cstore::MetadataLoader;
use rustc::mir::mono::{Linkage as RLinkage, Visibility};
use rustc::session::{
    config::{OutputFilenames, OutputType},
    CompileIncomplete,
};
use rustc::ty::query::Providers;
use rustc_codegen_ssa::back::linker::LinkerInfo;
use rustc_codegen_ssa::CrateInfo;
use rustc_codegen_utils::codegen_backend::CodegenBackend;

use cranelift::codegen::settings;

use crate::constant::ConstantCx;
use crate::prelude::*;

mod abi;
mod allocator;
mod analyze;
mod archive;
mod base;
mod common;
mod constant;
mod intrinsics;
mod main_shim;
mod metadata;
mod pretty_clif;
mod trap;
mod unimpl;
mod unsize;
mod vtable;

mod prelude {
    pub use std::any::Any;
    pub use std::collections::{HashMap, HashSet};

    pub use syntax::ast::{FloatTy, IntTy, UintTy};
    pub use syntax::source_map::DUMMY_SP;

    pub use rustc::bug;
    pub use rustc::hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
    pub use rustc::mir::{self, interpret::AllocId, *};
    pub use rustc::session::{
        config::{CrateType, Lto},
        Session,
    };
    pub use rustc::ty::layout::{self, Abi, LayoutOf, Scalar, Size, TyLayout, VariantIdx};
    pub use rustc::ty::{
        self, subst::Substs, FnSig, Instance, InstanceDef, ParamEnv, PolyFnSig, Ty, TyCtxt,
        TypeAndMut, TypeFoldable,
    };
    pub use rustc_data_structures::{
        fx::{FxHashMap, FxHashSet},
        indexed_vec::Idx,
        sync::Lrc,
    };
    pub use rustc_mir::monomorphize::{collector, MonoItem};

    pub use rustc_codegen_ssa::mir::operand::{OperandRef, OperandValue};
    pub use rustc_codegen_ssa::traits::*;
    pub use rustc_codegen_ssa::{CodegenResults, CompiledModule, ModuleKind};

    pub use cranelift::codegen::ir::{
        condcodes::IntCC, function::Function, ExternalName, FuncRef, Inst, StackSlot,
    };
    pub use cranelift::codegen::isa::CallConv;
    pub use cranelift::codegen::Context;
    pub use cranelift::prelude::*;
    pub use cranelift_module::{Backend, DataContext, DataId, FuncId, Linkage, Module};
    pub use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

    pub use crate::abi::*;
    pub use crate::base::{trans_operand, trans_place};
    pub use crate::common::*;
    pub use crate::trap::*;
    pub use crate::unimpl::{unimpl, with_unimpl_span};
    pub use crate::{Caches, CodegenCx};
}

pub struct Caches<'tcx> {
    pub context: Context,
    pub vtables: HashMap<(Ty<'tcx>, Option<ty::PolyExistentialTraitRef<'tcx>>), DataId>,
}

impl<'tcx> Default for Caches<'tcx> {
    fn default() -> Self {
        Caches {
            context: Context::new(),
            vtables: HashMap::new(),
        }
    }
}

pub struct CodegenCx<'a, 'clif, 'tcx, B: Backend + 'static> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    module: &'clif mut Module<B>,
    ccx: ConstantCx,
    caches: Caches<'tcx>,
}

impl<'a, 'clif, 'tcx, B: Backend + 'static> CodegenCx<'a, 'clif, 'tcx, B> {
    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, module: &'clif mut Module<B>) -> Self {
        CodegenCx {
            tcx,
            module,
            ccx: ConstantCx::default(),
            caches: Caches::default(),
        }
    }

    fn finalize(self) {
        self.ccx.finalize(self.tcx, self.module);
    }
}

struct CraneliftCodegenBackend;

impl CodegenBackend for CraneliftCodegenBackend {
    fn init(&self, sess: &Session) {
        for cty in sess.opts.crate_types.iter() {
            match *cty {
                CrateType::Rlib | CrateType::Dylib | CrateType::Executable => {}
                _ => {
                    sess.err(&format!(
                        "Rustc codegen cranelift doesn't support output type {}",
                        cty
                    ));
                }
            }
        }
        match sess.lto() {
            Lto::Fat | Lto::Thin | Lto::ThinLocal => {
                sess.warn("Rustc codegen cranelift doesn't support lto");
            }
            Lto::No => {}
        }
        if sess.opts.cg.rpath {
            sess.err("rpath is not yet supported");
        }
        if sess.opts.debugging_opts.pgo_gen.is_some() {
            sess.err("pgo is not supported");
        }
    }

    fn metadata_loader(&self) -> Box<dyn MetadataLoader + Sync> {
        Box::new(crate::metadata::CraneliftMetadataLoader)
    }

    fn provide(&self, providers: &mut Providers) {
        rustc_codegen_utils::symbol_names::provide(providers);
        rustc_codegen_ssa::back::symbol_export::provide(providers);

        providers.target_features_whitelist = |_tcx, _cnum| Lrc::new(Default::default());
    }
    fn provide_extern(&self, providers: &mut Providers) {
        rustc_codegen_ssa::back::symbol_export::provide_extern(providers);
    }

    fn codegen_crate<'a, 'tcx>(
        &self,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        _rx: mpsc::Receiver<Box<dyn Any + Send>>,
    ) -> Box<dyn Any> {
        env_logger::init();
        if !tcx.sess.crate_types.get().contains(&CrateType::Executable)
            && std::env::var("SHOULD_RUN").is_ok()
        {
            tcx.sess
                .err("Can't JIT run non executable (SHOULD_RUN env var is set)");
        }

        tcx.sess.abort_if_errors();

        let metadata = tcx.encode_metadata();

        // TODO: move to the end of this function when compiling libcore doesn't have unimplemented stuff anymore
        save_incremental(tcx);
        tcx.sess.warn("Saved incremental data");

        let mut log = if cfg!(debug_assertions) {
            Some(File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/target/out/log.txt")).unwrap())
        } else {
            None
        };

        let mut jit_module: Module<SimpleJITBackend> = Module::new(SimpleJITBuilder::new());
        assert_eq!(pointer_ty(tcx), jit_module.target_config().pointer_type());

        let sig = Signature {
            params: vec![
                AbiParam::new(jit_module.target_config().pointer_type()),
                AbiParam::new(jit_module.target_config().pointer_type()),
            ],
            returns: vec![AbiParam::new(
                jit_module.target_config().pointer_type(), /*isize*/
            )],
            call_conv: CallConv::SystemV,
        };
        let main_func_id = jit_module
            .declare_function("main", Linkage::Import, &sig)
            .unwrap();

        codegen_cgus(tcx, &mut jit_module, &mut log);
        crate::allocator::codegen(tcx.sess, &mut jit_module);
        jit_module.finalize_definitions();

        tcx.sess.abort_if_errors();

        let finalized_main: *const u8 = jit_module.get_finalized_function(main_func_id);

        let f: extern "C" fn(c_int, *const *const c_char) -> c_int =
            unsafe { ::std::mem::transmute(finalized_main) };

        let args = ::std::env::var("JIT_ARGS").unwrap_or_else(|_| String::new());
        let args = args
            .split(" ")
            .chain(Some(&*tcx.crate_name(LOCAL_CRATE).as_str().to_string()))
            .map(|arg| CString::new(arg).unwrap())
            .collect::<Vec<_>>();
        let argv = args.iter().map(|arg| arg.as_ptr()).collect::<Vec<_>>();
        // TODO: Rust doesn't care, but POSIX argv has a NULL sentinel at the end

        let ret = f(args.len() as c_int, argv.as_ptr());

        jit_module.finish();
        std::process::exit(ret);
    }

    fn join_codegen_and_link(
        &self,
        res: Box<dyn Any>,
        sess: &Session,
        _dep_graph: &DepGraph,
        outputs: &OutputFilenames,
    ) -> Result<(), CompileIncomplete> {
        let res = *res
            .downcast::<CodegenResults>()
            .expect("Expected CraneliftCodegenBackend's CodegenResult, found Box<Any>");
        Ok(())
    }
}

fn build_isa(sess: &Session) -> Box<isa::TargetIsa + 'static> {
    use rustc::session::config::OptLevel;

    let mut flags_builder = settings::builder();
    flags_builder.enable("is_pic").unwrap();
    flags_builder.set("probestack_enabled", "false").unwrap(); // ___cranelift_probestack is not provided
    flags_builder.set("enable_verifier", if cfg!(debug_assertions) {
        "true"
    } else {
        "false"
    }).unwrap();

    // FIXME enable again when https://github.com/CraneStation/cranelift/issues/664 is fixed
    /*match sess.opts.optimize {
        OptLevel::No => {
            flags_builder.set("opt_level", "fastest").unwrap();
        }
        OptLevel::Less | OptLevel::Default => {}
        OptLevel::Aggressive => {
            flags_builder.set("opt_level", "best").unwrap();
        }
        OptLevel::Size | OptLevel::SizeMin => {
            sess.warn("Optimizing for size is not supported. Just ignoring the request");
        }
    }*/

    let flags = settings::Flags::new(flags_builder);
    cranelift::codegen::isa::lookup(sess.target.target.llvm_target.parse().unwrap())
        .unwrap()
        .finish(flags)
}

fn codegen_cgus<'a, 'tcx: 'a>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    module: &mut Module<impl Backend + 'static>,
    log: &mut Option<File>,
) {
    let (_, cgus) = tcx.collect_and_partition_mono_items(LOCAL_CRATE);
    let mono_items = cgus
        .iter()
        .map(|cgu| cgu.items().iter())
        .flatten()
        .map(|(&mono_item, &(linkage, vis))| (mono_item, (linkage, vis)))
        .collect::<FxHashMap<_, (_, _)>>();

    codegen_mono_items(tcx, module, log, mono_items);

    crate::main_shim::maybe_create_entry_wrapper(tcx, module);
}

fn codegen_mono_items<'a, 'tcx: 'a>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    module: &mut Module<impl Backend + 'static>,
    log: &mut Option<File>,
    mono_items: FxHashMap<MonoItem<'tcx>, (RLinkage, Visibility)>,
) {
    let mut cx = CodegenCx::new(tcx, module);
    time("codegen mono items", move || {
        for (mono_item, (linkage, vis)) in mono_items {
            unimpl::try_unimpl(tcx, log, || {
                let linkage = match (linkage, vis) {
                    (RLinkage::External, Visibility::Default) => Linkage::Export,
                    (RLinkage::Internal, Visibility::Default) => Linkage::Local,
                    // FIXME this should get external linkage, but hidden visibility,
                    // not internal linkage and default visibility
                    | (RLinkage::External, Visibility::Hidden) => Linkage::Export,
                    _ => panic!("{:?} = {:?} {:?}", mono_item, linkage, vis),
                };
                base::trans_mono_item(&mut cx, mono_item, linkage);
            });
        }

        cx.finalize();
    });
}

fn time<R>(name: &str, f: impl FnOnce() -> R) -> R {
    println!("[{}] start", name);
    let before = ::std::time::Instant::now();
    let res = f();
    let after = ::std::time::Instant::now();
    println!("[{}] end time: {:?}", name, after - before);
    res
}

fn save_incremental<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>) {
    rustc_incremental::assert_dep_graph(tcx);
    rustc_incremental::save_dep_graph(tcx);
    rustc_incremental::finalize_session_directory(tcx.sess, tcx.crate_hash(LOCAL_CRATE));
}

/// This is the entrypoint for a hot plugged rustc_codegen_cranelift
#[no_mangle]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    Box::new(CraneliftCodegenBackend)
}
