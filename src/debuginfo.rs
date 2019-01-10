extern crate gimli;

use crate::prelude::*;

use gimli::write::{
    Address, AttributeValue, DebugAbbrev, DebugInfo, DebugStr, DebugLine, EndianVec, Result, SectionId,
    StringTable, UnitId, UnitTable, Writer, CompilationUnit, DebugLineOffsets,
    UnitEntryId, LineProgram, LineProgramTable,
};
use gimli::Format;

// FIXME: use target endian
use gimli::NativeEndian;

use faerie::*;

struct DebugReloc {
    offset: u32,
    size: u8,
    name: String,
    addend: i64,
}

pub struct DebugContext {
    strings: StringTable,
    units: UnitTable,
    unit_id: UnitId,
    line_programs: LineProgramTable,
    symbol_names: Vec<String>,
}

impl DebugContext {
    pub fn new(tcx: TyCtxt, address_size: u8) -> Self {
        let mut units = UnitTable::default();
        let mut strings = StringTable::default();
        // TODO: this should be configurable
        let version = 4;
        let unit_id = units.add(CompilationUnit::new(version, address_size, Format::Dwarf32));
        {
            // FIXME: how to get version when building out of tree?
            // Normally this would use option_env!("CFG_VERSION").
            let producer = format!("cranelift fn (rustc version {})", "unknown version");
            let name = match tcx.sess.local_crate_source_file {
                Some(ref path) => strings.add(&*path.to_string_lossy()),
                None => strings.add(&*tcx.crate_name(LOCAL_CRATE).as_str()),
            };
            let comp_dir = strings.add(&*tcx.sess.working_dir.0.to_string_lossy());

            let unit = units.get_mut(unit_id);
            let root = unit.root();
            let root = unit.get_mut(root);
            root.set(
                gimli::DW_AT_producer,
                AttributeValue::StringRef(strings.add(producer)),
            );
            root.set(
                gimli::DW_AT_language,
                AttributeValue::Language(gimli::DW_LANG_Rust),
            );
            //root.set(gimli::DW_AT_name, AttributeValue::StringRef(name));
            root.set(gimli::DW_AT_comp_dir, AttributeValue::StringRef(comp_dir));
            // FIXME: DW_AT_stmt_list
            // FIXME: DW_AT_low_pc
            // FIXME: DW_AT_ranges
        }

        DebugContext {
            strings,
            units,
            unit_id,
            line_programs: LineProgramTable::default(),
            symbol_names: Vec::new(),
        }
    }

    pub fn emit(&self, artifact: &mut Artifact) {
        let mut debug_abbrev = DebugAbbrev::from(WriterRelocate::new(self));
        let mut debug_info = DebugInfo::from(WriterRelocate::new(self));
        let mut debug_str = DebugStr::from(WriterRelocate::new(self));
        let mut debug_line = DebugLine::from(WriterRelocate::new(self));

        let debug_line_offsets = self.line_programs.write(&mut debug_line).unwrap();
        let debug_str_offsets = self.strings.write(&mut debug_str).unwrap();
        self.units
            .write(&mut debug_abbrev, &mut debug_info, &debug_line_offsets, &debug_str_offsets)
            .unwrap();

        artifact.declare_with(SectionId::DebugAbbrev.name(), Decl::DebugSection, debug_abbrev.0.writer.into_vec());
        artifact.declare_with(SectionId::DebugInfo.name(), Decl::DebugSection, debug_info.0.writer.into_vec());
        artifact.declare_with(SectionId::DebugStr.name(), Decl::DebugSection, debug_str.0.writer.into_vec());
        artifact.declare_with(SectionId::DebugLine.name(), Decl::DebugSection, debug_line.0.writer.into_vec());


        for reloc in debug_abbrev.0.relocs {
            artifact.link_with(
                faerie::Link {
                    from: SectionId::DebugAbbrev.name(),
                    to: &reloc.name,
                    at: u64::from(reloc.offset),
                },
                faerie::Reloc::Debug {
                    size: reloc.size,
                    addend: reloc.addend as i32,
                },
            ).expect("faerie relocation error");
        }

        for reloc in debug_info.0.relocs {
            artifact.link_with(
                faerie::Link {
                    from: SectionId::DebugInfo.name(),
                    to: &reloc.name,
                    at: u64::from(reloc.offset),
                },
                faerie::Reloc::Debug {
                    size: reloc.size,
                    addend: reloc.addend as i32,
                },
            ).expect("faerie relocation error");
        }

        for reloc in debug_str.0.relocs {
            artifact.link_with(
                faerie::Link {
                    from: SectionId::DebugStr.name(),
                    to: &reloc.name,
                    at: u64::from(reloc.offset),
                },
                faerie::Reloc::Debug {
                    size: reloc.size,
                    addend: reloc.addend as i32,
                },
            ).expect("faerie relocation error");
        }

        for reloc in debug_line.0.relocs {
            artifact.link_with(
                faerie::Link {
                    from: SectionId::DebugLine.name(),
                    to: &reloc.name,
                    at: u64::from(reloc.offset),
                },
                faerie::Reloc::Debug {
                    size: reloc.size,
                    addend: reloc.addend as i32,
                },
            ).expect("faerie relocation error");
        }
    }

    fn section_name(&self, id: SectionId) -> String {
        id.name().to_string()
    }
}

pub struct FunctionDebugContext<'a> {
    debug_context: &'a mut DebugContext,
    mir_span: Span,
    entry_id: UnitEntryId,
    symbol: usize,
}

impl<'a> FunctionDebugContext<'a> {
    pub fn new(
        tcx: TyCtxt,
        debug_context: &'a mut DebugContext,
        mir: &Mir,
        name: &str,
        _sig: &Signature,
    ) -> Self {
        let unit = debug_context.units.get_mut(debug_context.unit_id);
        // FIXME: add to appropriate scope intead of root
        let scope = unit.root();
        let entry_id = unit.add(scope, gimli::DW_TAG_subprogram);
        let entry = unit.get_mut(entry_id);
        let name_id = debug_context.strings.add(name);
        let dummy_name_id = debug_context.strings.add("dummy".to_string() + name);
        let loc = tcx.sess.source_map().lookup_char_pos(mir.span.lo());
        // FIXME: use file index into unit's line table
        // FIXME: specify directory too?
        let file_id = debug_context.strings.add(loc.file.name.to_string());
        entry.set(gimli::DW_AT_linkage_name, AttributeValue::StringRef(name_id));
        entry.set(gimli::DW_AT_name, AttributeValue::StringRef(dummy_name_id));

        let symbol = debug_context.symbol_names.len();
        debug_context.symbol_names.push(name.to_string());

        entry.set(gimli::DW_AT_low_pc, AttributeValue::Address(Address::Relative {
            symbol,
            addend: 0,
        }));
        entry.set(gimli::DW_AT_decl_file, AttributeValue::StringRef(file_id));
        entry.set(gimli::DW_AT_decl_line, AttributeValue::Udata(loc.line as u64));
        // FIXME: probably omit this
        entry.set(gimli::DW_AT_decl_column, AttributeValue::Udata(loc.col.to_usize() as u64));


        let int_id = unit.add(scope, gimli::DW_TAG_base_type);
        let int = unit.get_mut(int_id);
        let int_name = debug_context.strings.add("int");
        int.set(gimli::DW_AT_byte_size, AttributeValue::Data1([4]));
        int.set(gimli::DW_AT_encoding, AttributeValue::Data1([5]));
        int.set(gimli::DW_AT_name, AttributeValue::StringRef(int_name));

        let param_id = unit.add(entry_id, gimli::DW_TAG_formal_parameter);
        let param = unit.get_mut(param_id);
        param.set(gimli::DW_AT_name, AttributeValue::StringRef(int_name));
        param.set(gimli::DW_AT_type, AttributeValue::ThisUnitEntryRef(int_id));

        FunctionDebugContext {
            debug_context,
            mir_span: mir.span,
            entry_id,
            symbol,
        }
    }

    pub fn define(
        &mut self,
        tcx: TyCtxt,
        //module: &mut Module<impl Backend>,
        size: u32,
        context: &Context,
        isa: &cranelift::codegen::isa::TargetIsa,
        spans: &[Span],
    ) {
        use byteorder::ByteOrder;

        let unit = self.debug_context.units.get_mut(self.debug_context.unit_id);
        // FIXME: add to appropriate scope intead of root
        let scope = unit.root();
        let entry = unit.get_mut(self.entry_id);
        let mut size_array = [0; 8];
        byteorder::LittleEndian::write_u64(&mut size_array, size as u64);
        entry.set(gimli::DW_AT_high_pc, AttributeValue::Data8(size_array));

        let file = tcx.sess.source_map().lookup_char_pos(self.mir_span.lo()).file.name.to_string();

        let mut line_program = LineProgram::new(
            4,
            8,
            Format::Dwarf32,
            1,
            1,
            -5,
            14,
            b"",
            b"",
            None,
        );

        let default_dir = line_program.default_directory();
        let the_file = line_program.add_file(
            b"mini_core_hello_world.rs",
            default_dir,
            None,
        );

        line_program.begin_sequence(Some(Address::Relative {
            symbol: self.symbol,
            addend: 0,
        }));
        line_program.row().file = the_file;

        let encinfo = isa.encoding_info();
        let func = &context.func;
        let mut ebbs = func.layout.ebbs().collect::<Vec<_>>();
        ebbs.sort_by_key(|ebb|func.offsets[*ebb]); // Ensure inst offsets always increase
        for ebb in ebbs {
            for (offset, inst, size) in func.inst_offsets(ebb, &encinfo) {
                let srcloc = func.srclocs[inst];
                if !srcloc.is_default() {
                    let span = spans[srcloc.bits() as usize];
                    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
                    let file = loc.file.name.to_string();
                    tcx.sess
                        .warn(&format!("srcloc {} {}:{}:{}", offset, file, loc.line, loc.col.to_usize()));
                    line_program.row().address_offset = offset as u64;
                    line_program.row().line = loc.line as u64;
                    line_program.generate_row();
                }
            }
        }

        let address_offset = line_program.row().address_offset;
        line_program.end_sequence(address_offset);
        println!("{:?}", line_program);
        self.debug_context.line_programs.add(line_program);
    }
}

struct WriterRelocate<'a> {
    ctx: &'a DebugContext,
    relocs: Vec<DebugReloc>,
    writer: EndianVec<NativeEndian>,
}

impl<'a> WriterRelocate<'a> {
    fn new(ctx: &'a DebugContext) -> Self {
        WriterRelocate {
            ctx,
            relocs: Vec::new(),
            writer: EndianVec::new(NativeEndian),
        }
    }
}

impl<'a> Writer for WriterRelocate<'a> {
    type Endian = NativeEndian;

    fn endian(&self) -> Self::Endian {
        self.writer.endian()
    }

    fn len(&self) -> usize {
        self.writer.len()
    }

    fn write(&mut self, bytes: &[u8]) -> Result<()> {
        self.writer.write(bytes)
    }

    fn write_at(&mut self, offset: usize, bytes: &[u8]) -> Result<()> {
        self.writer.write_at(offset, bytes)
    }

    fn write_address(&mut self, address: Address, size: u8) -> Result<()> {
        match address {
            Address::Absolute(val) => self.write_word(val, size),
            Address::Relative { symbol, addend } => {
                let offset = self.len() as u64;
                self.relocs.push(DebugReloc {
                    offset: offset as u32,
                    size,
                    name: self.ctx.symbol_names[symbol].clone(),
                    addend: addend as i64,
                });
                self.write_word(0, size)
            }
        }
    }

    fn write_offset(&mut self, val: usize, section: SectionId, size: u8) -> Result<()> {
        let offset = self.len() as u32;
        let name = self.ctx.section_name(section);
        self.relocs.push(DebugReloc {
            offset,
            size,
            name,
            addend: val as i64,
        });
        self.write_word(0, size)
    }

    fn write_offset_at(
        &mut self,
        offset: usize,
        val: usize,
        section: SectionId,
        size: u8,
    ) -> Result<()> {
        let name = self.ctx.section_name(section);
        self.relocs.push(DebugReloc {
            offset: offset as u32,
            size,
            name,
            addend: val as i64,
        });
        self.write_word_at(offset, 0, size)
    }
}
