use rustc::middle::cstore::MetadataLoader;
use rustc_data_structures::owning_ref::{self, OwningRef};
use std::path::Path;

use object::{Object, ObjectSection};

pub struct CraneliftMetadataLoader;

impl MetadataLoader for CraneliftMetadataLoader {
    fn get_rlib_metadata(
        &self,
        _target: &::rustc_target::spec::Target,
        path: &Path,
    ) -> Result<owning_ref::ErasedBoxRef<[u8]>, String> {
        let file = ::std::fs::read(path).map_err(|e| format!("{:?}", e))?;
        let obj = ::object::File::parse(&file).map_err(|e| format!("{:?}", e))?;

        for section in obj.sections() {
            println!("section name: {:?}", section.name());
            if section.name().is_some() && section.name().unwrap().contains(".rustc.clif_metadata")
            {
                println!("found");
                let buf: Vec<u8> = section.data().into_owned();
                let buf: OwningRef<Vec<u8>, [u8]> = OwningRef::new(buf).into();
                return Ok(rustc_erase_owner!(buf.map_owner_box()));
            }
        }

        Err("couldn't find metadata entry".to_string())
    }

    fn get_dylib_metadata(
        &self,
        target: &::rustc_target::spec::Target,
        path: &Path,
    ) -> Result<owning_ref::ErasedBoxRef<[u8]>, String> {
        self.get_rlib_metadata(target, path)
    }
}
