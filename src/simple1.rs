use fugue::bytes::LE;
use fugue::ir::{AddressValue, LanguageDB};
use fuguex::machine::{Bound, Interpreter};

use fugue_typex::extract::PathExtractor;

const NSAMPLES: usize = 5;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let ldb = LanguageDB::from_directory_with("./processors", true)?;

    let tex = PathExtractor::<LE, 32>::new("/home/slt/projects/fugue-project/fugue-typex/experiments/simple1", &ldb)?;

    let space = tex.machine().interpreter().interpreter_space();

    let start = AddressValue::new(&*space, 0x080491fe);
    let end = AddressValue::new(&*space, 0x08049241);

    for _ in 0..NSAMPLES {
        tex.random_walk(start.clone(), Bound::address(end.clone()), true)?;
    }

    Ok(())
}
