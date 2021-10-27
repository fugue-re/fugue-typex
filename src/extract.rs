use fugue::bytes::Order;
use fugue::ir::LanguageDB;

use fuguex::concrete::ConcreteContext;
use fuguex::loader::{MappedDatabase, Error as LoaderError};
use fuguex::machine::{Interpreter, Machine};

use std::path::Path;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Loader(#[from] LoaderError),
}

#[derive(Clone)]
pub struct PathExtractor<O: Order, const OPERAND_SIZE: usize> {
    machine: Machine<ConcreteContext<O, String, { OPERAND_SIZE }>>,
}

impl<O: Order, const OPERAND_SIZE: usize> PathExtractor<O, { OPERAND_SIZE }> {
    pub fn new<P: AsRef<Path>>(program: P, language_db: &LanguageDB) -> Result<Self, Error> {
        Self::new_with(program, language_db, "gcc")
    }

    pub fn new_with<P: AsRef<Path>, C: AsRef<str>>(program: P, language_db: &LanguageDB, convention: C) -> Result<Self, Error> {
        let database = MappedDatabase::from_path(program, language_db)?
            .pcode_state_with(convention).left().unwrap();

        Ok(Self {
            machine: Machine::new(ConcreteContext::<O, _, { OPERAND_SIZE }>::from_loader(database)),
        })
    }

    pub fn fork(&self) -> Self {
        Self { machine: Machine::new(self.machine.interpreter().fork()) }
    }
}
