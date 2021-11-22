use intervals::collections::DisjointIntervalSet;
use intervals::Interval;

use fugue::bytes::Order;
use fugue::db::Segment;
use fugue::ir::il::pcode::{Operand, PCodeOp, Register};
use fugue::ir::il::Location;
use fugue::ir::{Address, AddressValue, IntoAddress, LanguageDB};

use fugue_static::analyses::fixed_point::FixedPointForward;
use fugue_static::analyses::reaching_definitions::{DefinitionMap, ReachingDefinitions};
use fugue_static::models::program::{Program, Error as ProgramModelError};
use fugue_static::transforms::{AliasedVars, NormaliseAliases, SSA};
use fugue_static::visualise::AsDot;

use fuguex::concrete::driver::RandomWalker;
use fuguex::concrete::hooks::{ClonableHookConcrete, HookConcrete};
use fuguex::concrete::microx::{PolicyHook, ZeroPolicy};
use fuguex::concrete::{ConcreteContext, ConcreteState, Error as InterpError};
use fuguex::hooks::types::{
    Error as HookError, HookAction, HookCallAction, HookOutcome, HookStepAction,
};
use fuguex::loader::{Error as LoaderError, MappedDatabase};
use fuguex::machine::{Bound, Interpreter, Machine};
use fuguex::state::pcode::Error as ConcreteError;
use fuguex::state::register::ReturnLocation;

use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::marker::PhantomData;
use std::path::Path;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Loader(#[from] LoaderError),
    #[error(transparent)]
    State(#[from] ConcreteError),
    #[error(transparent)]
    ProgramModel(#[from] ProgramModelError),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AccessKind {
    Read,
    Write,
}

impl Display for AccessKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read => write!(f, "read"),
            Self::Write => write!(f, "write"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallInfo {
    source_address: Address,
    target_function: Address,
    stack_pointer: Address,
    expected_return: Address,
}

// we follow the same logging format as proposed by Rolles
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryAccess {
    allocation: Address,
    allocation_size: usize,

    access_stack: bool,
    access_region: Option<usize>,
    access_source_pc: Address,
    access_source_sp: Address,
    access_offset: i64,
    access_size: usize,

    access_kind: AccessKind,
}

#[derive(Clone)]
pub struct ObserveMemoryAccess<O> {
    accesses: BTreeMap<MemoryAccess, usize>,
    allocations: DisjointIntervalSet<Address>,
    stack_range: Interval<Address>,
    stack_init: Address,
    call_stack: Vec<CallInfo>,
    region_stack: Vec<Interval<Address>>,
    marker: PhantomData<O>,
}

pub struct DisplayAccesses<'a, O: Order>(&'a ObserveMemoryAccess<O>);

impl<'a, O: Order> Display for DisplayAccesses<'a, O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for access in self.0.accesses.keys() {
            writeln!(
                f,
                "{} (sp: {}): [{}][{}] {}{}{}:{} ({})",
                access.access_source_pc,
                access.access_source_sp,
                if access.access_stack {
                    if access.access_offset.is_negative() {
                        "stack/local"
                    } else {
                        "stack"
                    }
                } else {
                    "alloc"
                },
                if let Some(r) = access.access_region {
                    format!("R{}", r)
                } else {
                    "N/A".to_string()
                },
                if access.access_stack {
                    "SP".to_string()
                } else {
                    format!("{}", access.allocation)
                },
                if access.access_offset.is_negative() {
                    "-"
                } else {
                    "+"
                },
                access.access_offset.abs(),
                access.access_size,
                access.access_kind,
            )?;
        }
        Ok(())
    }
}

impl<O: Order> ObserveMemoryAccess<O> {
    pub fn new<I>(stack_range: I, stack_init: Address) -> Self
    where
        I: Into<Interval<Address>>,
    {
        let stack_range = stack_range.into();
        println!("stack range: {}-{}", stack_range.start(), stack_range.end());
        Self {
            accesses: BTreeMap::new(),
            allocations: DisjointIntervalSet::new(),
            stack_range,
            stack_init,
            call_stack: Vec::new(),
            region_stack: Vec::new(),
            marker: PhantomData,
        }
    }

    pub fn observe_access(
        &mut self,
        source_pc: Address,
        source_sp: Address,
        address: Address,
        size: usize,
        kind: AccessKind,
    ) {
        let entry = if let Some(alloc) = self.allocations.find(address..=address + (size - 1)) {
            let allocation = alloc.interval().start();
            let allocation_size =
                1 + usize::from(*alloc.interval().end() - *alloc.interval().start());

            MemoryAccess {
                allocation: allocation.clone(),
                allocation_size,

                access_stack: false,
                access_region: None,
                access_source_pc: source_pc,
                access_source_sp: source_sp,
                access_offset: address.offset().wrapping_sub(allocation.offset()) as i64,
                access_size: size,

                access_kind: kind,
            }
        } else if *self.stack_range.start() <= address && *self.stack_range.end() >= address + (size - 1) {
            let allocation = if let Some(last) = self.call_stack.last() {
                last.stack_pointer
            } else {
                self.stack_init
            };

            /*
            println!("live regions (access: {}):", address);
            for (i, r) in self.region_stack.iter().enumerate() {
                println!("R{}: {}-{}", i, r.start(), r.end());
            }
            */

            MemoryAccess {
                allocation,
                allocation_size: size, // FIXME: no idea?

                access_stack: true,
                access_region: self.region_stack.iter().enumerate().find_map(|(i, iv)| {
                    if *iv.start() <= address && *iv.end() >= address + (size - 1) {
                        Some(i)
                    } else {
                        None
                    }
                }),
                access_source_pc: source_pc,
                access_source_sp: source_sp,
                access_offset: address.offset().wrapping_sub(allocation.offset()) as i64,
                access_size: size,
                access_kind: kind,
            }
        } else {
            return;
        };

        *self.accesses.entry(entry).or_default() += 1;
    }

    pub fn display_accesses<'a>(&'a self) -> DisplayAccesses<'a, O> {
        DisplayAccesses(self)
    }
}

impl<O: Order> HookConcrete for ObserveMemoryAccess<O> {
    type State = ConcreteState<O>;
    type Error = ConcreteError;
    type Outcome = ();

    fn hook_memory_read(
        &mut self,
        state: &mut Self::State,
        address: &Address,
        size: usize,
    ) -> Result<HookOutcome<HookAction<Self::Outcome>>, HookError<Self::Error>> {
        let pc = state.program_counter_value().map_err(HookError::state)?;
        let sp = state.stack_pointer_value().map_err(HookError::state)?;

        self.observe_access(pc, sp, address.clone(), size, AccessKind::Read);

        Ok(HookAction::Pass.into())
    }

    fn hook_memory_write(
        &mut self,
        state: &mut Self::State,
        address: &Address,
        size: usize,
        _value: &[u8],
    ) -> Result<HookOutcome<HookAction<Self::Outcome>>, HookError<Self::Error>> {
        let pc = state.program_counter_value().map_err(HookError::state)?;
        let sp = state.stack_pointer_value().map_err(HookError::state)?;

        self.observe_access(pc, sp, address.clone(), size, AccessKind::Write);

        Ok(HookAction::Pass.into())
    }

    fn hook_register_write(
        &mut self,
        state: &mut Self::State,
        register: &Register,
        _value: &[u8],
    ) -> Result<HookOutcome<HookAction<Self::Outcome>>, HookError<Self::Error>> {
        if register.offset() == state.registers().stack_pointer().offset() {
            let pc = state.program_counter_value().map_err(HookError::state)?;
            let sp = state.stack_pointer_value().map_err(HookError::state)?;
            // new SP -> determine if GEN/KILL/NO-OP
            if let Some(iv) = self.region_stack.last() {
                if sp > *iv.start() {
                    // KILL
                    while !self.region_stack.is_empty() {
                        let iv = self.region_stack.last().unwrap();
                        if sp > *iv.start() {
                            let (s, e) = self.region_stack.pop().unwrap().into_inner();
                            println!("[KILL] {}: {}-{}", pc, s, e);
                            // inside region
                            if sp <= e {
                                // split the region
                                println!("[GEN] {}: {}-{}", pc, sp, e);
                                self.region_stack.push(Interval::from(sp..=e));
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                } else if sp < *iv.start() {
                    // GEN
                    let e = *iv.start() - 1usize;
                    let s = sp;
                    println!("[GEN] {}: {}-{}", pc, s, e);
                    self.region_stack.push(Interval::from(s..=e));
                } // else { // NOTE: we do not generate empty regions
            } else if sp != self.stack_init {
                // GEN fresh (and ensure actually moved!)
                let e = self.stack_init - 1usize;
                let s = sp;
                println!("[GEN] {}: {}-{}", pc, s, e);
                self.region_stack.push(Interval::from(s..=e));
            }
        }
        Ok(HookAction::Pass.into())
    }

    fn hook_call(
        &mut self,
        state: &mut Self::State,
        destination: &Address,
    ) -> Result<HookOutcome<HookCallAction<Self::Outcome>>, HookError<Self::Error>> {
        let pc = state.program_counter_value().map_err(HookError::state)?;
        let sp = state.stack_pointer_value().map_err(HookError::state)?;

        let return_address = match &*state.registers().return_location() {
            ReturnLocation::Register(ref operand) => state.get_address(&operand),
            ReturnLocation::Relative(ref operand, offset) => {
                let address = state.get_address(operand).map_err(HookError::state)?;
                let operand = Operand::Address {
                    value: Address::new(&*state.memory_space(), u64::from(address + *offset)),
                    size: state.memory_space().address_size(),
                };
                state.get_address(&operand)
            }
        }
        .map_err(HookError::state)?;

        self.call_stack.push(CallInfo {
            source_address: pc,
            stack_pointer: sp,
            target_function: *destination,
            expected_return: return_address,
        });

        Ok(HookCallAction::Pass.into())
    }

    fn hook_operation_step(
        &mut self,
        state: &mut Self::State,
        location: &Location,
        operation: &PCodeOp,
    ) -> Result<HookOutcome<HookStepAction<Self::Outcome>>, HookError<Self::Error>> {
        //println!("{} {}", location, operation);

        let sp = state.stack_pointer_value().map_err(HookError::state)?;

        if matches!(self.call_stack.last(), Some(v) if sp > v.stack_pointer) {
            self.call_stack.pop();
        }

        Ok(HookStepAction::Pass.into())
    }
}

impl<O: Order> ClonableHookConcrete for ObserveMemoryAccess<O> {}

#[derive(Clone)]
pub struct SkipCall<O> {
    ranges: DisjointIntervalSet<Address>,
    marker: PhantomData<O>,
}

impl<O> SkipCall<O> {
    pub fn from_iter<'a, I: IntoIterator<Item = &'a Segment>>(iter: I) -> Self {
        Self {
            ranges: iter
                .into_iter()
                .map(|s| {
                    let start = Address::from(s.address());
                    let end = start + (s.len() - 1);
                    start..=end
                })
                .collect(),
            marker: PhantomData,
        }
    }
}

impl<O: Order> HookConcrete for SkipCall<O> {
    type State = ConcreteState<O>;
    type Error = ConcreteError;
    type Outcome = ();

    fn hook_call(
        &mut self,
        _state: &mut Self::State,
        destination: &Address,
    ) -> Result<HookOutcome<HookCallAction<Self::Outcome>>, HookError<Self::Error>> {
        if self.ranges.contains_point(destination) {
            Ok(HookCallAction::Skip.into())
        } else {
            Ok(HookCallAction::Pass.into())
        }
    }
}

impl<O: Order> ClonableHookConcrete for SkipCall<O> {}

#[derive(Clone)]
pub struct PathExtractor<O: Order, const OPERAND_SIZE: usize> {
    machine: Machine<ConcreteContext<O, (), { OPERAND_SIZE }>>,
}

impl<O: Order, const OPERAND_SIZE: usize> PathExtractor<O, { OPERAND_SIZE }> {
    pub fn new<P: AsRef<Path>>(program: P, language_db: &LanguageDB) -> Result<Self, Error> {
        Self::new_with(program, language_db, "gcc")
    }

    pub fn new_with<P: AsRef<Path>, C: AsRef<str>>(
        program: P,
        language_db: &LanguageDB,
        convention: C,
    ) -> Result<Self, Error> {
        let database = MappedDatabase::from_path(program, language_db)?
            .pcode_state_with(convention)
            .left()
            .unwrap();

        let db = database.database();
        let program = Program::new(&db)?;
        let registers = AliasedVars::registers(&program);
        for fcn in program.functions().values() {
            let mut cfg = fcn.cfg(&program);
            let mut registers = registers.clone(); // FIXME
            cfg.normalise_aliases(&mut registers);
            cfg.ssa();

            println!("[i] processing function: {}", fcn.symbol());

            let mut rd = ReachingDefinitions::default();
            let rds = rd.analyse::<BTreeMap<_, _>>(&cfg).unwrap();
            println!("{:?}", rds);
        }

        let mut machine = Machine::new(ConcreteContext::<O, _, { OPERAND_SIZE }>::from_loader(
            database,
        ));

        let microx = PolicyHook::new(ZeroPolicy::<_, _, ()>::default());

        if let Some(db) = machine.interpreter().database().cloned() {
            // FIXME!!!
            machine.interpreter_mut().add_hook(
                "skip-externs",
                SkipCall::from_iter(db.segments().iter().filter_map(|(_, s)| {
                    if s.is_external() || s.name().contains("got") || s.name().contains("plt") {
                        Some(s)
                    } else {
                        None
                    }
                })),
            )
        }

        machine.interpreter_mut().add_hook("microx-access", microx);

        Ok(Self { machine })
    }

    pub fn initialise_stack<A: IntoAddress>(&mut self, base: A, size: usize) -> Result<(), Error> {
        let space = self.machine.interpreter().interpreter_space();
        let stack_base = base.into_address(&space);

        let stack_init = stack_base + 0x1000usize;
        let observer =
            ObserveMemoryAccess::new(stack_base..=(stack_base + size - 1usize), stack_init);

        self.machine
            .interpreter_mut()
            .add_hook("memory-access", observer);

        self.machine
            .interpreter_mut()
            .state_mut()
            .memory_mut()
            .static_mapping("stack", stack_base, size)
            .map_err(ConcreteError::Memory)?;

        self.machine
            .interpreter_mut()
            .state_mut()
            .set_stack_pointer_value(stack_init)?;

        Ok(())
    }

    pub fn random_walk<L: Into<Location>>(
        &self,
        from: L,
        until: Bound<AddressValue>,
        display: bool,
    ) -> Result<Option<InterpError>, Error> {
        let base = 0xf000_0000u32;
        let delta = rand::random::<u16>() as u32 & !0xf;

        let mut nself = self.fork();

        nself.initialise_stack(base + delta, 0x10000)?;
        nself
            .machine_mut()
            .interpreter_mut()
            .add_hook("random-walker", RandomWalker::new_small());

        let e = if let Err(err) = nself.machine_mut().step_until(from, until) {
            Some(err)
        } else {
            None
        };

        if display && e.is_none() {
            println!(
                "{}",
                nself
                    .machine()
                    .interpreter()
                    .find_hook::<_, ObserveMemoryAccess<O>>("memory-access")
                    .unwrap()
                    .display_accesses()
            );
        }

        Ok(e)
    }

    pub fn fork(&self) -> Self {
        Self {
            machine: Machine::new(self.machine.interpreter().fork()),
        }
    }

    pub fn machine(&self) -> &Machine<ConcreteContext<O, (), { OPERAND_SIZE }>> {
        &self.machine
    }

    pub fn machine_mut(&mut self) -> &mut Machine<ConcreteContext<O, (), { OPERAND_SIZE }>> {
        &mut self.machine
    }

    pub fn memory_accesses(&self) -> &BTreeMap<MemoryAccess, usize> {
        self.machine
            .interpreter()
            .find_hook::<_, ObserveMemoryAccess<O>>("memory-access")
            .map(|v| &v.accesses)
            .unwrap()
    }

    pub fn memory_accesses_mut(&mut self) -> &mut BTreeMap<MemoryAccess, usize> {
        self.machine
            .interpreter_mut()
            .find_hook_mut::<_, ObserveMemoryAccess<O>>("memory-access")
            .map(|v| &mut v.accesses)
            .unwrap()
    }
}
