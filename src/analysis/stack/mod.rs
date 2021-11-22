use fugue_static::analyses::fixed_point::FixedPointForward;
use fugue_static::models::block::Block;
use fugue_static::traits::*;
use fugue_static::types::SimpleVar;
use fugue_static::graphs::entity::AsEntityGraph;

use fugue::bv::BitVec;
use fugue::ir::il::ecode::EntityId;

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::ops::Range;

pub type StackShift = Option<BitVec>;

pub struct StackBoundary<'ecode>(SimpleVar<'ecode>, Range<BitVec>);

impl<'ecode, E, G> FixedPointForward<'ecode, Block, E, G, StackShift> for StackBoundary<'ecode>
where E: 'ecode,
      G: AsEntityGraph<'ecode, Block, E> {
    type Err = Infallible;

    fn join(&mut self, current: StackShift, prev: &StackShift) -> Result<StackShift, Self::Err> {
        Ok(match (current, prev) {
            (None, None) => None,
            (None, Some(v)) => Some(v.clone()),
            (Some(v), None) => Some(v),
            (Some(v1), Some(v2)) => Some(if v1 <= *v2 { v1 } else { v2.clone() }),
        })
    }

    fn transfer(&mut self, block: &'ecode Block, current: Option<StackShift>) -> Result<StackShift, Self::Err> {
        Ok(None)
    }
}
