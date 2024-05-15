use std::path::Path;

use rustc_hash::FxHashMap;
use rustc_middle::ty::{self, TyCtxt};
use rustc_serialize::{opaque::FileEncoder, Encoder};
use rustc_type_ir::TyEncoder;

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.file_encoder.$name(value)
        })*
    }
}

pub struct ParalegalEncoder<'tcx> {
    file_encoder: FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
}

impl<'tcx> ParalegalEncoder<'tcx> {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            file_encoder: FileEncoder::new(path).unwrap(),
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
        }
    }

    pub fn finish(self) {
        self.file_encoder.finish().unwrap();
    }
}

impl<'a, 'tcx> Encoder for ParalegalEncoder<'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);

        emit_raw_bytes(&[u8]);
    }
}

impl<'tcx> TyEncoder for ParalegalEncoder<'tcx> {
    type I = TyCtxt<'tcx>;
    const CLEAR_CROSS_CRATE: bool = false;

    fn position(&self) -> usize {
        self.file_encoder.position()
    }

    fn type_shorthands(
        &mut self,
    ) -> &mut FxHashMap<<Self::I as rustc_type_ir::Interner>::Ty, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(
        &mut self,
    ) -> &mut FxHashMap<<Self::I as rustc_type_ir::Interner>::PredicateKind, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &<Self::I as rustc_type_ir::Interner>::AllocId) {
        unimplemented!()
    }
}
