//! Readers and writers for the intermediate artifacts we store per crate.
//!
//! Most of this code is adapted/copied from `EncodeContext` and `DecodeContext` in
//! `rustc_metadata`.
//!
//! Note that the methods pertaining to allocations of `AllocId`'s are
//! unimplemented and will cause a crash if you try to stick an `AllocId` into
//! the Paralegal artifact.

use std::path::Path;
use std::{num::NonZeroU64, path::PathBuf};

use rustc_const_eval::interpret::AllocId;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefIndex};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_serialize::{
    opaque::{FileEncoder, MemDecoder},
    Decodable, Decoder, Encodable, Encoder,
};
use rustc_span::{
    source_map::StableSourceFileId, BytePos, FileName, RealFileName, Span, SpanData, SyntaxContext,
    DUMMY_SP,
};
use rustc_type_ir::{TyDecoder, TyEncoder};

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.file_encoder.$name(value)
        })*
    }
}

pub struct ParalegalEncoder<'tcx> {
    tcx: TyCtxt<'tcx>,
    file_encoder: FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
}

impl<'tcx> ParalegalEncoder<'tcx> {
    pub fn new(path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            file_encoder: FileEncoder::new(path).unwrap(),
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
        }
    }

    pub fn finish(self) {
        self.file_encoder.finish().unwrap();
    }
}

const CLEAR_CROSS_CRATE: bool = false;

impl<'tcx> Encoder for ParalegalEncoder<'tcx> {
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
    const CLEAR_CROSS_CRATE: bool = CLEAR_CROSS_CRATE;

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
        u64::from(alloc_id.0).encode(self)
    }
}

impl<'tcx> Encodable<ParalegalEncoder<'tcx>> for CrateNum {
    fn encode(&self, s: &mut ParalegalEncoder<'tcx>) {
        s.tcx.stable_crate_id(*self).encode(s)
    }
}

pub struct ParalegalDecoder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    mem_decoder: MemDecoder<'a>,
    shorthand_map: FxHashMap<usize, Ty<'tcx>>,
}

impl<'tcx, 'a> ParalegalDecoder<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, buf: &'a [u8]) -> Self {
        Self {
            tcx,
            mem_decoder: MemDecoder::new(buf, 0),
            shorthand_map: Default::default(),
        }
    }
}

impl<'tcx, 'a> TyDecoder for ParalegalDecoder<'tcx, 'a> {
    const CLEAR_CROSS_CRATE: bool = CLEAR_CROSS_CRATE;

    type I = TyCtxt<'tcx>;

    fn interner(&self) -> Self::I {
        self.tcx
    }

    fn cached_ty_for_shorthand<F>(
        &mut self,
        shorthand: usize,
        or_insert_with: F,
    ) -> <Self::I as ty::Interner>::Ty
    where
        F: FnOnce(&mut Self) -> <Self::I as ty::Interner>::Ty,
    {
        if let Some(ty) = self.shorthand_map.get(&shorthand) {
            return *ty;
        }
        let ty = or_insert_with(self);
        self.shorthand_map.insert(shorthand, ty);
        ty
    }

    fn decode_alloc_id(&mut self) -> <Self::I as ty::Interner>::AllocId {
        AllocId(NonZeroU64::new(u64::decode(self)).unwrap())
    }

    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_opaque = MemDecoder::new(self.mem_decoder.data(), pos);
        let old_opaque = std::mem::replace(&mut self.mem_decoder, new_opaque);
        let r = f(self);
        self.mem_decoder = old_opaque;
        r
    }
}

macro_rules! decoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self) -> $ty {
            self.mem_decoder.$name()
        })*
    }
}

impl<'tcx, 'a> Decoder for ParalegalDecoder<'tcx, 'a> {
    decoder_methods! {
        read_usize(usize);
        read_u128(u128);
        read_u64(u64);
        read_u32(u32);
        read_u16(u16);
        read_u8(u8);
        read_isize(isize);
        read_i128(i128);
        read_i64(i64);
        read_i32(i32);
        read_i16(i16);
    }
    fn position(&self) -> usize {
        self.mem_decoder.position()
    }
    fn peek_byte(&self) -> u8 {
        self.mem_decoder.peek_byte()
    }
    fn read_raw_bytes(&mut self, len: usize) -> &[u8] {
        self.mem_decoder.read_raw_bytes(len)
    }
}

impl<'tcx, 'a> Decodable<ParalegalDecoder<'tcx, 'a>> for CrateNum {
    fn decode(d: &mut ParalegalDecoder<'tcx, 'a>) -> Self {
        d.tcx.stable_crate_id_to_crate_num(Decodable::decode(d))
    }
}

impl<'tcx> Encodable<ParalegalEncoder<'tcx>> for DefIndex {
    fn encode(&self, s: &mut ParalegalEncoder<'tcx>) {
        self.as_u32().encode(s)
    }
}

impl<'tcx, 'a> Decodable<ParalegalDecoder<'tcx, 'a>> for DefIndex {
    fn decode(d: &mut ParalegalDecoder<'tcx, 'a>) -> Self {
        Self::from_u32(u32::decode(d))
    }
}

// const TAG_PARTIAL_SPAN: u8 = 0;
// const TAG_VALID_SPAN_FULL: u8 = 1;

// impl<'tcx> Encodable<ParalegalEncoder<'tcx>> for Span {
//     fn encode(&self, s: &mut ParalegalEncoder<'tcx>) {
//         self.data().encode(s)
//     }
// }

// impl<'tcx> Encodable<ParalegalEncoder<'tcx>> for SpanData {
//     fn encode(&self, s: &mut ParalegalEncoder<'tcx>) {
//         if self.is_dummy() {
//             return TAG_PARTIAL_SPAN.encode(s);
//         }
//         let source_map = s.tcx.sess.source_map();
//         let source_file = source_map.lookup_source_file(self.lo);
//         if !source_file.contains(self.hi) {
//             // Unfortunately, macro expansion still sometimes generates Spans
//             // that malformed in this way.
//             return TAG_PARTIAL_SPAN.encode(s);
//         }
//         TAG_VALID_SPAN_FULL.encode(s);
//         StableSourceFileId::new(&source_file).encode(s);

//         let lo = self.lo - source_file.start_pos;
//         let len = self.hi - self.lo;
//         lo.encode(s);
//         len.encode(s);
//     }
// }

// impl<'tcx> Encodable<ParalegalEncoder<'tcx>> for SyntaxContext {
//     fn encode(&self, _: &mut ParalegalEncoder<'tcx>) {}
// }

// impl<'tcx, 'a> Decodable<ParalegalDecoder<'tcx, 'a>> for Span {
//     fn decode(d: &mut ParalegalDecoder<'tcx, 'a>) -> Self {
//         SpanData::decode(d).span()
//     }
// }

// impl<'tcx, 'a> Decodable<ParalegalDecoder<'tcx, 'a>> for SpanData {
//     fn decode(d: &mut ParalegalDecoder<'tcx, 'a>) -> Self {
//         let ctxt = SyntaxContext::decode(d);
//         let tag = u8::decode(d);
//         if tag == TAG_PARTIAL_SPAN {
//             return DUMMY_SP.with_ctxt(ctxt).data();
//         }
//         debug_assert_eq!(tag, TAG_VALID_SPAN_FULL);
//         let id = StableSourceFileId::decode(d);
//         let source_file = d
//             .tcx
//             .sess
//             .source_map()
//             .source_file_by_stable_id(id)
//             .unwrap();
//         let lo = BytePos::decode(d);
//         let len = BytePos::decode(d);
//         let hi = lo + len;
//         SpanData {
//             lo: source_file.start_pos + lo,
//             hi: source_file.start_pos + hi,
//             ctxt,
//             parent: None,
//         }
//     }
// }

// impl<'tcx, 'a> Decodable<ParalegalDecoder<'tcx, 'a>> for SyntaxContext {
//     fn decode(_: &mut ParalegalDecoder<'tcx, 'a>) -> Self {
//         SyntaxContext::root()
//     }
// }
