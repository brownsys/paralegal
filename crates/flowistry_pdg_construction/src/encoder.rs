//! Readers and writers for the intermediate artifacts we store per crate.
//!
//! Most of this code is adapted/copied from `EncodeContext` and `DecodeContext`
//! in `rustc_metadata`.
//!
//! We use a lot of `min_specialization` here to change how `DefId`s, `Span`s
//! and such are encoded since their default implementations are panics.
//!
//! Specifically for `CrateNum` (e.g. `DefId` also), we use stable crate hashes.
//! These appear to work fine, however I am not sure they are guaranteed to be
//! stable across different crates. Rustc itself uses an explicit remapping
//! replying on `CrateMetadataRef`, which we can construct but not use (relevant
//! functions are hidden).
//!
//! Note that we encode `AllocId`s simply as themselves. This is possibly
//! incorrect but we're not really relying on this information at the moment so
//! we are not investing in it.
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;
use std::sync::Arc;
use std::{num::NonZeroU64, path::PathBuf};

use rustc_const_eval::interpret::AllocId;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_serialize::{
    opaque::{FileEncoder, MemDecoder},
    Decodable, Decoder, Encodable, Encoder,
};
use rustc_span::{
    AttrId, BytePos, ExpnId, FileName, RealFileName, SourceFile, Span, SpanData, SpanDecoder,
    SpanEncoder, Symbol, SyntaxContext, DUMMY_SP,
};
use rustc_type_ir::{PredicateKind, TyDecoder, TyEncoder};

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.file_encoder.$name(value)
        })*
    }
}

/// A structure that implements `TyEncoder` for us.
pub struct ParalegalEncoder<'tcx> {
    tcx: TyCtxt<'tcx>,
    file_encoder: FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    filepath_shorthands: FxHashMap<FileName, usize>,
}

impl<'tcx> ParalegalEncoder<'tcx> {
    /// Create a new encoder that will write to the provided file.
    pub fn new(path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            file_encoder: FileEncoder::new(path).unwrap(),
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
            filepath_shorthands: Default::default(),
        }
    }

    pub fn finish(mut self) {
        self.file_encoder.finish().unwrap();
    }
}

/// Convenience function that encodes some value to a file.
pub fn encode_to_file<'tcx, V: Encodable<ParalegalEncoder<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    path: impl AsRef<Path>,
    v: &V,
) {
    let mut encoder = ParalegalEncoder::new(path, tcx);
    v.encode(&mut encoder);
    encoder.finish();
}

/// Whatever can't survive the crossing we need to live without.
const CLEAR_CROSS_CRATE: bool = true;

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

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<PredicateKind<Self::I>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &<Self::I as rustc_type_ir::Interner>::AllocId) {
        u64::from(alloc_id.0).encode(self)
    }
}

/// Something that implements `TyDecoder`.
pub struct ParalegalDecoder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    mem_decoder: MemDecoder<'a>,
    shorthand_map: FxHashMap<usize, Ty<'tcx>>,
    file_shorthands: FxHashMap<usize, Arc<SourceFile>>,
}

impl<'tcx, 'a> ParalegalDecoder<'tcx, 'a> {
    /// Decode what is in this buffer.
    pub fn new(tcx: TyCtxt<'tcx>, buf: &'a [u8]) -> Self {
        Self {
            tcx,
            mem_decoder: MemDecoder::new(buf, 0).unwrap(),
            shorthand_map: Default::default(),
            file_shorthands: Default::default(),
        }
    }
}

/// Convenience function that decodes a value from a file.
pub fn decode_from_file<'tcx, V: for<'a> Decodable<ParalegalDecoder<'tcx, 'a>>>(
    tcx: TyCtxt<'tcx>,
    path: impl AsRef<Path>,
) -> io::Result<V> {
    let mut file = File::open(path)?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;
    let mut decoder = ParalegalDecoder::new(tcx, buf.as_slice());
    Ok(V::decode(&mut decoder))
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
        debug_assert!(pos < self.mem_decoder.len());

        let new_opaque = self.mem_decoder.split_at(pos);
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

impl<'tcx, 'a> SpanDecoder for ParalegalDecoder<'tcx, 'a> {
    fn decode_crate_num(&mut self) -> CrateNum {
        self.tcx
            .stable_crate_id_to_crate_num(Decodable::decode(self))
    }
    fn decode_def_index(&mut self) -> DefIndex {
        DefIndex::from_u32(u32::decode(self))
    }
    fn decode_span(&mut self) -> Span {
        SpanData::decode(self).span()
    }

    fn decode_syntax_context(&mut self) -> SyntaxContext {
        SyntaxContext::root()
    }

    fn decode_def_id(&mut self) -> DefId {
        DefId {
            krate: self.decode_crate_num(),
            index: self.decode_def_index(),
        }
    }

    fn decode_expn_id(&mut self) -> ExpnId {
        unimplemented!()
    }

    fn decode_symbol(&mut self) -> Symbol {
        Symbol::intern(&String::decode(self))
    }

    fn decode_attr_id(&mut self) -> AttrId {
        unimplemented!()
    }
}

impl<'tcx> SpanEncoder for ParalegalEncoder<'tcx> {
    fn encode_def_index(&mut self, def_index: DefIndex) {
        def_index.as_u32().encode(self)
    }
    fn encode_span(&mut self, span: Span) {
        span.data().encode(self)
    }
    fn encode_syntax_context(&mut self, _syntax_context: SyntaxContext) {}

    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        self.tcx.stable_crate_id(crate_num).encode(self)
    }
    fn encode_def_id(&mut self, def_id: DefId) {
        self.encode_crate_num(def_id.krate);
        self.encode_def_index(def_id.index);
    }
    fn encode_expn_id(&mut self, _expn_id: ExpnId) {
        unimplemented!()
    }
    fn encode_symbol(&mut self, symbol: Symbol) {
        symbol.as_str().encode(self)
    }
}

const TAG_PARTIAL_SPAN: u8 = 0;
const TAG_VALID_SPAN_FULL: u8 = 1;

/// Some of this code is lifted from `EncodeContext`.
///
/// However we directly encode file names because that's easier.
impl<'tcx> Encodable<ParalegalEncoder<'tcx>> for SpanData {
    fn encode(&self, s: &mut ParalegalEncoder<'tcx>) {
        if self.is_dummy() {
            return TAG_PARTIAL_SPAN.encode(s);
        }
        let source_map = s.tcx.sess.source_map();
        let source_file = source_map.lookup_source_file(self.lo);
        if !source_file.contains(self.hi) {
            // Unfortunately, macro expansion still sometimes generates Spans
            // that malformed in this way.
            return TAG_PARTIAL_SPAN.encode(s);
        }
        TAG_VALID_SPAN_FULL.encode(s);
        source_file.cnum.encode(s);
        let mut name = source_file.name.clone();
        if let FileName::Real(RealFileName::Remapped { local_path, .. }) = &mut name {
            local_path.take();
        }
        s.encode_file_name(&name);

        let lo = self.lo - source_file.start_pos;
        let len = self.hi - self.lo;
        lo.encode(s);
        len.encode(s);
    }
}

impl<'tcx> ParalegalEncoder<'tcx> {
    fn encode_file_name(&mut self, n: &FileName) {
        if let Some(&idx) = self.filepath_shorthands.get(n) {
            TAG_ENCODE_REMOTE.encode(self);
            idx.encode(self);
        } else {
            TAG_ENCODE_LOCAL.encode(self);
            self.filepath_shorthands
                .insert(n.clone(), self.file_encoder.position());
            n.encode(self);
        }
    }
}

impl<'tcx, 'a> ParalegalDecoder<'tcx, 'a> {
    fn decode_file_name(&mut self, crate_num: CrateNum) -> Arc<SourceFile> {
        let tag = u8::decode(self);
        let pos = if tag == TAG_ENCODE_REMOTE {
            let index = usize::decode(self);
            if let Some(cached) = self.file_shorthands.get(&index) {
                return cached.clone();
            }
            Some(index)
        } else if tag == TAG_ENCODE_LOCAL {
            None
        } else {
            panic!("Unexpected tag value {tag}");
        };
        let (index, file) = if let Some(idx) = pos {
            (
                idx,
                self.with_position(idx, |slf| slf.decode_filename_local(crate_num)),
            )
        } else {
            (self.position(), self.decode_filename_local(crate_num))
        };

        self.file_shorthands.insert(index, file.clone());
        file
    }

    fn decode_filename_local(&mut self, crate_num: CrateNum) -> Arc<SourceFile> {
        let file_name = FileName::decode(self);
        let source_map = self.tcx.sess.source_map();
        let matching_source_files = source_map
            .files()
            .iter()
            .filter(|f| {
                f.cnum == crate_num && (file_name == f.name || matches!((&file_name, &f.name), (FileName::Real(r), FileName::Real(other)) if {
                    let before = path_in_real_path(r);
                    let after = path_in_real_path(other);
                    after.ends_with(before)
                }))
            })
            .cloned()
            .collect::<Box<[_]>>();
        match matching_source_files.as_ref() {
            [sf] => sf.clone(),
            [] => match &file_name {
                FileName::Real(RealFileName::LocalPath(local)) if source_map.file_exists(local) => {
                    source_map.load_file(local).unwrap()
                }
                _ => panic!("Could not load file {}", file_name.prefer_local()),
            },
            other => {
                let names = other.iter().map(|f| &f.name).collect::<Vec<_>>();
                panic!("Too many matching file names for {file_name:?}: {names:?}")
            }
        }
    }
}

const TAG_ENCODE_REMOTE: u8 = 0;
const TAG_ENCODE_LOCAL: u8 = 1;

/// Which path in a [`RealFileName`] do we care about?
fn path_in_real_path(r: &RealFileName) -> &PathBuf {
    match r {
        RealFileName::LocalPath(p) => p,
        RealFileName::Remapped { virtual_name, .. } => virtual_name,
    }
}

/// Partially uses code similar to `DecodeContext`. But we fully encode file
/// names. We then map them back by searching the currently loaded files. If the
/// file we care about is not found there, we try and load its source.
impl<'tcx, 'a> Decodable<ParalegalDecoder<'tcx, 'a>> for SpanData {
    fn decode(d: &mut ParalegalDecoder<'tcx, 'a>) -> Self {
        let ctxt = SyntaxContext::decode(d);
        let tag = u8::decode(d);
        if tag == TAG_PARTIAL_SPAN {
            return DUMMY_SP.with_ctxt(ctxt).data();
        }
        debug_assert_eq!(tag, TAG_VALID_SPAN_FULL);
        let crate_num = CrateNum::decode(d);
        let source_file = d.decode_file_name(crate_num);
        let lo = BytePos::decode(d);
        let len = BytePos::decode(d);
        let hi = lo + len;
        let lo = source_file.start_pos + lo;
        let hi = source_file.start_pos + hi;
        assert!(source_file.contains(lo));
        assert!(source_file.contains(hi));
        SpanData {
            lo,
            hi,
            ctxt,
            parent: None,
        }
    }
}
