use std::hash::Hash;

use flowistry_pdg::Constant;
use internment::Intern;

use rustc_middle::{
    mir::{self, Place},
    ty::{self},
};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum PlaceOrConst<'tcx> {
    Place(Place<'tcx>),
    Const(Constant),
}

impl<'tcx> From<Place<'tcx>> for PlaceOrConst<'tcx> {
    fn from(value: Place<'tcx>) -> Self {
        Self::Place(value)
    }
}

impl From<Constant> for PlaceOrConst<'_> {
    fn from(value: Constant) -> Self {
        Self::Const(value)
    }
}

impl<'tcx, T: Copy + Into<PlaceOrConst<'tcx>>> From<&'_ T> for PlaceOrConst<'tcx> {
    fn from(value: &'_ T) -> Self {
        (*value).into()
    }
}

impl<'tcx> PlaceOrConst<'tcx> {
    pub fn try_from_operand(
        tcx: ty::TyCtxt<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty_env: ty::TypingEnv<'tcx>,
        span: rustc_span::Span,
    ) -> Result<Self, ConstConversionError<'tcx>> {
        Ok(match operand {
            mir::Operand::Copy(place) => Self::Place(*place),
            mir::Operand::Move(place) => Self::Place(*place),
            mir::Operand::Constant(constant) => {
                Self::Const(constant_from_const(tcx, &constant.const_, ty_env, span)?)
            }
        })
    }

    /// Same as try_from_operand, but ignores certain constants that aren't
    /// convertible and reports errors for others directly as rustc errors.
    ///
    /// The span is for reporting error messages
    ///
    /// Returns None if the constant should be ignored.
    pub fn from_operand_default_policy(
        tcx: ty::TyCtxt<'tcx>,
        operand: &mir::Operand<'tcx>,
        ty_env: ty::TypingEnv<'tcx>,
        span: rustc_span::Span,
        strict: bool,
    ) -> Option<Self> {
        Self::try_from_operand(tcx, operand, ty_env, span)
            .map_err(|e| e.handle_default_policy(tcx, span, strict))
            .ok()
    }

    pub fn place(&self) -> Option<&Place<'tcx>> {
        match self {
            Self::Place(place) => Some(place),
            _ => None,
        }
    }

    pub fn const_(&self) -> Option<&Constant> {
        match self {
            Self::Const(constant) => Some(constant),
            _ => None,
        }
    }

    pub fn try_from_const(
        tcx: ty::TyCtxt<'tcx>,
        c: &mir::Const<'tcx>,
        ty_env: ty::TypingEnv<'tcx>,
        span: rustc_span::Span,
    ) -> Result<Self, ConstConversionError<'tcx>> {
        constant_from_const(tcx, c, ty_env, span).map(Self::Const)
    }

    pub fn map_place(self, f: impl FnOnce(Place<'tcx>) -> Place<'tcx>) -> Self {
        match self {
            Self::Place(place) => Self::Place(f(place)),
            Self::Const(constant) => Self::Const(constant),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConstConversionError<'tcx> {
    UnsupportedConstType(mir::Const<'tcx>),
    Integer128NotSupported { signed: bool },
    EvalFailed(mir::Const<'tcx>),
}

impl<'tcx> ConstConversionError<'tcx> {
    fn handle_default_policy(&self, tcx: ty::TyCtxt<'tcx>, span: rustc_span::Span, strict: bool) {
        let emit = |msg| {
            if strict {
                tcx.dcx().span_err(span, msg);
            } else {
                //tcx.dcx().span_warn(span, msg);
            }
        };
        if let ConstConversionError::UnsupportedConstType(c) = self {
            match c {
                mir::Const::Unevaluated(c, _) => {
                    emit(format!("Unevaluated constants are not supported {c:?}"));
                    return;
                }
                mir::Const::Val(v, t) => {
                    if let (_, ty::Ref(..) | ty::RawPtr(..)) = (v, t.kind()) {
                        return emit(format!("references and pointers are not supported: {t:?}"));
                    }
                }
                _ => (),
            }
        }
        tcx.dcx().span_err(span, format!("{self}"));
    }
}

impl std::fmt::Display for ConstConversionError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstConversionError::UnsupportedConstType(c) => {
                write!(f, "Unsupported constant type: {:?}", c)
            }
            ConstConversionError::Integer128NotSupported { signed } => {
                write!(f, "{}128 is not supported", if *signed { "i" } else { "u" })
            }
            ConstConversionError::EvalFailed(c) => {
                write!(f, "Evaluation failed for constant: {:?}", c)
            }
        }
    }
}

pub fn constant_from_const<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    c: &mir::Const<'tcx>,
    ty_env: ty::TypingEnv<'tcx>,
    span: rustc_span::Span,
) -> Result<Constant, ConstConversionError<'tcx>> {
    if matches!(c, mir::Const::Unevaluated(..)) {
        return Err(ConstConversionError::UnsupportedConstType(*c));
    };
    if let Ok(const_val) = c.eval(tcx, ty_env, span) {
        constant_from_const_value(tcx, c.ty(), &const_val)
    } else {
        Err(ConstConversionError::EvalFailed(*c))
    }
}

fn constant_from_const_value<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ct: &mir::ConstValue<'tcx>,
) -> Result<Constant, ConstConversionError<'tcx>> {
    // largely from rustc_middle/mir/pretty.rs:1952-1962
    match (ct, ty.kind()) {
        (_, ty::Ref(_, inner_ty, _)) if matches!(inner_ty.kind(), ty::Str) => {
            if let Some(data) = ct.try_get_slice_bytes_for_diagnostics(tcx) {
                return Ok(Constant::String(Intern::from_ref(
                    String::from_utf8_lossy(data).as_ref(),
                )));
            }
        }
        (mir::ConstValue::Scalar(mir::interpret::Scalar::Int(int)), tyk) => match tyk {
            ty::Bool => return Ok(Constant::Bool(int.try_to_bool().unwrap())),
            // Skipping floats for now.
            // ty::Float(fty) => Self::Float(match fty {
            //     ty::FloatTy::F16 => int.to_f16() as f64,
            //     ty::FloatTy::F32 => int.to_f32() as f64,
            //     ty::FloatTy::F64 => int.to_f64() as f64,
            // }),
            ty::Int(ity) => {
                return Ok(Constant::Int(match ity {
                    ty::IntTy::I8 => int.to_u8() as i64,
                    ty::IntTy::I16 => int.to_u16() as i64,
                    ty::IntTy::I32 => int.to_u32() as i64,
                    ty::IntTy::I64 => int.to_u64() as i64,
                    ty::IntTy::Isize => int.to_target_isize(tcx),
                    ty::IntTy::I128 => {
                        return Err(ConstConversionError::Integer128NotSupported { signed: true })
                    }
                }))
            }
            ty::Uint(uty) => {
                return Ok(Constant::Uint(match uty {
                    ty::UintTy::U8 => int.to_u8() as u64,
                    ty::UintTy::U16 => int.to_u16() as u64,
                    ty::UintTy::U32 => int.to_u32() as u64,
                    ty::UintTy::U64 => int.to_u64(),
                    ty::UintTy::Usize => int.to_target_usize(tcx),
                    ty::UintTy::U128 => {
                        return Err(ConstConversionError::Integer128NotSupported { signed: false })
                    }
                }))
            }
            ty::Char => {
                return Ok(Constant::Char(int.to_u32() as u8 as char));
            }
            _ => (),
        },
        (mir::ConstValue::ZeroSized, t) => return Ok(Constant::Zst(Intern::new(format!("{t:?}")))),
        _ => (),
    }
    Err(ConstConversionError::UnsupportedConstType(mir::Const::Val(
        *ct, ty,
    )))
}
