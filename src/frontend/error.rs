#![allow(unused)]
use super::ty::Type;

#[derive(Debug)]
pub enum ErrorNumber {
    ParseIntError,
    ParseFloatError,
    InvalidOperands,
    NotConst,
    NotConstInt,
    NegaInt,
    NotLValue,
    BreakNotInLoop,
    ContinueNotInLoop,
    Undefined,
    Redefinition,
    IncompatibleType,
    InitListTooLong,
    ListShouldBeScalar,
}

#[derive(Debug)]
pub struct CompilerError {
    pub error_number: ErrorNumber,
    pub line_col: (usize, usize),
}

impl std::error::Error for CompilerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl std::fmt::Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
