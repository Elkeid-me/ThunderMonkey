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
    Redefinition,
    VoidFuncReturn,
    NonVoidFuncReturn,
    InitIncompatibleType,
}

pub struct CompilerError {
    pub error_number: ErrorNumber,
}
