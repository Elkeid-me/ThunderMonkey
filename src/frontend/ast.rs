// Copyright (C) 2024 一梦全能 team
//
// This file is part of ThunderMonkey.
//
// ThunderMonkey is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ThunderMonkey is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ThunderMonkey.  If not, see <http://www.gnu.org/licenses/>.

use super::ty::Type;
use std::collections::{HashMap, HashSet};

pub type Handler = usize;

#[derive(Debug)]
pub struct Definition {
    pub init: Option<Init>,
    pub ty: Type,
    pub id: String,
    pub is_global: bool,
    pub is_arg: bool,
}

#[derive(Debug)]
pub struct TranslationUnit {
    pub ast: Vec<Handler>,
    pub symbol_table: HashMap<Handler, Definition>,
}

/// # 初始化器
/// - [`Init::Function`] 是二元组，前者为每个形参的重整化后名字，后者为函数体.
/// - [`Init::Expr`]，表示这个变量使用一个表达式初始化，即这是一个整型变量.
/// - [`Init::Const`]，表示这个变量使用一个整型常量初始化，即这是一个整型常量.
/// - [`Init::ConstList`] 和 [`Init::List`] 同理.
#[derive(Debug)]
pub enum Init {
    Function { block: Block, is_entry: bool },
    Expr(Expr),
    Const(i32),
    List(InitList),
    ConstList(ConstInitList),
}

#[derive(Debug, Clone)]
pub enum InitListItem {
    InitList(Box<InitList>),
    Expr(Expr),
}

pub type InitList = Vec<InitListItem>;

#[derive(Debug, Clone)]
pub enum ConstInitListItem {
    ConstInitList(Box<ConstInitList>),
    Num(i32),
}

pub type ConstInitList = Vec<ConstInitListItem>;

#[derive(Debug)]
pub enum Statement {
    Expr(Expr),
    If(Expr, Box<Block>, Box<Block>),
    While(Expr, Box<Block>),
    Return(Option<Expr>),
    Break,
    Continue,
}

pub type Block = Vec<BlockItem>;

#[derive(Debug)]
pub enum BlockItem {
    Def(Handler),
    Block(Block),
    Statement(Statement),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),

    ShL(Box<Expr>, Box<Expr>),
    ShR(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),

    Eq(Box<Expr>, Box<Expr>),
    Neq(Box<Expr>, Box<Expr>),
    Grt(Box<Expr>, Box<Expr>),
    Geq(Box<Expr>, Box<Expr>),
    Les(Box<Expr>, Box<Expr>),
    Leq(Box<Expr>, Box<Expr>),

    LogicAnd(Box<Expr>, Box<Expr>),
    LogicOr(Box<Expr>, Box<Expr>),

    LogicNot(Box<Expr>),
    Nega(Box<Expr>),
    Not(Box<Expr>),

    PostInc(Box<Expr>),
    PostDec(Box<Expr>),
    PreInc(Box<Expr>),
    PreDec(Box<Expr>),

    Assignment(Box<Expr>, Box<Expr>),
    AddAssign(Box<Expr>, Box<Expr>),
    SubAssign(Box<Expr>, Box<Expr>),
    MulAssign(Box<Expr>, Box<Expr>),
    DivAssign(Box<Expr>, Box<Expr>),
    ModAssign(Box<Expr>, Box<Expr>),
    AndAssign(Box<Expr>, Box<Expr>),
    OrAssign(Box<Expr>, Box<Expr>),
    XorAssign(Box<Expr>, Box<Expr>),
    ShLAssign(Box<Expr>, Box<Expr>),
    SaRAssign(Box<Expr>, Box<Expr>),

    Integer(i32),
    Float(f32),
    Var(Handler),
    Func(Handler, Vec<Expr>),
    Array(Handler, Vec<Expr>),
}

#[derive(Clone, Copy)]
pub enum ExprCategory {
    LValue,
    RValue,
}

#[derive(Clone, Copy)]
pub enum ExprConst {
    ConstEval,
    NonConst,
}

impl std::ops::BitAnd for ExprConst {
    type Output = ExprConst;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::ConstEval, Self::ConstEval) => Self::ConstEval,
            _ => Self::NonConst,
        }
    }
}
