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

use super::super::error::{CompilerError, ErrorNumber::*};
use crate::frontend::ast::{ExprCategory::*, ExprInner::*, *};
use crate::frontend::parser::{ASTBuilder, Rule};
use crate::frontend::ty::Type::{self, *};
use libc::strtof;
use pest::iterators::Pair;
use std::ptr::null_mut;

fn parse_integer(expr: Pair<Rule>) -> Result<Expr, CompilerError> {
    match expr.as_rule() {
        Rule::integer_bin => match i32::from_str_radix(&expr.as_str()[2..], 2) {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: true }),
            Err(_) => Err(CompilerError { error_number: ParseIntError, line_col: expr.line_col() }),
        },
        Rule::integer_oct => match i32::from_str_radix(&expr.as_str(), 8) {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: true }),
            Err(_) => Err(CompilerError { error_number: ParseIntError, line_col: expr.line_col() }),
        },
        Rule::integer_dec => match expr.as_str().parse() {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: true }),
            Err(_) => Err(CompilerError { error_number: ParseIntError, line_col: expr.line_col() }),
        },
        Rule::integer_hex => match i32::from_str_radix(&expr.as_str()[2..], 16) {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: true }),
            Err(_) => Err(CompilerError { error_number: ParseIntError, line_col: expr.line_col() }),
        },
        _ => unreachable!(),
    }
}

fn parse_float(expr: Pair<Rule>) -> Result<Expr, CompilerError> {
    match expr.as_rule() {
        Rule::floating_dec => match expr.as_str().parse() {
            Ok(val) => Ok(Expr { inner: Floating(val), ty: Float, category: RValue, is_const: true }),
            Err(_) => Err(CompilerError { error_number: ParseFloatError, line_col: expr.line_col() }),
        },
        Rule::floating_hex => {
            let mut floating_str = expr.as_str().to_string();
            floating_str.push('\0');
            match unsafe { strtof(floating_str.as_ptr() as *const i8, null_mut()) } {
                f32::INFINITY => Err(CompilerError { error_number: ParseFloatError, line_col: expr.line_col() }),
                val => Ok(Expr { inner: Floating(val), ty: Float, category: RValue, is_const: true }),
            }
        }
        _ => unreachable!(),
    }
}

#[macro_export]
macro_rules! arith_op_check {
    ($l: expr, $r: expr, $op_1: tt, $op_2: path, $line_col: expr) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        let ty = match (&l_ty, &r_ty) {
            (Int, Int) => Ok(Int),
            (Float, Int) | (Int, Float) | (Float, Float) => Ok(Float),
            _ => Err(CompilerError { error_number: InvalidOperands, line_col: $line_col }),
        }?;
        let inner = match (l_inner, r_inner) {
            (Integer(l), Integer(r)) => Integer(l $op_1 r),
            (Floating(l), Integer(r)) => Floating(l $op_1 (r as f32)),
            (Integer(l), Floating(r)) => Floating((l as f32) $op_1 r),
            (Floating(l), Floating(r)) => Floating(l $op_1 r),
            (l_inner, r_inner) => $op_2(
                Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
                Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
            ),
        };
        let is_const = l_is_const & r_is_const;
        Ok(Expr { inner, ty , category: RValue, is_const})
    }};
}

#[macro_export]
macro_rules! logic_op_check {
    ($l: expr, $r: expr, $op_1: tt, $op_2: path, $line_col: expr) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!((&l_ty, &r_ty), (Int, Int) | (Float, Int) | (Int, Float) | (Float, Float)) {
            return Err(CompilerError { error_number: InvalidOperands, line_col: $line_col });
        }
        let inner = match (l_inner, r_inner) {
            (Integer(l), Integer(r)) => Integer((l != 0 $op_1 r != 0) as i32),
            (Floating(l), Integer(r)) => Integer((l != 0.0 $op_1 r != 0) as i32),
            (Integer(l), Floating(r)) => Integer((l != 0 $op_1 r != 0.0) as i32),
            (Floating(l), Floating(r)) => Integer((l != 0.0 $op_1 r != 0.0) as i32),
            (l_inner, r_inner) => $op_2(
                Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
                Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
            ),
        };
        let is_const = l_is_const & r_is_const;
        Ok(Expr { inner, ty: Int ,category: RValue, is_const})
    }};
}

#[macro_export]
macro_rules! int_op_check {
    ($l: expr, $r: expr, $op_1: tt, $op_2: path, $line_col: expr) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!((&l_ty, &r_ty), (Int, Int)) {
            return Err(CompilerError { error_number: InvalidOperands, line_col: $line_col });
        }
        let inner = match (l_inner, r_inner) {
            (Integer(l), Integer(r)) => Integer(l $op_1 r),
            (l_inner, r_inner) => $op_2(
                Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
                Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
            ),
        };
        let is_const = l_is_const & r_is_const;
        Ok(Expr { inner, ty: Int ,category: RValue, is_const})
    }};
}

#[macro_export]
macro_rules! rel_op_check {
    ($l: expr, $r: expr, $op_1: tt, $op_2: path, $line_col: expr) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!((&l_ty, &r_ty), (Int, Int) | (Float, Int) | (Int, Float) | (Float, Float)) {
            return Err(CompilerError { error_number: InvalidOperands, line_col: $line_col });
        }
        let inner = match (l_inner, r_inner) {
            (Integer(l), Integer(r)) => Integer((l $op_1 r) as i32),
            (Floating(l), Integer(r)) => Integer((l $op_1 (r as f32)) as i32),
            (Integer(l), Floating(r)) => Integer(((l as f32) $op_1 r) as i32),
            (Floating(l), Floating(r)) => Integer((l $op_1 r) as i32),
            (l_inner, r_inner) => $op_2(
                Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
                Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
            ),
        };
        let is_const = l_is_const & r_is_const;
        Ok(Expr { inner, ty: Int ,category: RValue, is_const})
    }};
}

#[macro_export]
macro_rules! assign_op_check {
    ($l: expr, $r: expr, $op: path, $line_col: expr) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!(l_category, LValue) {
            return Err(CompilerError { error_number: NotLValue, line_col: $line_col });
        }
        let ty = match (&l_ty, &r_ty) {
            (Int, Int) | (Int, Float) => Ok(Int),
            (Float, Int) | (Float, Float) => Ok(Float),
            _ => Err(CompilerError { error_number: InvalidOperands, line_col: $line_col }),
        }?;
        let inner = $op(
            Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
            Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
        );
        Ok(Expr { inner, ty, category: LValue, is_const: false })
    }};
}

#[macro_export]
macro_rules! int_assign_op_check {
    ($l: expr, $r: expr, $op: path, $line_col: expr) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!(l_category, LValue) {
            return Err(CompilerError { error_number: NotLValue, line_col: $line_col });
        }
        if !matches!((&l_ty, &r_ty), (Int, Int)) {
            return Err(CompilerError { error_number: InvalidOperands, line_col: $line_col });
        }
        let inner = $op(
            Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
            Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
        );
        Ok(Expr { inner, ty: Int, category: LValue, is_const: false })
    }};
}

fn parse_infix(l: Result<Expr, CompilerError>, op: Pair<Rule>, r: Result<Expr, CompilerError>) -> Result<Expr, CompilerError> {
    match op.as_rule() {
        Rule::modu => int_op_check!(l, r, %, Mod, op.line_col()),

        Rule::mul => arith_op_check!(l, r, *, Mul, op.line_col()),
        Rule::div => arith_op_check!(l, r, /, Div, op.line_col()),
        Rule::add => arith_op_check!(l, r, +, Add, op.line_col()),
        Rule::sub => arith_op_check!(l, r, -, Sub, op.line_col()),

        Rule::logic_and => logic_op_check!(l, r, ||, LogicAnd, op.line_col()),
        Rule::logic_or => logic_op_check!(l, r, ||, LogicOr, op.line_col()),

        Rule::shl => int_op_check!(l, r, <<, ShL, op.line_col()),
        Rule::sar => int_op_check!(l, r, >>, SaR, op.line_col()),
        Rule::xor => int_op_check!(l, r, ^, Xor, op.line_col()),
        Rule::and => int_op_check!(l, r, &, And, op.line_col()),
        Rule::or => int_op_check!(l, r, |, Or, op.line_col()),

        Rule::eq => rel_op_check!(l, r, ==, Eq, op.line_col()),
        Rule::neq => rel_op_check!(l, r, !=, Neq, op.line_col()),
        Rule::grt => rel_op_check!(l, r, >, Grt, op.line_col()),
        Rule::geq => rel_op_check!(l, r, >=, Geq, op.line_col()),
        Rule::les => rel_op_check!(l, r, <, Les, op.line_col()),
        Rule::leq => rel_op_check!(l, r, <=, Leq, op.line_col()),

        Rule::assignment => assign_op_check!(l, r, Assignment, op.line_col()),
        Rule::add_assign => assign_op_check!(l, r, AddAssign, op.line_col()),
        Rule::sub_assign => assign_op_check!(l, r, SubAssign, op.line_col()),
        Rule::mul_assign => assign_op_check!(l, r, MulAssign, op.line_col()),
        Rule::div_assign => assign_op_check!(l, r, DivAssign, op.line_col()),

        Rule::mod_assign => int_assign_op_check!(l, r, ModAssign, op.line_col()),
        Rule::and_assign => int_assign_op_check!(l, r, AndAssign, op.line_col()),
        Rule::or_assign => int_assign_op_check!(l, r, OrAssign, op.line_col()),
        Rule::xor_assign => int_assign_op_check!(l, r, XorAssign, op.line_col()),
        Rule::shl_assign => int_assign_op_check!(l, r, ShLAssign, op.line_col()),
        Rule::sar_assign => int_assign_op_check!(l, r, SaRAssign, op.line_col()),
        _ => unreachable!(),
    }
}

#[macro_export]
macro_rules! dec_inc_check {
    ($e: expr, $op: path, $result_category: expr, $line_col: expr) => {{
        let Expr { inner: expr_inner, ty: expr_ty, category, is_const } = $e?;
        if !matches!(category, LValue) {
            return Err(CompilerError { error_number: NotLValue, line_col: $line_col });
        }
        let ty = match &expr_ty {
            Int => Ok(Int),
            Float => Ok(Float),
            _ => Err(CompilerError { error_number: InvalidOperands, line_col: $line_col }),
        }?;
        let inner = $op(Box::new(Expr { inner: expr_inner, ty: expr_ty, category, is_const }));
        Ok(Expr { inner, ty, category: $result_category, is_const: false })
    }};
}

fn parse_prefix(op: Pair<Rule>, expr: Result<Expr, CompilerError>) -> Result<Expr, CompilerError> {
    match op.as_rule() {
        Rule::logic_not => {
            let Expr { inner: expr_inner, ty: expr_ty, category, is_const } = expr?;
            if !matches!(&expr_ty, Int | Float) {
                return Err(CompilerError { error_number: InvalidOperands, line_col: op.line_col() });
            }
            let inner = match expr_inner {
                Integer(i) => Integer((i == 0) as i32),
                Floating(f) => Integer((f == 0.0) as i32),
                inner => Not(Box::new(Expr { inner, ty: expr_ty, category, is_const })),
            };
            Ok(Expr { inner, ty: Int, category: RValue, is_const })
        }
        Rule::negative => {
            let Expr { inner: expr_inner, ty: expr_ty, category, is_const } = expr?;
            let ty = match &expr_ty {
                Int => Ok(Int),
                Float => Ok(Float),
                _ => Err(CompilerError { error_number: InvalidOperands, line_col: op.line_col() }),
            }?;
            let inner = match expr_inner {
                Integer(i) => Integer(-i),
                Floating(f) => Floating(-f),
                inner => Nega(Box::new(Expr { inner, ty: expr_ty, category, is_const })),
            };
            Ok(Expr { inner, ty, category: RValue, is_const })
        }
        Rule::positive => Ok(expr?),
        Rule::bit_not => {
            let Expr { inner: expr_inner, ty: expr_ty, category, is_const } = expr?;
            if !matches!(&expr_ty, Int) {
                return Err(CompilerError { error_number: InvalidOperands, line_col: op.line_col() });
            }
            let inner = match expr_inner {
                Integer(i) => Integer(!i),
                inner => Not(Box::new(Expr { inner, ty: expr_ty, category, is_const })),
            };
            Ok(Expr { inner, ty: Int, category: RValue, is_const })
        }
        Rule::pre_inc => dec_inc_check!(expr, PreInc, RValue, op.line_col()),
        Rule::pre_dec => dec_inc_check!(expr, PreDec, LValue, op.line_col()),
        _ => unreachable!(),
    }
}

fn parse_postfix(expr: Result<Expr, CompilerError>, op: Pair<Rule>) -> Result<Expr, CompilerError> {
    match op.as_rule() {
        Rule::post_inc => dec_inc_check!(expr, PostInc, RValue, op.line_col()),
        Rule::post_dec => dec_inc_check!(expr, PostDec, RValue, op.line_col()),
        _ => unreachable!(),
    }
}

impl ASTBuilder {
    pub fn parse_expr(&self, expr: Pair<Rule>) -> Result<Expr, CompilerError> {
        self.expr_parser
            .map_primary(|expr| self.parse_primary(expr))
            .map_infix(parse_infix)
            .map_prefix(parse_prefix)
            .map_postfix(parse_postfix)
            .parse(expr.into_inner())
    }

    fn parse_primary(&self, expr: Pair<Rule>) -> Result<Expr, CompilerError> {
        match expr.as_rule() {
            Rule::integer_bin | Rule::integer_oct | Rule::integer_dec | Rule::integer_hex => parse_integer(expr),
            Rule::floating_dec | Rule::floating_hex => parse_float(expr),
            Rule::identifier => match self.search(expr.as_str()) {
                Some(handler) => match self.symbol_table.get(&handler).unwrap() {
                    Definition { init: Some(Init::ConstInt(i)), .. } => {
                        Ok(Expr { inner: Integer(*i), ty: Int, category: RValue, is_const: true })
                    }
                    Definition { init: Some(Init::ConstFloat(f)), .. } => {
                        Ok(Expr { inner: Floating(*f), ty: Float, category: RValue, is_const: true })
                    }
                    Definition { init: _, ty, .. } => match ty {
                        Int | Float => Ok(Expr { inner: Var(handler), ty: ty.clone(), category: LValue, is_const: false }),
                        _ => Ok(Expr { inner: Var(handler), ty: ty.clone(), category: RValue, is_const: false }),
                    },
                },
                None => Err(CompilerError { error_number: Undefined, line_col: expr.line_col() }),
            },
            Rule::func_call => {
                let line_col = expr.line_col();
                let mut iter = expr.into_inner();
                let id = iter.next().unwrap().as_str();
                match self.search(id) {
                    Some(handler) => match self.symbol_table.get(&handler).unwrap() {
                        Definition { init: _, ty: Function(ret_ty, arg_tys), .. } => {
                            let args = iter.map(|p| self.parse_expr(p)).collect::<Result<Vec<_>, _>>()?;
                            if arg_tys.len() != args.len() {
                                Err(CompilerError { error_number: IncompatibleType(todo!(), todo!()), line_col })
                            } else {
                                for (arg, expected_ty) in args.iter().zip(arg_tys) {
                                    if !arg.ty.convertible(expected_ty) {
                                        return Err(CompilerError {
                                            error_number: IncompatibleType(arg.ty.clone(), vec![expected_ty.clone()]),
                                            line_col,
                                        });
                                    }
                                }
                                Ok(Expr {
                                    inner: Func(handler, args),
                                    ty: ret_ty.as_ref().clone(),
                                    category: RValue,
                                    is_const: false,
                                })
                            }
                        }
                        Definition { .. } => Err(CompilerError { error_number: IncompatibleType(todo!(), todo!()), line_col }),
                    },
                    None => Err(CompilerError { error_number: Undefined, line_col }),
                }
            }
            Rule::array_element => {
                let line_col = expr.line_col();
                let mut iter = expr.into_inner();
                let id = iter.next().unwrap().as_str();
                let subscripts =
                    iter.next().unwrap().into_inner().map(|p| self.parse_expr(p)).collect::<Result<Vec<_>, _>>()?;
                match self.search(id) {
                    Some(handler) => match self.symbol_table.get(&handler).unwrap() {
                        Definition { init: Some(Init::ConstList(list)), ty: Array(base, lens), .. } => {
                            self.check_pointer(subscripts, handler, base, &lens[1..])
                        }
                        Definition { init: _, ty: Pointer(base, lens), .. } => {
                            self.check_pointer(subscripts, handler, base, lens)
                        }
                        Definition { init: _, ty: Array(base, lens), .. } => {
                            self.check_pointer(subscripts, handler, base, &lens[1..])
                        }
                        Definition { init: _, ty, .. } => Err(CompilerError {
                            error_number: IncompatibleType(ty.clone(), vec![Array(Box::new(Int), Vec::new())]),
                            line_col,
                        }),
                    },
                    None => Err(CompilerError { error_number: Undefined, line_col }),
                }
            }
            Rule::expression => self.parse_expr(expr),
            _ => unreachable!(),
        }
    }

    // len 是指针长度
    fn check_pointer(&self, subscripts: Vec<Expr>, handler: usize, base: &Type, lens: &[usize]) -> Result<Expr, CompilerError> {
        for expr in subscripts.iter() {
            if !matches!(expr.ty, Int) {
                return Err(CompilerError { error_number: IncompatibleType(expr.ty.clone(), vec![Int]), line_col: (0, 0) });
            }
        }
        let subscripts_len = subscripts.len();
        match (subscripts_len - 1).cmp(&lens.len()) {
            std::cmp::Ordering::Less => Ok(Expr {
                inner: ArrayElem(handler, subscripts),
                ty: Pointer(Box::new(base.clone()), lens[subscripts_len..].to_vec()),
                category: RValue,
                is_const: false,
            }),
            std::cmp::Ordering::Equal => {
                Ok(Expr { inner: ArrayElem(handler, subscripts), ty: base.clone(), category: LValue, is_const: false })
            }
            std::cmp::Ordering::Greater => Err(CompilerError {
                error_number: IncompatibleType(base.clone(), vec![Array(Box::new(Int), Vec::new())]),
                line_col: (0, 0),
            }),
        }
    }

    // // len 是指针长度
    // fn check_pointer(&self, exprs: &[Expr], len: [usize]) -> Result<(Type, ExprCategory, ExprConst), String> {
    //     for expr in exprs {
    //         if !matches!(self.expr_type(expr)?, RefInt) {
    //             return Err(format!("{expr:?} 不是整型表达式"));
    //         }
    //     }
    //     match (exprs.len() - 1).cmp(&len.len()) {
    //         std::cmp::Ordering::Less => Ok((RefIntPointer(&len[exprs.len()..]), RValue, false)),
    //         std::cmp::Ordering::Equal => Ok((RefInt, LValue, false)),
    //         std::cmp::Ordering::Greater => Err("下标运算符不能应用于整型对象".to_string()),
    //     }
    // }

    // // 返回值：表达式的值类型、是否为可修改左值、是否为整型常量表达式
    // fn expr_check(&self, expr: &Expr) -> Result<(RefType, ExprCategory, ExprConst), String> {
    //     match expr {
    //         Mul(l, r)
    //         | Div(l, r)
    //         | Mod(l, r)
    //         | Add(l, r)
    //         | Sub(l, r)
    //         | ShL(l, r)
    //         | ShR(l, r)
    //         | Xor(l, r)
    //         | And(l, r)
    //         | Or(l, r)
    //         | Eq(l, r)
    //         | Neq(l, r)
    //         | Grt(l, r)
    //         | Geq(l, r)
    //         | Les(l, r)
    //         | Leq(l, r)
    //         | LogicAnd(l, r)
    //         | LogicOr(l, r) => match (self.expr_check(l)?, self.expr_check(r)?) {
    //             ((RefInt, _, is_l_const), (RefInt, _, is_r_const)) => {
    //                 Ok((RefInt, RValue, is_l_const & is_r_const))
    //             }
    //             _ => Err(format!("{l:?} 或 {r:?} 不是整型表达式")),
    //         },

    //         LogicNot(e) | Nega(e) | Not(e) => match self.expr_check(e)? {
    //             (RefInt, _, is_const) => Ok((RefInt, RValue, is_const)),
    //             _ => Err(format!("{e:?} 不是整型表达式")),
    //         },

    //         PostInc(e) | PostDec(e) => match self.expr_check(e)? {
    //             (RefInt, LValue, _) => Ok((RefInt, RValue, false)),
    //             _ => Err(format!("{e:?} 不是左值表达式")),
    //         },

    //         PreInc(e) | PreDec(e) => match self.expr_check(e)? {
    //             (RefInt, LValue, _) => Ok((RefInt, LValue, false)),
    //             _ => Err(format!("{e:?} 不是左值表达式")),
    //         },

    //         Assignment(l, r)
    //         | AddAssign(l, r)
    //         | SubAssign(l, r)
    //         | MulAssign(l, r)
    //         | AndAssign(l, r)
    //         | OrAssign(l, r)
    //         | XorAssign(l, r)
    //         | ShLAssign(l, r)
    //         | SaRAssign(l, r)
    //         | DivAssign(l, r)
    //         | ModAssign(l, r) => match (self.expr_check(l)?, self.expr_check(r)?) {
    //             ((RefInt, LValue, _), (RefInt, _, _)) => Ok((RefInt, LValue, false)),
    //             _ => Err(format!("{l:?} 或 {r:?} 不是整型表达式, 或 {l:?} 不是左值表达式")),
    //         },

    //         Num(_) => Ok((RefInt, RValue, true)),
    //         Var(id) => match self.search(id) {
    //             Some((Int, Some(Init::Const(_)))) => Ok((RefInt, RValue, true)), // const 变量
    //             Some((Int, _)) => Ok((RefInt, LValue, false)),                     // 普通变量
    //             Some((IntArray(_), Some(Init::ConstList(_)))) => Err("孤立的 const 数组似乎干不了什么事...".to_string()), // const 数组
    //             Some((IntArray(len), _)) => Ok((RefIntPointer(&len[1..]), RValue, false)), // 普通数组
    //             Some((IntPointer(len), _)) => Ok((RefIntPointer(len), RValue, false)),     // 普通指针
    //             _ => Err(format!("标识符 {id} 在当前作用域不存在")),
    //         },
    //         Func(id, exprs) => match self.search(id) {
    //             Some((Function(ret_type, paras_type), _)) => {
    //                 if exprs.len() != paras_type.len() {
    //                     return Err(format!("实参列表与函数 {id} 的签名不匹配"));
    //                 }
    //                 for (expect_type, expr) in paras_type.iter().zip(exprs.iter()) {
    //                     let valid = match (expect_type, self.expr_type(expr)?) {
    //                         (Int, RefInt) => true,
    //                         (IntArray(l), RefIntArray(r)) | (IntPointer(l), RefIntPointer(r)) => l == r,
    //                         (IntArray(l), RefIntPointer(r)) => &l[1..] == r,
    //                         (IntPointer(l), RefIntArray(r)) => l == &r[1..],
    //                         _ => false,
    //                     };
    //                     if !valid {
    //                         return Err(format!("{expr:?} 与类型 {expect_type} 不兼容"));
    //                     }
    //                 }
    //                 Ok((ret_type.to_ref_type(), RValue, false))
    //             }
    //             Some(_) => Err(format!("标识符 {id} 不是函数")),
    //             None => Err(format!("标识符 {id} 在当前作用域中不存在")),
    //         },
    //         Array(id, exprs) => match self.search(id) {
    //             // const 数组
    //             Some((IntArray(len), Some(Init::ConstList(_)))) => match exprs.len().cmp(&len.len()) {
    //                 std::cmp::Ordering::Less => Err(format!("常量数组 {id} 不能转为指针")),
    //                 std::cmp::Ordering::Equal => {
    //                     let mut const_eval = true;
    //                     for expr in exprs {
    //                         let (ty, _, is_const) = self.expr_check(expr)?;
    //                         if !matches!(ty, RefInt) {
    //                             return Err(format!("{expr:?} 不是整型表达式"));
    //                         }
    //                         const_eval &= matches!(is_const, true);
    //                     }
    //                     if const_eval {
    //                         Ok((RefInt, RValue, true))
    //                     } else {
    //                         Ok((RefInt, RValue, false))
    //                     }
    //                 }
    //                 std::cmp::Ordering::Greater => Err("下标运算符不能应用于整型对象".to_string()),
    //             },
    //             // 普通数组
    //             Some((IntArray(len), _)) => self.check_pointer(exprs, &len[1..]),
    //             // 普通指针
    //             Some((IntPointer(len), _)) => self.check_pointer(exprs, len),
    //             Some(_) => Err(format!("标识符 {id} 不是数组或指针")),
    //             None => Err(format!("标识符 {id} 在当前作用域中不存在")),
    //         },
    //     }
    // }

    // fn expr_type(&self, expr: &Expr) -> Result<RefType, String> {
    //     Ok(self.expr_check(expr)?.0)
    // }
}
