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

use crate::error::{CompilerError, ErrorNumber::*};
use crate::frontend::ast::{ExprCategory::*, ExprConst::*, ExprInner::*, *};
use crate::frontend::parser::{ASTBuilder, Rule};
use crate::{frontend::ty::Type::*, risk};
use libc::strtof;
use pest::{iterators::Pair, Parser};
use std::ptr::null_mut;

fn parse_integer(expr: Pair<Rule>) -> Result<Expr, CompilerError> {
    match expr.as_rule() {
        Rule::integer_bin => match i32::from_str_radix(&expr.as_str()[2..], 2) {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: ConstEval }),
            Err(_) => Err(CompilerError { error_number: ParseIntError }),
        },
        Rule::integer_oct => match i32::from_str_radix(&expr.as_str()[2..], 8) {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: ConstEval }),
            Err(_) => Err(CompilerError { error_number: ParseIntError }),
        },
        Rule::integer_dec => match expr.as_str().parse() {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: ConstEval }),
            Err(_) => Err(CompilerError { error_number: ParseIntError }),
        },
        Rule::integer_hex => match i32::from_str_radix(&expr.as_str()[2..], 16) {
            Ok(val) => Ok(Expr { inner: Integer(val), ty: Int, category: RValue, is_const: ConstEval }),
            Err(_) => Err(CompilerError { error_number: ParseIntError }),
        },
        _ => unreachable!(),
    }
}

fn parse_float(expr: Pair<Rule>) -> Result<Expr, CompilerError> {
    match expr.as_rule() {
        Rule::floating_dec => match expr.as_str().parse() {
            Ok(val) => Ok(Expr { inner: Floating(val), ty: Float, category: RValue, is_const: ConstEval }),
            Err(_) => Err(CompilerError { error_number: ParseFloatError }),
        },
        Rule::floating_hex => {
            let mut floating_str = expr.as_str().to_string();
            floating_str.push('\0');
            match unsafe { strtof(floating_str.as_ptr() as *const i8, null_mut()) } {
                f32::INFINITY => Err(CompilerError { error_number: ParseFloatError }),
                val => Ok(Expr { inner: Floating(val), ty: Float, category: RValue, is_const: ConstEval }),
            }
        }
        _ => unreachable!(),
    }
}

#[macro_export]
macro_rules! arith_op_check {
    ($l: expr, $r: expr, $op_1: tt, $op_2: path) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        let ty = match (&l_ty, &r_ty) {
            (Int, Int) => Ok(Int),
            (Float, Int) | (Int, Float) | (Float, Float) => Ok(Float),
            _ => Err(CompilerError { error_number: InvalidOperands }),
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
    ($l: expr, $r: expr, $op_1: tt, $op_2: path) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!((&l_ty, &r_ty), (Int, Int) | (Float, Int) | (Int, Float) | (Float, Float)) {
            return Err(CompilerError { error_number: InvalidOperands });
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
    ($l: expr, $r: expr, $op_1: tt, $op_2: path) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!((&l_ty, &r_ty), (Int, Int)) {
            return Err(CompilerError { error_number: InvalidOperands });
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
    ($l: expr, $r: expr, $op_1: tt, $op_2: path) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!((&l_ty, &r_ty), (Int, Int) | (Float, Int) | (Int, Float) | (Float, Float)) {
            return Err(CompilerError { error_number: InvalidOperands });
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
    ($l: expr, $r: expr, $op: path) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!(l_category, LValue) {
            return Err(CompilerError { error_number: NotLValue });
        }
        let ty = match (&l_ty, &r_ty) {
            (Int, Int) | (Int, Float) => Ok(Int),
            (Float, Int) | (Float, Float) => Ok(Float),
            _ => Err(CompilerError { error_number: InvalidOperands }),
        }?;
        let inner = $op(
            Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
            Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
        );
        Ok(Expr { inner, ty, category: LValue, is_const: NonConst })
    }};
}

#[macro_export]
macro_rules! int_assign_op_check {
    ($l: expr, $r: expr, $op: path) => {{
        let Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const } = $l?;
        let Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const } = $r?;
        if !matches!(l_category, LValue) {
            return Err(CompilerError { error_number: NotLValue });
        }
        if !matches!((&l_ty, &r_ty), (Int, Int)) {
            return Err(CompilerError { error_number: InvalidOperands });
        }
        let inner = $op(
            Box::new(Expr { inner: l_inner, ty: l_ty, category: l_category, is_const: l_is_const }),
            Box::new(Expr { inner: r_inner, ty: r_ty, category: r_category, is_const: r_is_const }),
        );
        Ok(Expr { inner, ty: Int, category: LValue, is_const: NonConst })
    }};
}

fn parse_infix(l: Result<Expr, CompilerError>, op: Pair<Rule>, r: Result<Expr, CompilerError>) -> Result<Expr, CompilerError> {
    match op.as_rule() {
        Rule::modu => int_op_check!(l, r, %, Mod),

        Rule::mul => arith_op_check!(l, r, *, Mul),
        Rule::div => arith_op_check!(l, r, /, Div),
        Rule::add => arith_op_check!(l, r, +, Add),
        Rule::sub => arith_op_check!(l, r, -, Sub),

        Rule::logic_and => logic_op_check!(l, r, ||, LogicAnd),
        Rule::logic_or => logic_op_check!(l, r, ||, LogicOr),

        Rule::shl => int_op_check!(l, r, <<, ShL),
        Rule::sar => int_op_check!(l, r, >>, SaR),
        Rule::xor => int_op_check!(l, r, ^, Xor),
        Rule::and => int_op_check!(l, r, &, And),
        Rule::or => int_op_check!(l, r, |, Or),

        Rule::eq => rel_op_check!(l, r, ==, Eq),
        Rule::neq => rel_op_check!(l, r, !=, Neq),
        Rule::grt => rel_op_check!(l, r, >, Grt),
        Rule::geq => rel_op_check!(l, r, >=, Geq),
        Rule::les => rel_op_check!(l, r, <, Les),
        Rule::leq => rel_op_check!(l, r, <=, Leq),

        Rule::assignment => assign_op_check!(l, r, Assignment),
        Rule::add_assign => assign_op_check!(l, r, AddAssign),
        Rule::sub_assign => assign_op_check!(l, r, SubAssign),
        Rule::mul_assign => assign_op_check!(l, r, MulAssign),
        Rule::div_assign => assign_op_check!(l, r, DivAssign),

        Rule::mod_assign => int_assign_op_check!(l, r, ModAssign),
        Rule::and_assign => int_assign_op_check!(l, r, AndAssign),
        Rule::or_assign => int_assign_op_check!(l, r, OrAssign),
        Rule::xor_assign => int_assign_op_check!(l, r, XorAssign),
        Rule::shl_assign => int_assign_op_check!(l, r, ShLAssign),
        Rule::sar_assign => int_assign_op_check!(l, r, SaRAssign),
        _ => unreachable!(),
    }
}

#[macro_export]
macro_rules! dec_inc_check {
    ($e: expr, $op: path, $result_category: expr) => {{
        let Expr { inner: expr_inner, ty: expr_ty, category, is_const } = $e?;
        if !matches!(category, LValue) {
            return Err(CompilerError { error_number: NotLValue });
        }
        let ty = match &expr_ty {
            Int => Ok(Int),
            Float => Ok(Float),
            _ => Err(CompilerError { error_number: InvalidOperands }),
        }?;
        let inner = $op(Box::new(Expr { inner: expr_inner, ty: expr_ty, category, is_const }));
        Ok(Expr { inner, ty, category: $result_category, is_const: NonConst })
    }};
}

fn parse_prefix(op: Pair<Rule>, expr: Result<Expr, CompilerError>) -> Result<Expr, CompilerError> {
    match op.as_rule() {
        Rule::logic_not => {
            let Expr { inner: expr_inner, ty: expr_ty, category, is_const } = expr?;
            if !matches!(&expr_ty, Int | Float) {
                return Err(CompilerError { error_number: InvalidOperands });
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
                _ => Err(CompilerError { error_number: InvalidOperands }),
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
                return Err(CompilerError { error_number: InvalidOperands });
            }
            let inner = match expr_inner {
                Integer(i) => Integer(!i),
                inner => Not(Box::new(Expr { inner, ty: expr_ty, category, is_const })),
            };
            Ok(Expr { inner, ty: Int, category: RValue, is_const })
        }
        Rule::pre_inc => dec_inc_check!(expr, PreInc, RValue),
        Rule::pre_dec => dec_inc_check!(expr, PreDec, LValue),
        _ => unreachable!(),
    }
}

fn parse_postfix(expr: Result<Expr, CompilerError>, op: Pair<Rule>) -> Result<Expr, CompilerError> {
    match op.as_rule() {
        Rule::post_inc => dec_inc_check!(expr, PostInc, RValue),
        Rule::post_dec => dec_inc_check!(expr, PostDec, RValue),
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
            Rule::expression => self.parse_expr(expr),
            Rule::integer_bin | Rule::integer_oct | Rule::integer_dec | Rule::integer_hex => parse_integer(expr),
            Rule::floating_dec | Rule::floating_hex => parse_float(expr),
            // Rule::identifier => Ok(Var(expr.as_str().to_string())),
            // Rule::function_call => {
            //     let mut iter = expr.into_inner();
            //     Ok(Func(
            //         iter.next().unwrap().as_str().to_string(),
            //         iter.map(|p| self.parse_expr(p)).collect::<Result<_, _>>()?,
            //     ))
            // }
            // Rule::array_element => {
            //     let mut iter = expr.into_inner();
            //     Ok(Array(
            //         iter.next().unwrap().as_str().to_string(),
            //         iter.next()
            //             .unwrap()
            //             .into_inner()
            //             .map(|p| self.parse_expr(p))
            //             .collect::<Result<_, _>>()?,
            //     ))
            // }
            _ => unreachable!(),
        }
    }

    // // len 是指针长度
    // fn check_pointer<'a>(&self, exprs: &[Expr], len: &'a [usize]) -> Result<(RefType<'a>, ExprCategory, ExprConst), String> {
    //     for expr in exprs {
    //         if !matches!(self.expr_type(expr)?, RefInt) {
    //             return Err(format!("{expr:?} 不是整型表达式"));
    //         }
    //     }
    //     match (exprs.len() - 1).cmp(&len.len()) {
    //         std::cmp::Ordering::Less => Ok((RefIntPointer(&len[exprs.len()..]), RValue, NonConst)),
    //         std::cmp::Ordering::Equal => Ok((RefInt, LValue, NonConst)),
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
    //             (RefInt, LValue, _) => Ok((RefInt, RValue, NonConst)),
    //             _ => Err(format!("{e:?} 不是左值表达式")),
    //         },

    //         PreInc(e) | PreDec(e) => match self.expr_check(e)? {
    //             (RefInt, LValue, _) => Ok((RefInt, LValue, NonConst)),
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
    //             ((RefInt, LValue, _), (RefInt, _, _)) => Ok((RefInt, LValue, NonConst)),
    //             _ => Err(format!("{l:?} 或 {r:?} 不是整型表达式, 或 {l:?} 不是左值表达式")),
    //         },

    //         Num(_) => Ok((RefInt, RValue, ConstEval)),
    //         Var(id) => match self.search(id) {
    //             Some((Int, Some(Init::Const(_)))) => Ok((RefInt, RValue, ConstEval)), // const 变量
    //             Some((Int, _)) => Ok((RefInt, LValue, NonConst)),                     // 普通变量
    //             Some((IntArray(_), Some(Init::ConstList(_)))) => Err("孤立的 const 数组似乎干不了什么事...".to_string()), // const 数组
    //             Some((IntArray(len), _)) => Ok((RefIntPointer(&len[1..]), RValue, NonConst)), // 普通数组
    //             Some((IntPointer(len), _)) => Ok((RefIntPointer(len), RValue, NonConst)),     // 普通指针
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
    //                 Ok((ret_type.to_ref_type(), RValue, NonConst))
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
    //                         const_eval &= matches!(is_const, ConstEval);
    //                     }
    //                     if const_eval {
    //                         Ok((RefInt, RValue, ConstEval))
    //                     } else {
    //                         Ok((RefInt, RValue, NonConst))
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
