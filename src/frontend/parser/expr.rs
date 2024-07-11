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

// use crate::frontend::ast::{Expr::*, ExprCategory::*, ExprConst::*, *};
// use crate::frontend::parser::{ASTBuilder, Rule};
// use crate::{frontend::ty::*, risk};
// use pest::iterators::Pair;

// impl ASTBuilder {
//     fn parse_expr(&self, expr: Pair<Rule>) -> Result<Expr, String> {
//         self.expr_parser
//             .map_primary(|exp| match exp.as_rule() {
//                 Rule::expression => self.parse_expr(exp),
//                 Rule::integer_bin => Ok(Num(i32::from_str_radix(&exp.as_str()[2..], 2).unwrap())),
//                 Rule::integer_oct => Ok(Num(i32::from_str_radix(exp.as_str(), 8).unwrap())),
//                 Rule::integer_dec => Ok(Num(exp.as_str().parse().unwrap())),
//                 Rule::integer_hex => Ok(Num(i32::from_str_radix(&exp.as_str()[2..], 16).unwrap())),
//                 Rule::identifier => Ok(Var(exp.as_str().to_string())),
//                 Rule::function_call => {
//                     let mut iter = exp.into_inner();
//                     Ok(Func(iter.next().unwrap().as_str().to_string(), iter.map(|p| self.parse_expr(p)).collect::<Result<_, _>>()?))
//                 }
//                 Rule::array_element => {
//                     let mut iter = exp.into_inner();
//                     Ok(Array(
//                         iter.next().unwrap().as_str().to_string(),
//                         iter.next().unwrap().into_inner().map(|p| self.parse_expr(p)).collect::<Result<_, _>>()?,
//                     ))
//                 }
//                 _ => unreachable!(),
//             })
//             .map_infix(|l, op, r| match op.as_rule() {
//                 Rule::custom => Ok(Func(op.into_inner().as_str().to_string(), vec![l?, r?])),
//                 Rule::mul => Ok(Mul(Box::new(l?), Box::new(r?))),
//                 Rule::div => Ok(Div(Box::new(l?), Box::new(r?))),
//                 Rule::modu => Ok(Mod(Box::new(l?), Box::new(r?))),
//                 Rule::add => Ok(Add(Box::new(l?), Box::new(r?))),
//                 Rule::sub => Ok(Sub(Box::new(l?), Box::new(r?))),

//                 Rule::logic_and => Ok(LogicAnd(Box::new(l?), Box::new(r?))),
//                 Rule::logic_or => Ok(LogicOr(Box::new(l?), Box::new(r?))),

//                 Rule::shl => Ok(ShL(Box::new(l?), Box::new(r?))),
//                 Rule::sar => Ok(ShR(Box::new(l?), Box::new(r?))),
//                 Rule::xor => Ok(Xor(Box::new(l?), Box::new(r?))),
//                 Rule::and => Ok(And(Box::new(l?), Box::new(r?))),
//                 Rule::or => Ok(Or(Box::new(l?), Box::new(r?))),

//                 Rule::eq => Ok(Eq(Box::new(l?), Box::new(r?))),
//                 Rule::neq => Ok(Neq(Box::new(l?), Box::new(r?))),
//                 Rule::grt => Ok(Grt(Box::new(l?), Box::new(r?))),
//                 Rule::geq => Ok(Geq(Box::new(l?), Box::new(r?))),
//                 Rule::les => Ok(Les(Box::new(l?), Box::new(r?))),
//                 Rule::leq => Ok(Leq(Box::new(l?), Box::new(r?))),

//                 Rule::assignment => Ok(Assignment(Box::new(l?), Box::new(r?))),
//                 Rule::add_assign => Ok(AddAssign(Box::new(l?), Box::new(r?))),
//                 Rule::sub_assign => Ok(SubAssign(Box::new(l?), Box::new(r?))),
//                 Rule::mul_assign => Ok(MulAssign(Box::new(l?), Box::new(r?))),
//                 Rule::div_assign => Ok(DivAssign(Box::new(l?), Box::new(r?))),
//                 Rule::mod_assign => Ok(ModAssign(Box::new(l?), Box::new(r?))),
//                 Rule::and_assign => Ok(AndAssign(Box::new(l?), Box::new(r?))),
//                 Rule::or_assign => Ok(OrAssign(Box::new(l?), Box::new(r?))),
//                 Rule::xor_assign => Ok(XorAssign(Box::new(l?), Box::new(r?))),
//                 Rule::shl_assign => Ok(ShLAssign(Box::new(l?), Box::new(r?))),
//                 Rule::sar_assign => Ok(SaRAssign(Box::new(l?), Box::new(r?))),
//                 _ => unreachable!(),
//             })
//             .map_prefix(|op, expr| match op.as_rule() {
//                 Rule::logic_not => Ok(LogicNot(Box::new(expr?))),
//                 Rule::negative => Ok(Nega(Box::new(expr?))),
//                 Rule::positive => expr,
//                 Rule::bit_not => Ok(Not(Box::new(expr?))),
//                 Rule::pre_inc => Ok(PreInc(Box::new(expr?))),
//                 Rule::pre_dec => Ok(PreDec(Box::new(expr?))),
//                 _ => unreachable!(),
//             })
//             .map_postfix(|expr, op| match op.as_rule() {
//                 Rule::post_inc => Ok(PostInc(Box::new(expr?))),
//                 Rule::post_dec => Ok(PostDec(Box::new(expr?))),
//                 _ => unreachable!(),
//             })
//             .parse(expr.into_inner())
//     }

//     // len 是指针长度
//     fn check_pointer<'a>(&self, exprs: &[Expr], len: &'a [usize]) -> Result<(RefType<'a>, ExprCategory, ExprConst), String> {
//         for expr in exprs {
//             if !matches!(self.expr_type(expr)?, RefType::Int) {
//                 return Err(format!("{expr:?} 不是整型表达式"));
//             }
//         }
//         match (exprs.len() - 1).cmp(&len.len()) {
//             std::cmp::Ordering::Less => Ok((RefType::IntPointer(&len[exprs.len()..]), RValue, NonConst)),
//             std::cmp::Ordering::Equal => Ok((RefType::Int, LValue, NonConst)),
//             std::cmp::Ordering::Greater => Err("下标运算符不能应用于整型对象".to_string()),
//         }
//     }

//     // 返回值：表达式的值类型、是否为可修改左值、是否为整型常量表达式
//     pub fn expr_check(&self, expr: &Expr) -> Result<(RefType, ExprCategory, ExprConst), String> {
//         match expr {
//             Mul(l, r)
//             | Div(l, r)
//             | Mod(l, r)
//             | Add(l, r)
//             | Sub(l, r)
//             | ShL(l, r)
//             | ShR(l, r)
//             | Xor(l, r)
//             | And(l, r)
//             | Or(l, r)
//             | Eq(l, r)
//             | Neq(l, r)
//             | Grt(l, r)
//             | Geq(l, r)
//             | Les(l, r)
//             | Leq(l, r)
//             | LogicAnd(l, r)
//             | LogicOr(l, r) => match (self.expr_check(l)?, self.expr_check(r)?) {
//                 ((RefType::Int, _, is_l_const), (RefType::Int, _, is_r_const)) => Ok((RefType::Int, RValue, is_l_const & is_r_const)),
//                 _ => Err(format!("{l:?} 或 {r:?} 不是整型表达式")),
//             },

//             LogicNot(e) | Nega(e) | Not(e) => match self.expr_check(e)? {
//                 (RefType::Int, _, is_const) => Ok((RefType::Int, RValue, is_const)),
//                 _ => Err(format!("{e:?} 不是整型表达式")),
//             },

//             PostInc(e) | PostDec(e) => match self.expr_check(e)? {
//                 (RefType::Int, LValue, _) => Ok((RefType::Int, RValue, NonConst)),
//                 _ => Err(format!("{e:?} 不是左值表达式")),
//             },

//             PreInc(e) | PreDec(e) => match self.expr_check(e)? {
//                 (RefType::Int, LValue, _) => Ok((RefType::Int, LValue, NonConst)),
//                 _ => Err(format!("{e:?} 不是左值表达式")),
//             },

//             Assignment(l, r)
//             | AddAssign(l, r)
//             | SubAssign(l, r)
//             | MulAssign(l, r)
//             | AndAssign(l, r)
//             | OrAssign(l, r)
//             | XorAssign(l, r)
//             | ShLAssign(l, r)
//             | SaRAssign(l, r)
//             | DivAssign(l, r)
//             | ModAssign(l, r) => match (self.expr_check(l)?, self.expr_check(r)?) {
//                 ((RefType::Int, LValue, _), (RefType::Int, _, _)) => Ok((RefType::Int, LValue, NonConst)),
//                 _ => Err(format!("{l:?} 或 {r:?} 不是整型表达式, 或 {l:?} 不是左值表达式")),
//             },

//             Num(_) => Ok((RefType::Int, RValue, ConstEval)),
//             Var(id) => match self.search(id) {
//                 Some((Type::Int, Some(Init::Const(_)))) => Ok((RefType::Int, RValue, ConstEval)), // const 变量
//                 Some((Type::Int, _)) => Ok((RefType::Int, LValue, NonConst)),                     // 普通变量
//                 Some((Type::IntArray(_), Some(Init::ConstList(_)))) => Err("孤立的 const 数组似乎干不了什么事...".to_string()), // const 数组
//                 Some((Type::IntArray(len), _)) => Ok((RefType::IntPointer(&len[1..]), RValue, NonConst)), // 普通数组
//                 Some((Type::IntPointer(len), _)) => Ok((RefType::IntPointer(len), RValue, NonConst)),     // 普通指针
//                 _ => Err(format!("标识符 {id} 在当前作用域不存在")),
//             },
//             Func(id, exprs) => match self.search(id) {
//                 Some((Type::Function(ret_type, paras_type), _)) => {
//                     if exprs.len() != paras_type.len() {
//                         return Err(format!("实参列表与函数 {id} 的签名不匹配"));
//                     }
//                     for (expect_type, expr) in paras_type.iter().zip(exprs.iter()) {
//                         let valid = match (expect_type, self.expr_type(expr)?) {
//                             (Type::Int, RefType::Int) => true,
//                             (Type::IntArray(l), RefType::IntArray(r)) | (Type::IntPointer(l), RefType::IntPointer(r)) => l == r,
//                             (Type::IntArray(l), RefType::IntPointer(r)) => &l[1..] == r,
//                             (Type::IntPointer(l), RefType::IntArray(r)) => l == &r[1..],
//                             _ => false,
//                         };
//                         if !valid {
//                             return Err(format!("{expr:?} 与类型 {expect_type} 不兼容"));
//                         }
//                     }
//                     Ok((ret_type.to_ref_type(), RValue, NonConst))
//                 }
//                 Some(_) => Err(format!("标识符 {id} 不是函数")),
//                 None => Err(format!("标识符 {id} 在当前作用域中不存在")),
//             },
//             Array(id, exprs) => match self.search(id) {
//                 // const 数组
//                 Some((Type::IntArray(len), Some(Init::ConstList(_)))) => match exprs.len().cmp(&len.len()) {
//                     std::cmp::Ordering::Less => Err(format!("常量数组 {id} 不能转为指针")),
//                     std::cmp::Ordering::Equal => {
//                         let mut const_eval = true;
//                         for expr in exprs {
//                             let (ty, _, is_const) = self.expr_check(expr)?;
//                             if !matches!(ty, RefType::Int) {
//                                 return Err(format!("{expr:?} 不是整型表达式"));
//                             }
//                             const_eval &= matches!(is_const, ConstEval);
//                         }
//                         if const_eval {
//                             Ok((RefType::Int, RValue, ConstEval))
//                         } else {
//                             Ok((RefType::Int, RValue, NonConst))
//                         }
//                     }
//                     std::cmp::Ordering::Greater => Err("下标运算符不能应用于整型对象".to_string()),
//                 },
//                 // 普通数组
//                 Some((Type::IntArray(len), _)) => self.check_pointer(exprs, &len[1..]),
//                 // 普通指针
//                 Some((Type::IntPointer(len), _)) => self.check_pointer(exprs, len),
//                 Some(_) => Err(format!("标识符 {id} 不是数组或指针")),
//                 None => Err(format!("标识符 {id} 在当前作用域中不存在")),
//             },
//         }
//     }

//     pub fn expr_type(&self, expr: &Expr) -> Result<RefType, String> {
//         Ok(self.expr_check(expr)?.0)
//     }

//     fn simplify(&self, expr: Expr) -> Expr {
//         match expr {
//             Num(i) => Num(i),
//             Var(x) => match self.search(&x).unwrap() {
//                 (_, Some(Init::Const(i))) => Num(*i),
//                 (_, _) => Var(x),
//             },
//             Add(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a + b),
//                 (l, r) => Add(Box::new(l), Box::new(r)),
//             },
//             Sub(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a - b),
//                 (l, r) => Sub(Box::new(l), Box::new(r)),
//             },
//             Mul(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a * b),
//                 (l, r) => Mul(Box::new(l), Box::new(r)),
//             },
//             Div(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (_, Num(0)) => Num(0),
//                 (Num(a), Num(b)) => Num(a / b),
//                 (l, r) => Div(Box::new(l), Box::new(r)),
//             },
//             Mod(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (_, Num(0)) => Num(0),
//                 (Num(a), Num(b)) => Num(a % b),
//                 (l, r) => Mod(Box::new(l), Box::new(r)),
//             },
//             ShL(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a << b),
//                 (l, r) => ShL(Box::new(l), Box::new(r)),
//             },
//             ShR(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a >> b),
//                 (l, r) => ShR(Box::new(l), Box::new(r)),
//             },
//             Xor(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a ^ b),
//                 (l, r) => Xor(Box::new(l), Box::new(r)),
//             },
//             And(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a & b),
//                 (l, r) => And(Box::new(l), Box::new(r)),
//             },
//             Or(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num(a | b),
//                 (l, r) => Or(Box::new(l), Box::new(r)),
//             },
//             Eq(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a == b) as i32),
//                 (l, r) => Eq(Box::new(l), Box::new(r)),
//             },
//             Neq(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a != b) as i32),
//                 (l, r) => Neq(Box::new(l), Box::new(r)),
//             },
//             Grt(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a > b) as i32),
//                 (l, r) => Grt(Box::new(l), Box::new(r)),
//             },
//             Geq(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a >= b) as i32),
//                 (l, r) => Geq(Box::new(l), Box::new(r)),
//             },
//             Les(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a < b) as i32),
//                 (l, r) => Les(Box::new(l), Box::new(r)),
//             },
//             Leq(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a <= b) as i32),
//                 (l, r) => Leq(Box::new(l), Box::new(r)),
//             },
//             LogicAnd(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a != 0 && b != 0) as i32),
//                 (l, r) => LogicAnd(Box::new(l), Box::new(r)),
//             },
//             LogicOr(l, r) => match (self.simplify(*l), self.simplify(*r)) {
//                 (Num(a), Num(b)) => Num((a != 0 || b != 0) as i32),
//                 (l, r) => LogicOr(Box::new(l), Box::new(r)),
//             },
//             LogicNot(expr) => match self.simplify(*expr) {
//                 Num(a) => Num((a == 0) as i32),
//                 e => LogicNot(Box::new(e)),
//             },
//             Nega(expr) => match self.simplify(*expr) {
//                 Num(a) => Num(-a),
//                 e => Nega(Box::new(e)),
//             },
//             Not(expr) => match self.simplify(*expr) {
//                 Num(a) => Num(!a),
//                 e => Not(Box::new(e)),
//             },
//             PostInc(expr) => PostInc(Box::new(self.simplify(*expr))),
//             PostDec(expr) => PostDec(Box::new(self.simplify(*expr))),
//             PreInc(expr) => PreInc(Box::new(self.simplify(*expr))),
//             PreDec(expr) => PreDec(Box::new(self.simplify(*expr))),
//             Assignment(l, r) => Assignment(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             AddAssign(l, r) => AddAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             SubAssign(l, r) => SubAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             MulAssign(l, r) => MulAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             DivAssign(l, r) => DivAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             ModAssign(l, r) => ModAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             AndAssign(l, r) => AndAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             OrAssign(l, r) => OrAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             XorAssign(l, r) => XorAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             ShLAssign(l, r) => ShLAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             SaRAssign(l, r) => SaRAssign(Box::new(self.simplify(*l)), Box::new(self.simplify(*r))),
//             Func(id, args) => {
//                 let simplified_args = args.into_iter().map(|expr| self.simplify(expr)).collect();
//                 Func(id, simplified_args)
//             }
//             Array(id, subscripts) => {
//                 let (_, init) = self.search(&id).unwrap();
//                 let simplified_subscripts: Vec<_> = subscripts.into_iter().map(|expr| self.simplify(expr)).collect();
//                 match (simplified_subscripts.iter().all(|expr| matches!(expr, Num(_))), init) {
//                     (true, Some(Init::ConstList(l))) => {
//                         let mut r_ref = l;
//                         for expr in simplified_subscripts.iter().take(simplified_subscripts.len() - 1) {
//                             let i = expr.get_num() as usize;
//                             if i >= r_ref.len() {
//                                 return Num(0);
//                             }
//                             r_ref = risk!(&r_ref[i], ConstInitListItem::ConstInitList(l) => l);
//                         }
//                         let i = simplified_subscripts.last().unwrap().get_num() as usize;
//                         if i >= r_ref.len() {
//                             Num(0)
//                         } else {
//                             Num(risk!(r_ref[i], ConstInitListItem::Num(i) => i))
//                         }
//                     }
//                     _ => Array(id, simplified_subscripts),
//                 }
//             }
//         }
//     }

//     pub fn process_expr_impl(&self, expr: Pair<Rule>) -> Result<(Expr, RefType, ExprConst), String> {
//         let expr = self.parse_expr(expr)?;
//         let (ty, _, is_const) = self.expr_check(&expr)?;
//         let expr = self.simplify(expr);
//         Ok((expr, ty, is_const))
//     }

//     pub fn process_expr(&self, expr: Pair<Rule>) -> Result<Expr, String> {
//         let (expr, _, _) = self.process_expr_impl(expr)?;
//         Ok(expr)
//     }
// }
