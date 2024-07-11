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

mod expr;

use super::ast::{Expr::*, ExprConst::*, *};
use super::ty::Type::{self, *};
use crate::risk;
use pest::pratt_parser::Assoc::{Left, Right};
use pest::pratt_parser::{Op, PrattParser};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::collections::HashMap;
use std::{iter::repeat, mem::take};

#[derive(Parser)]
#[grammar = "frontend/sysy.pest"]
struct SysYParser;

// struct Counter {
//     value: usize,
// }

// impl Counter {
//     fn get(&mut self) -> usize {
//         self.value += 1;
//         self.value
//     }
// }
// pub struct ASTBuilder {
//     expr_parser: PrattParser<Rule>,
//     table: Vec<HashMap<String, Handler>>,
//     symbol_table: HashMap<Handler, Definition>,
//     counter: Counter,
//     depth: usize,
// }

// trait InitListTrait {
//     fn new_list(l: Vec<Self>) -> Self
//     where
//         Self: Sized;
//     fn new_item(ast_builder: &ASTBuilder, expr: Pair<Rule>) -> Result<Self, String>
//     where
//         Self: Sized;
//     fn get_last(v: &mut Vec<Self>) -> &mut Vec<Self>
//     where
//         Self: Sized;
//     fn add_empty_list(len: &[usize], init_list: Vec<Self>) -> Vec<Self>
//     where
//         Self: Sized;
//     fn generate_empty_list(len: &[usize]) -> Self;
// }

// impl InitListTrait for ConstInitListItem {
//     fn new_list(l: Vec<Self>) -> Self {
//         Self::ConstInitList(Box::new(l))
//     }
//     fn new_item(ast_builder: &ASTBuilder, expr: Pair<Rule>) -> Result<Self, String> {
//         match ast_builder.process_expr(expr)? {
//             Num(i) => Ok(Self::Num(i)),
//             expr => Err(format!("{expr:?} 不是整型常量表达式")),
//         }
//     }
//     fn get_last(v: &mut Vec<Self>) -> &mut Vec<Self> {
//         risk!(v.last_mut().unwrap(), Self::ConstInitList(l) => l.as_mut())
//     }
//     fn generate_empty_list(len: &[usize]) -> Self {
//         match len.len() {
//             0 => Self::Num(0),
//             _ => Self::new_list(
//                 repeat(Self::generate_empty_list(&len[1..])).take(len[0]).collect(),
//             ),
//         }
//     }
//     fn add_empty_list(len: &[usize], init_list: Vec<Self>) -> Vec<Self> {
//         let empty_list = Self::generate_empty_list(&len[1..]);
//         let empty_list_n = len[0] - init_list.len();
//         init_list
//             .into_iter()
//             .map(|item| match item {
//                 Self::ConstInitList(list) => {
//                     Self::ConstInitList(Box::new(Self::add_empty_list(&len[1..], *list)))
//                 }
//                 i => i,
//             })
//             .chain(repeat(empty_list).take(empty_list_n))
//             .collect()
//     }
// }

// impl InitListTrait for InitListItem {
//     fn new_list(l: Vec<Self>) -> Self {
//         Self::InitList(Box::new(l))
//     }
//     fn new_item(ast_builder: &ASTBuilder, expr: Pair<Rule>) -> Result<Self, String> {
//         match ast_builder.process_expr_impl(expr)? {
//             (expr, RefType::Int, _) => Ok(Self::Expr(expr)),
//             (expr, _, _) => Err(format!("{expr:?} 不是整型表达式")),
//         }
//     }
//     fn get_last(v: &mut Vec<Self>) -> &mut Vec<Self> {
//         risk!(v.last_mut().unwrap(), Self::InitList(l) => l.as_mut())
//     }
//     fn generate_empty_list(len: &[usize]) -> Self {
//         match len.len() {
//             0 => Self::Expr(Num(0)),
//             _ => Self::new_list(
//                 repeat(Self::generate_empty_list(&len[1..])).take(len[0]).collect(),
//             ),
//         }
//     }
//     fn add_empty_list(len: &[usize], init_list: Vec<Self>) -> Vec<Self> {
//         let empty_list = Self::generate_empty_list(&len[1..]);
//         let empty_list_n = len[0] - init_list.len();
//         init_list
//             .into_iter()
//             .map(|item| match item {
//                 Self::InitList(list) => {
//                     Self::InitList(Box::new(Self::add_empty_list(&len[1..], *list)))
//                 }
//                 expr => expr,
//             })
//             .chain(repeat(empty_list).take(empty_list_n))
//             .collect()
//     }
// }
// type Signature = (String, Type, Vec<Type>, Vec<Option<String>>);
// impl ASTBuilder {
//     fn new() -> Self {
//         let expr_parser = PrattParser::new()
//             .op(Op::infix(Rule::assignment, Right)
//                 | Op::infix(Rule::add_assign, Right)
//                 | Op::infix(Rule::sub_assign, Right)
//                 | Op::infix(Rule::mul_assign, Right)
//                 | Op::infix(Rule::div_assign, Right)
//                 | Op::infix(Rule::mod_assign, Right)
//                 | Op::infix(Rule::and_assign, Right)
//                 | Op::infix(Rule::or_assign, Right)
//                 | Op::infix(Rule::xor_assign, Right)
//                 | Op::infix(Rule::shl_assign, Right)
//                 | Op::infix(Rule::sar_assign, Right))
//             .op(Op::infix(Rule::logic_or, Left))
//             .op(Op::infix(Rule::logic_and, Left))
//             .op(Op::infix(Rule::xor, Left))
//             .op(Op::infix(Rule::or, Left))
//             .op(Op::infix(Rule::and, Left))
//             .op(Op::infix(Rule::eq, Left) | Op::infix(Rule::neq, Left))
//             .op(Op::infix(Rule::grt, Left)
//                 | Op::infix(Rule::geq, Left)
//                 | Op::infix(Rule::les, Left)
//                 | Op::infix(Rule::leq, Left))
//             .op(Op::infix(Rule::shl, Left) | Op::infix(Rule::sar, Left))
//             .op(Op::infix(Rule::add, Left) | Op::infix(Rule::sub, Left))
//             .op(Op::infix(Rule::mul, Left)
//                 | Op::infix(Rule::div, Left)
//                 | Op::infix(Rule::modu, Left))
//             .op(Op::infix(Rule::right_pipe, Left))
//             .op(Op::infix(Rule::left_pipe, Right))
//             .op(Op::infix(Rule::custom, Left))
//             .op(Op::infix(Rule::method, Left))
//             .op(Op::prefix(Rule::logic_not)
//                 | Op::prefix(Rule::negative)
//                 | Op::prefix(Rule::positive)
//                 | Op::prefix(Rule::bit_not)
//                 | Op::prefix(Rule::pre_inc)
//                 | Op::prefix(Rule::pre_dec))
//             .op(Op::postfix(Rule::post_inc) | Op::postfix(Rule::post_dec));
//         Self {
//             expr_parser,
//             table: vec![HashMap::new()],
//             symbol_table: HashMap::new(),
//             counter: Counter { value: 0 },
//             depth: 0,
//         }
//     }

//     fn is_global_now(&self) -> bool {
//         self.depth == 0
//     }

//     fn is_arg_now(&self) -> bool {
//         self.depth == 1
//     }

//     fn search(&self, id: &str) -> Option<&Definition> {
//         for map in self.table.iter().rev() {
//             if let Some(handler) = map.get(id) {
//                 return self.symbol_table.get(handler);
//             }
//         }
//         None
//     }
//     fn insert_definition(
//         &mut self,
//         id: String,
//         ty: Type,
//         init: Option<Init>,
//     ) -> Result<Handler, String> {
//         let handler = self.counter.get();
//         if self.table.last().unwrap().contains_key(&id) {
//             let old_handler = self.table.last().unwrap().get(&id).unwrap();
//             match (self.symbol_table.get(old_handler).unwrap(), &ty) {
//                 (
//                     Definition {
//                         init: None, ty: Function(ret_type_1, arg_types_1), ..
//                     },
//                     Function(ret_type_2, arg_types_2),
//                 ) if ret_type_1 == ret_type_2 && arg_types_1 == arg_types_2 => {
//                     self.symbol_table.insert(
//                         *old_handler,
//                         Definition {
//                             id,
//                             init,
//                             ty,
//                             is_global: self.is_arg_now(),
//                             is_arg: self.is_arg_now(),
//                         },
//                     );
//                     Ok(*old_handler)
//                 }
//                 _ => Err(format!("标识符 {id} 在当前作用域中已存在")),
//             }
//         } else {
//             self.table.last_mut().unwrap().insert(id.clone(), handler);
//             self.symbol_table.insert(
//                 handler,
//                 Definition {
//                     id,
//                     init,
//                     ty,
//                     is_global: self.is_arg_now(),
//                     is_arg: self.is_arg_now(),
//                 },
//             );
//             Ok(handler)
//         }
//     }
//     fn enter_scope(&mut self) {
//         self.table.push(HashMap::new());
//     }
//     fn exit_scope(&mut self) {
//         self.table.pop();
//     }

//     fn iter_to_vec(&self, iter: Option<Pair<Rule>>) -> Result<Vec<usize>, String> {
//         match iter {
//             Some(i) => i
//                 .into_inner()
//                 .map(|expr| {
//                     let (expr, _, is_const) = self.process_expr_impl(expr)?;
//                     match is_const {
//                         ConstEval => {
//                             let i = expr.get_num();
//                             if i > 0 {
//                                 Ok(i as usize)
//                             } else {
//                                 Err(format!("{expr:?} 的值不是正整数"))
//                             }
//                         }
//                         NonConst => Err(format!("{expr:?} 不是整型常量表达式")),
//                     }
//                 })
//                 .collect::<Result<_, _>>(),
//             None => Ok(Vec::new()),
//         }
//     }

//     fn parse_init_list_impl<T>(
//         &self,
//         init_list: Pair<Rule>,
//         len_prod: &[usize],
//     ) -> Result<(Vec<T>, usize), String>
//     where
//         T: InitListTrait,
//     {
//         let mut v = Vec::new();
//         let mut sum = 0usize;
//         for ele in init_list.into_inner() {
//             match ele.as_rule() {
//                 Rule::initializer_list => {
//                     if len_prod.len() == 1 || sum % len_prod[0] != 0 {
//                         return Err(format!("{ele:?} 不能是初始化列表"));
//                     }
//                     //   对于 `int lint[1][14][51][4]`，我们计算一个列表：`L = {4, 204, 2856, 2856}`，这个数组给出了每一层的大小.
//                     //                                                      ^   ^    ^     ^
//                     //                                                      |   |    |     |
//                     //                                                      0   1    2     3
//                     //   rev_depth 给出了列表中第一个不能被 sum 整除的元素的下标.
//                     //   rev_depth == 0 -> 错误，即当前已经填充完毕的元素的个数不能被 L[0] 整除
//                     //   rev_depth == 1 -> init_list 对应最内层的列表. 譬如 int array[4][3][2]，init_list 对应 int[2].
//                     // 而此时需要寻位到 `v` 的第 2 层（以最外层为 1 层），然后 push.
//                     //   换句话说，寻位的次数是 l.len() - rev_depth.
//                     //   若 sum == 0，则 position 返回 None. unwrap 为 0.

//                     //   对于 `int lint[1][14][51][4]`，rev_depth == 3 时，意味着 init_list 对应 int[14][51][4]
//                     // 需要寻位 0 次
//                     let rev_depth = len_prod
//                         .iter()
//                         .position(|prod| sum % prod != 0)
//                         .unwrap_or(len_prod.len() - 1);
//                     let depth = len_prod.len() - rev_depth - 1;
//                     let (l, s) =
//                         self.parse_init_list_impl(ele, &len_prod[0..rev_depth])?;
//                     let v_ref = (0..depth).fold(&mut v, |state, _| {
//                         if state.is_empty() {
//                             state.push(T::new_list(Vec::new()));
//                         }
//                         T::get_last(state)
//                     });
//                     v_ref.push(T::new_list(l));
//                     sum += s;
//                 }
//                 Rule::expression => {
//                     let v_ref = len_prod.iter().rev().skip(1).fold(&mut v, |state, i| {
//                         if state.is_empty() || sum % i == 0 {
//                             state.push(T::new_list(Vec::new()));
//                         }
//                         T::get_last(state)
//                     });
//                     v_ref.push(T::new_item(self, ele)?);
//                     sum += 1;
//                 }
//                 _ => unreachable!(),
//             }
//             if sum > *len_prod.last().unwrap() {
//                 return Err("初始化列表过长".to_string());
//             }
//         }
//         Ok((v, *len_prod.last().unwrap()))
//     }
//     fn parse_init_list<T>(
//         &self,
//         init_list: Pair<Rule>,
//         lengths: &[usize],
//     ) -> Result<Vec<T>, String>
//     where
//         T: InitListTrait,
//     {
//         let len_prod: Vec<usize> = lengths
//             .iter()
//             .rev()
//             .scan(1, |l, &r| {
//                 *l *= r;
//                 Some(*l)
//             })
//             .collect();
//         Ok(T::add_empty_list(
//             lengths,
//             self.parse_init_list_impl::<T>(init_list, &len_prod)?.0,
//         ))
//     }

//     fn parse_definition(&mut self, pair: Pair<Rule>) -> Result<Handler, String> {
//         match pair.as_rule() {
//             Rule::const_variable_definition => {
//                 let mut iter = pair.into_inner();
//                 let id = iter.next().unwrap().as_str().to_string();
//                 match self.process_expr_impl(iter.next().unwrap())? {
//                     (Num(i), _, ConstEval) => {
//                         self.insert_definition(id, Int, Some(Init::Const(i)))
//                     }
//                     (expr, _, _) => Err(format!("{expr:?} 不是整型常量表达式")),
//                 }
//             }
//             Rule::variable_definition => {
//                 let mut iter = pair.into_inner();
//                 let id = iter.next().unwrap().as_str().to_string();
//                 match iter.next().map(|expr| self.process_expr_impl(expr)) {
//                     Some(Ok((expr, RefType::Int, _))) => {
//                         self.insert_definition(id, Int, Some(Init::Expr(expr)))
//                     }
//                     Some(Ok((expr, _, _))) => Err(format!("{expr:?} 不是整型表达式")),
//                     Some(Err(s)) => Err(s),
//                     None => self.insert_definition(id, Int, None),
//                 }
//             }
//             Rule::const_array_definition => {
//                 let mut iter = pair.into_inner();
//                 let id = iter.next().unwrap().as_str().to_string();
//                 let len = self.iter_to_vec(iter.next())?;
//                 let init_list = self.parse_init_list(iter.next().unwrap(), &len)?;
//                 self.insert_definition(
//                     id,
//                     IntArray(len),
//                     Some(Init::ConstList(init_list)),
//                 )
//             }
//             Rule::array_definition => {
//                 let mut iter = pair.into_inner();
//                 let id = iter.next().unwrap().as_str().to_string();
//                 let len = self.iter_to_vec(iter.next())?;
//                 match iter.next() {
//                     Some(i) => {
//                         let init_list = self.parse_init_list(i, &len)?;
//                         self.insert_definition(
//                             id,
//                             IntArray(len),
//                             Some(Init::List(init_list)),
//                         )
//                     }
//                     None => self.insert_definition(id, IntArray(len), None),
//                 }
//             }
//             _ => unreachable!(),
//         }
//     }

//     fn parse_if_while_helper(
//         &mut self,
//         pair: Pair<Rule>,
//         in_while: bool,
//         ret_type: &Type,
//     ) -> Result<Block, String> {
//         match pair.as_rule() {
//             Rule::block => self.parse_block(pair, in_while, ret_type),
//             Rule::expression
//             | Rule::return_statement
//             | Rule::if_statement
//             | Rule::while_statement
//             | Rule::break_keyword
//             | Rule::continue_keyword => Ok(vec![BlockItem::Statement(
//                 self.parse_statement(pair, in_while, ret_type)?,
//             )]),
//             Rule::empty_statement => Ok(Vec::new()),
//             Rule::definitions_in_if_or_while_non_block => pair
//                 .into_inner()
//                 .skip(1)
//                 .map(|pair| Ok(BlockItem::Def(self.parse_definition(pair)?)))
//                 .collect::<Result<_, _>>(),
//             _ => unreachable!(),
//         }
//     }

//     fn parse_if(
//         &mut self,
//         pair: Pair<Rule>,
//         in_while: bool,
//         ret_type: &Type,
//     ) -> Result<Statement, String> {
//         let mut iter = pair.into_inner();
//         Ok(Statement::If(
//             self.process_expr(iter.next().unwrap())?,
//             Box::new(self.parse_if_while_helper(
//                 iter.next().unwrap(),
//                 in_while,
//                 ret_type,
//             )?),
//             match iter.next() {
//                 Some(block) => {
//                     Box::new(self.parse_if_while_helper(block, in_while, ret_type)?)
//                 }
//                 None => Box::default(),
//             },
//         ))
//     }

//     fn parse_while(
//         &mut self,
//         pair: Pair<Rule>,
//         ret_type: &Type,
//     ) -> Result<Statement, String> {
//         let mut iter = pair.into_inner();
//         Ok(Statement::While(
//             self.process_expr(iter.next().unwrap())?,
//             Box::new(self.parse_if_while_helper(iter.next().unwrap(), true, ret_type)?),
//         ))
//     }

//     fn parse_statement(
//         &mut self,
//         iter: Pair<Rule>,
//         in_while: bool,
//         ret_type: &Type,
//     ) -> Result<Statement, String> {
//         match iter.as_rule() {
//             Rule::expression => Ok(Statement::Expr(self.process_expr(iter)?)),
//             Rule::return_statement => match (
//                 iter.into_inner().nth(1).map(|expr| self.process_expr_impl(expr)),
//                 ret_type,
//             ) {
//                 (None, RefType::Void) => Ok(Statement::Return(None)),
//                 (Some(Ok((e, RefType::Int, _))), RefType::Int) => {
//                     Ok(Statement::Return(Some(e)))
//                 }
//                 (Some(Err(s)), _) => Err(s),
//                 _ => Err("return 语句的返回值与函数签名不匹配".to_string()),
//             },
//             Rule::if_statement => self.parse_if(iter, in_while, ret_type),
//             Rule::while_statement => self.parse_while(iter, ret_type),
//             Rule::break_keyword => {
//                 if in_while {
//                     Ok(Statement::Break)
//                 } else {
//                     Err("在 while 循环外使用了 break".to_string())
//                 }
//             }
//             Rule::continue_keyword => {
//                 if in_while {
//                     Ok(Statement::Continue)
//                 } else {
//                     Err("在 while 循环外使用了 continue".to_string())
//                 }
//             }
//             _ => unreachable!(),
//         }
//     }

//     fn parse_block(
//         &mut self,
//         block: Pair<Rule>,
//         in_while: bool,
//         ret_type: &Type,
//     ) -> Result<Block, String> {
//         self.enter_scope();
//         let block = block
//             .into_inner()
//             .filter(|pair| {
//                 !matches!(pair.as_rule(), Rule::int_keyword | Rule::const_keyword)
//             })
//             .map(|pair| match pair.as_rule() {
//                 Rule::block => {
//                     Ok(BlockItem::Block(self.parse_block(pair, in_while, ret_type)?))
//                 }
//                 Rule::expression
//                 | Rule::return_statement
//                 | Rule::if_statement
//                 | Rule::while_statement
//                 | Rule::break_keyword
//                 | Rule::continue_keyword => Ok(BlockItem::Statement(
//                     self.parse_statement(pair, in_while, ret_type)?,
//                 )),
//                 Rule::variable_definition
//                 | Rule::array_definition
//                 | Rule::const_variable_definition
//                 | Rule::const_array_definition => {
//                     Ok(BlockItem::Def(self.parse_definition(pair)?))
//                 }
//                 _ => unreachable!(),
//             })
//             .collect::<Result<_, _>>();
//         self.exit_scope();
//         block
//     }

//     fn parse_signature(&self, pair: Pair<Rule>) -> Result<Signature, String> {
//         let mut iter = pair.into_inner();
//         let return_type = match iter.next().unwrap().as_rule() {
//             Rule::void_keyword => Void,
//             _ => Int,
//         };
//         let id = iter.next().unwrap().as_str().to_string();
//         let mut para_id = Vec::new();
//         let mut para_type = Vec::new();
//         for para in iter.next().unwrap().into_inner() {
//             match para.as_rule() {
//                 Rule::var_parameter => {
//                     para_id.push(Some(
//                         para.into_inner().nth(1).unwrap().as_str().to_string(),
//                     ));
//                     para_type.push(Int);
//                 }
//                 Rule::ptr_parameter => {
//                     let mut iter = para.into_inner().skip(1);
//                     let id = iter.next().unwrap().as_str().to_string();
//                     let lengths = self.iter_to_vec(iter.next())?;
//                     para_id.push(Some(id));
//                     para_type.push(IntPointer(lengths));
//                 }
//                 Rule::var_parameter_no_name => {
//                     para_id.push(None);
//                     para_type.push(Int);
//                 }
//                 Rule::ptr_parameter_no_name => {
//                     let lengths = self.iter_to_vec(para.into_inner().nth(1))?;
//                     para_id.push(None);
//                     para_type.push(IntPointer(lengths));
//                 }
//                 _ => unreachable!(),
//             }
//         }
//         Ok((id, return_type, para_type, para_id))
//     }

//     fn parse_function(&mut self, func: Pair<Rule>) -> Result<Handler, String> {
//         let mut iter = func.into_inner();
//         let (id, ret_type, para_type, para_id) =
//             self.parse_signature(iter.next().unwrap())?;
//         match iter.next() {
//             Some(_) => todo!(),
//             None => todo!(),
//         }
//         self.enter_scope();
//         // for (ty, id) in para_type.into_iter().zip(para_id.iter_mut()) {
//         //     if let Some(i) = id {
//         //         *i = self.insert_definition(take(i), ty, None)?.1;
//         //     }
//         // }
//         let block = self.parse_block(iter.next().unwrap(), false, ret_type)?;
//         self.exit_scope();
//         let is_entry = false;
//         self.insert_definition(
//             id,
//             Function(Box::new(ret_type.clone()), para_type.clone()),
//             Some(Init::Function { block, is_entry }),
//         )
//     }

//     fn parse_global_item(&mut self, pair: Pair<Rule>) -> Result<Handler, String> {
//         match pair.as_rule() {
//             Rule::variable_definition
//             | Rule::array_definition
//             | Rule::const_variable_definition
//             | Rule::const_array_definition => self.parse_definition(pair),
//             Rule::func_decl | Rule::func_def => self.parse_function(pair),
//             _ => unreachable!(),
//         }
//     }

//     fn parse(mut self, code: &str) -> Result<TranslationUnit, String> {
//         let sysy_lib = [
//             (Function(Box::new(Int), Vec::new()), "getint".to_string()),
//             (Function(Box::new(Int), Vec::new()), "getch".to_string()),
//             (
//                 Function(Box::new(Int), vec![Pointer(Box::new(Int))]),
//                 "getarray".to_string(),
//             ),
//             (Function(Box::new(Void), vec![Int]), "putint".to_string()),
//             (Function(Box::new(Void), vec![Int]), "putch".to_string()),
//             (
//                 Function(Box::new(Void), vec![Int, Pointer(Box::new(Int))]),
//                 "putarray".to_string(),
//             ),
//             (Function(Box::new(Void), Vec::new()), "starttime".to_string()),
//             (Function(Box::new(Void), Vec::new()), "stoptime".to_string()),
//         ]
//         .into_iter()
//         .map(|(ty, id)| self.insert_definition(id, ty, None));

//         let ast_iter = SysYParser::parse(Rule::translation_unit, code)
//             .unwrap()
//             .filter(|pair| !matches!(pair.as_rule(), Rule::EOI))
//             .map(|pair| self.parse_global_item(pair));
//         let ast = sysy_lib.chain(ast_iter).collect::<Result<_, _>>()?;
//         Ok(TranslationUnit { ast, symbol_table: self.symbol_table })
//     }
// }

pub fn parse(code: &str) -> Result<pest::iterators::Pairs<Rule>, String> {
    Ok(SysYParser::parse(Rule::translation_unit, code).unwrap())
}
