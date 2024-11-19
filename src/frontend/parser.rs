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

use std::iter::repeat;

use super::ast::{ExprCategory::*, ExprInner::*, *};
use super::error::{CompilerError, ErrorNumber::*};
use super::ty::Type::{self, *};
use crate::{risk, Handler, HashMap, HashSet};
use pest::pratt_parser::Assoc::{Left, Right};
use pest::pratt_parser::{Op, PrattParser};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "frontend/sysy.pest"]
struct SysYParser;

struct Counter {
    value: Handler,
}

impl Counter {
    fn get(&mut self) -> Handler {
        self.value += 1;
        self.value
    }
}
pub struct ASTBuilder {
    expr_parser: PrattParser<Rule>,
    table: Vec<HashMap<String, Handler>>,
    symbol_table: HashMap<Handler, Definition>,
    counter: Counter,
    depth: u32,
}

trait InitListTrait {
    fn new_list(l: Vec<Self>) -> Self
    where
        Self: Sized;
    fn new_item(ast_builder: &ASTBuilder, expr: Pair<Rule>, ty: &Type) -> Result<Self, CompilerError>
    where
        Self: Sized;
    fn get_last(v: &mut Vec<Self>) -> &mut Vec<Self>
    where
        Self: Sized;
    fn add_empty_list(len: &[usize], init_list: Vec<Self>) -> Vec<Self>
    where
        Self: Sized;
    fn generate_empty_list(len: &[usize]) -> Self;
}

impl InitListTrait for ConstInitListItem {
    fn new_list(l: Vec<Self>) -> Self {
        Self::ConstInitList(Box::new(l))
    }
    fn new_item(ast_builder: &ASTBuilder, expr: Pair<Rule>, ty: &Type) -> Result<Self, CompilerError> {
        let line_col = expr.line_col();
        match (ast_builder.parse_expr(expr)?, ty) {
            (Expr { inner: Integer(i), .. }, Int) => Ok(Self::Int(i)),
            (Expr { inner: Floating(f), .. }, Int) => Ok(Self::Int(f as i32)),
            (Expr { inner: Integer(i), .. }, Float) => Ok(Self::Float(i as f32)),
            (Expr { inner: Floating(f), .. }, Float) => Ok(Self::Float(f)),
            (Expr { inner: _, ty: Int | Float, .. }, _) => Err(CompilerError { error_number: NotConst, line_col }),
            (Expr { inner: _, ty: _, .. }, _) => Err(CompilerError { error_number: IncompatibleType, line_col }),
        }
    }
    fn get_last(v: &mut Vec<Self>) -> &mut Vec<Self> {
        risk!(v.last_mut().unwrap(), Self::ConstInitList(l) => l.as_mut())
    }
    fn generate_empty_list(len: &[usize]) -> Self {
        match len.len() {
            0 => Self::Int(0),
            _ => Self::new_list(repeat(Self::generate_empty_list(&len[1..])).take(len[0]).collect()),
        }
    }
    fn add_empty_list(len: &[usize], init_list: Vec<Self>) -> Vec<Self> {
        let empty_list = Self::generate_empty_list(&len[1..]);
        let empty_list_n = len[0] - init_list.len();
        init_list
            .into_iter()
            .map(|item| match item {
                Self::ConstInitList(list) => Self::ConstInitList(Box::new(Self::add_empty_list(&len[1..], *list))),
                i => i,
            })
            .chain(repeat(empty_list).take(empty_list_n))
            .collect()
    }
}

impl InitListTrait for InitListItem {
    fn new_list(l: Vec<Self>) -> Self {
        Self::InitList(Box::new(l))
    }
    fn new_item(ast_builder: &ASTBuilder, expr: Pair<Rule>, ty: &Type) -> Result<Self, CompilerError> {
        let line_col = expr.line_col();
        match (ast_builder.parse_expr(expr)?, ty) {
            (Expr { inner: Integer(i), .. }, Int) => {
                Ok(Self::Expr(Expr { inner: Integer(i), ty: Int, category: RValue, is_const: true }))
            }
            (Expr { inner: Floating(f), .. }, Int) => {
                Ok(Self::Expr(Expr { inner: Integer(f as i32), ty: Int, category: RValue, is_const: true }))
            }
            (Expr { inner: Integer(i), .. }, Float) => {
                Ok(Self::Expr(Expr { inner: Floating(i as f32), ty: Int, category: RValue, is_const: true }))
            }
            (Expr { inner: Floating(f), .. }, Float) => {
                Ok(Self::Expr(Expr { inner: Floating(f), ty: Int, category: RValue, is_const: true }))
            }
            (Expr { inner, ty: Int, category, is_const }, _) => Ok(Self::Expr(Expr { inner, ty: Int, category, is_const })),
            (Expr { inner, ty: Float, category, is_const }, _) => Ok(Self::Expr(Expr { inner, ty: Float, category, is_const })),
            (Expr { inner: _, ty: _, .. }, _) => Err(CompilerError { error_number: IncompatibleType, line_col }),
        }
    }
    fn get_last(v: &mut Vec<Self>) -> &mut Vec<Self> {
        risk!(v.last_mut().unwrap(), Self::InitList(l) => l.as_mut())
    }
    fn generate_empty_list(len: &[usize]) -> Self {
        match len.len() {
            0 => Self::Expr(Expr { inner: Integer(0), ty: Int, category: RValue, is_const: true }),
            _ => Self::new_list(repeat(Self::generate_empty_list(&len[1..])).take(len[0]).collect()),
        }
    }
    fn add_empty_list(len: &[usize], init_list: Vec<Self>) -> Vec<Self> {
        let empty_list = Self::generate_empty_list(&len[1..]);
        let empty_list_n = len[0] - init_list.len();
        init_list
            .into_iter()
            .map(|item| match item {
                Self::InitList(list) => Self::InitList(Box::new(Self::add_empty_list(&len[1..], *list))),
                expr => expr,
            })
            .chain(repeat(empty_list).take(empty_list_n))
            .collect()
    }
}
type Signature = (String, Type, Vec<Type>, Vec<String>);
impl ASTBuilder {
    fn new() -> Self {
        let expr_parser = PrattParser::new()
            .op(Op::infix(Rule::assignment, Right)
                | Op::infix(Rule::add_assign, Right)
                | Op::infix(Rule::sub_assign, Right)
                | Op::infix(Rule::mul_assign, Right)
                | Op::infix(Rule::div_assign, Right)
                | Op::infix(Rule::mod_assign, Right)
                | Op::infix(Rule::and_assign, Right)
                | Op::infix(Rule::or_assign, Right)
                | Op::infix(Rule::xor_assign, Right)
                | Op::infix(Rule::shl_assign, Right)
                | Op::infix(Rule::sar_assign, Right))
            .op(Op::infix(Rule::logic_or, Left))
            .op(Op::infix(Rule::logic_and, Left))
            .op(Op::infix(Rule::xor, Left))
            .op(Op::infix(Rule::or, Left))
            .op(Op::infix(Rule::and, Left))
            .op(Op::infix(Rule::eq, Left) | Op::infix(Rule::neq, Left))
            .op(Op::infix(Rule::grt, Left)
                | Op::infix(Rule::geq, Left)
                | Op::infix(Rule::les, Left)
                | Op::infix(Rule::leq, Left))
            .op(Op::infix(Rule::shl, Left) | Op::infix(Rule::sar, Left))
            .op(Op::infix(Rule::add, Left) | Op::infix(Rule::sub, Left))
            .op(Op::infix(Rule::mul, Left) | Op::infix(Rule::div, Left) | Op::infix(Rule::modu, Left))
            .op(Op::prefix(Rule::logic_not)
                | Op::prefix(Rule::negative)
                | Op::prefix(Rule::positive)
                | Op::prefix(Rule::bit_not)
                | Op::prefix(Rule::pre_inc)
                | Op::prefix(Rule::pre_dec))
            .op(Op::postfix(Rule::post_inc) | Op::postfix(Rule::post_dec));
        Self {
            expr_parser,
            table: vec![HashMap::default()],
            symbol_table: HashMap::default(),
            counter: Counter { value: 0 },
            depth: 0,
        }
    }

    fn is_global_now(&self) -> bool {
        self.depth == 0
    }

    fn is_arg_now(&self) -> bool {
        self.depth == 1
    }

    fn search(&self, id: &str) -> Option<Handler> {
        for map in self.table.iter().rev() {
            if let Some(handler) = map.get(id) {
                return Some(*handler);
            }
        }
        None
    }
    fn insert_definition(&mut self, id: String, ty: Type, init: Option<Init>) -> Result<Handler, CompilerError> {
        if self.table.last().unwrap().contains_key(&id) {
            let old_handler = self.table.last().unwrap().get(&id).unwrap();
            match (self.symbol_table.get(old_handler).unwrap(), &ty) {
                (Definition { init: None, ty: Function(ret_type_1, arg_types_1), .. }, Function(ret_type_2, arg_types_2))
                    if ret_type_1 == ret_type_2 && arg_types_1 == arg_types_2 =>
                {
                    self.symbol_table.get_mut(old_handler).unwrap().init = init;
                    Ok(*old_handler)
                }
                _ => Err(CompilerError { error_number: Redefinition, line_col: (0, 0) }),
            }
        } else {
            let handler = self.counter.get();
            self.table.last_mut().unwrap().insert(id.clone(), handler);
            self.symbol_table
                .insert(handler, Definition { id, init, ty, is_global: self.is_global_now(), is_arg: self.is_arg_now() });
            Ok(handler)
        }
    }
    fn enter_scope(&mut self) {
        self.depth += 1;
        self.table.push(HashMap::default());
    }
    fn exit_scope(&mut self) {
        self.table.pop();
        self.depth -= 1;
    }

    fn iter_to_vec(&self, iter: Option<Pair<Rule>>) -> Result<Vec<usize>, CompilerError> {
        iter.map_or(Ok(Vec::new()), |iter| {
            iter.into_inner()
                .map(|expr| {
                    let line_col = expr.line_col();
                    let Expr { inner, .. } = self.parse_expr(expr)?;
                    match inner {
                        Integer(i) if i >= 0 => Ok(i as usize),
                        Integer(_) => Err(CompilerError { error_number: NegaInt, line_col }),
                        _ => Err(CompilerError { error_number: NotConstInt, line_col }),
                    }
                })
                .collect::<Result<_, _>>()
        })
    }

    fn parse_init_list_impl<T>(
        &self,
        init_list: Pair<Rule>,
        len_prod: &[usize],
        ty: &Type,
    ) -> Result<(Vec<T>, usize), CompilerError>
    where
        T: InitListTrait,
    {
        let line_col = init_list.line_col();
        let mut v = Vec::new();
        let mut sum = 0usize;
        for ele in init_list.into_inner() {
            match ele.as_rule() {
                Rule::initializer_list => {
                    if len_prod.len() == 1 || sum % len_prod[0] != 0 {
                        return Err(CompilerError { error_number: ListShouldBeScalar, line_col: ele.line_col() });
                    }
                    //   对于 `int lint[1][14][51][4]`，计算一个列表：`L = {4, 204, 2856, 2856}`，这个列表给出了每一层的大小.
                    //                                                   ^   ^    ^     ^
                    //                                                   |   |    |     |
                    //                                                   0   1    2     3
                    //   rev_depth 给出了列表中第一个不能被 sum 整除的元素的下标.
                    //   rev_depth == 0 -> 错误，即当前已经填充完毕的元素的个数不能被 L[0] 整除
                    //   rev_depth == 1 -> init_list 对应最内层的列表. 譬如 int array[4][3][2]，init_list 对应 int[2].
                    // 而此时需要 `get_last` 到 `v` 的第 2 层（以最外层为 1 层），然后 push.
                    //   换句话说，`get_last` 的次数是 l.len() - rev_depth.
                    //   若 sum == 0，则 position 返回 None. unwrap 为 0.

                    //   对于 `int lint[1][14][51][4]`，rev_depth == 3 时，意味着 init_list 对应 int[14][51][4]
                    // 需要 `get_last` 0 次
                    let rev_depth = len_prod.iter().position(|prod| sum % prod != 0).unwrap_or(len_prod.len() - 1);
                    let depth = len_prod.len() - rev_depth - 1;
                    let (l, s) = self.parse_init_list_impl(ele, &len_prod[0..rev_depth], ty)?;
                    let v_ref = (0..depth).fold(&mut v, |state, _| {
                        if state.is_empty() {
                            state.push(T::new_list(Vec::new()));
                        }
                        T::get_last(state)
                    });
                    v_ref.push(T::new_list(l));
                    sum += s;
                }
                Rule::expression => {
                    let v_ref = len_prod.iter().rev().skip(1).fold(&mut v, |state, i| {
                        if state.is_empty() || sum % i == 0 {
                            state.push(T::new_list(Vec::new()));
                        }
                        T::get_last(state)
                    });
                    v_ref.push(T::new_item(self, ele, ty)?);
                    sum += 1;
                }
                _ => unreachable!(),
            }
            if sum > *len_prod.last().unwrap() {
                return Err(CompilerError { error_number: InitListTooLong, line_col });
            }
        }
        Ok((v, *len_prod.last().unwrap()))
    }
    fn parse_init_list<T>(&self, init_list: Pair<Rule>, lengths: &[usize], ty: &Type) -> Result<Vec<T>, CompilerError>
    where
        T: InitListTrait,
    {
        let len_prod: Vec<usize> = lengths
            .iter()
            .rev()
            .scan(1, |l, &r| {
                *l *= r;
                Some(*l)
            })
            .collect();
        Ok(T::add_empty_list(lengths, self.parse_init_list_impl::<T>(init_list, &len_prod, ty)?.0))
    }

    fn parse_definition(&mut self, pair: Pair<Rule>) -> Result<Vec<Handler>, CompilerError> {
        match pair.as_rule() {
            Rule::const_definitions => {
                let mut iter = pair.into_inner().filter(|p| !matches!(p.as_rule(), Rule::const_keyword));
                let ty = match iter.next().unwrap().as_rule() {
                    Rule::int_keyword => Int,
                    Rule::float_keyword => Float,
                    _ => unreachable!(),
                };
                iter.map(|pair| match pair.as_rule() {
                    Rule::const_variable_definition => {
                        let mut iter = pair.into_inner();
                        let id = iter.next().unwrap().as_str().to_string();
                        let init = self.parse_expr(iter.next().unwrap())?;
                        if !init.is_const {
                            return Err(CompilerError { error_number: NotConst, line_col: (0, 0) });
                        }
                        let init = match (init.inner, &ty) {
                            (Integer(i), Int) => Init::ConstInt(i),
                            (Integer(i), Float) => Init::ConstFloat(i as f32),
                            (Floating(f), Int) => Init::ConstInt(f as i32),
                            (Floating(f), Float) => Init::ConstFloat(f),
                            _ => unreachable!(),
                        };
                        self.insert_definition(id, ty.clone(), Some(init))
                    }
                    Rule::const_array_definition => {
                        let mut iter = pair.into_inner();
                        let id = iter.next().unwrap().as_str().to_string();
                        let len = self.iter_to_vec(iter.next())?;
                        let init_list = self.parse_init_list(iter.next().unwrap(), &len, &ty)?;
                        self.insert_definition(id, Array(Box::new(ty.clone()), len), Some(Init::ConstList(init_list)))
                    }
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, _>>()
            }
            Rule::definitions => {
                let mut iter = pair.into_inner();
                let ty = match iter.next().unwrap().as_rule() {
                    Rule::int_keyword => Int,
                    Rule::float_keyword => Float,
                    _ => unreachable!(),
                };
                iter.map(|pair| match pair.as_rule() {
                    Rule::variable_definition => {
                        let mut iter = pair.into_inner();
                        let id = iter.next().unwrap().as_str().to_string();
                        match iter.next() {
                            Some(expr) => {
                                let line_col = expr.line_col();
                                let expr = self.parse_expr(expr)?;
                                if !matches!(&expr.ty, Int | Float) {
                                    return Err(CompilerError { error_number: IncompatibleType, line_col });
                                }
                                self.insert_definition(id, ty.clone(), Some(Init::Expr(expr)))
                            }
                            None => self.insert_definition(id, ty.clone(), None),
                        }
                    }
                    Rule::array_definition => {
                        let mut iter = pair.into_inner();
                        let id = iter.next().unwrap().as_str().to_string();
                        let len = self.iter_to_vec(iter.next())?;
                        match iter.next() {
                            Some(i) => {
                                let init_list = self.parse_init_list(i, &len, &ty)?;
                                self.insert_definition(id, Array(Box::new(ty.clone()), len), Some(Init::List(init_list)))
                            }
                            None => self.insert_definition(id, Array(Box::new(ty.clone()), len), None),
                        }
                    }
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, _>>()
            }
            _ => unreachable!(),
        }
    }

    fn parse_if_while_helper(&mut self, pair: Pair<Rule>, in_while: bool, ret_type: &Type) -> Result<Block, CompilerError> {
        match pair.as_rule() {
            Rule::block => self.parse_block(pair, in_while, ret_type),
            Rule::empty_statement => Ok(Vec::new()),
            Rule::expression
            | Rule::return_statement
            | Rule::if_statement
            | Rule::while_statement
            | Rule::break_keyword
            | Rule::continue_keyword => Ok(vec![BlockItem::Statement(self.parse_statement(pair, in_while, ret_type)?)]),
            Rule::const_definitions | Rule::definitions => {
                self.enter_scope();
                let ret = Ok(vec![BlockItem::Def(self.parse_definition(pair)?)]);
                self.exit_scope();
                ret
            }
            _ => unreachable!(),
        }
    }

    fn parse_if(&mut self, pair: Pair<Rule>, in_while: bool, ret_type: &Type) -> Result<Statement, CompilerError> {
        let mut iter = pair.into_inner();
        Ok(Statement::If(
            self.parse_expr(iter.next().unwrap())?,
            Box::new(self.parse_if_while_helper(iter.next().unwrap(), in_while, ret_type)?),
            match iter.next() {
                Some(block) => Box::new(self.parse_if_while_helper(block, in_while, ret_type)?),
                None => Box::default(),
            },
        ))
    }

    fn parse_while(&mut self, pair: Pair<Rule>, ret_type: &Type) -> Result<Statement, CompilerError> {
        let mut iter = pair.into_inner();
        Ok(Statement::While(
            self.parse_expr(iter.next().unwrap())?,
            Box::new(self.parse_if_while_helper(iter.next().unwrap(), true, ret_type)?),
        ))
    }

    fn parse_statement(&mut self, iter: Pair<Rule>, in_while: bool, ret_type: &Type) -> Result<Statement, CompilerError> {
        match iter.as_rule() {
            Rule::expression => Ok(Statement::Expr(self.parse_expr(iter)?)),
            Rule::return_statement => match (iter.into_inner().nth(1).map(|expr| self.parse_expr(expr)), ret_type) {
                (None, Void) => Ok(Statement::Return(None)),
                (Some(Ok(expr)), Int | Float) => match &expr.ty {
                    Int | Float => Ok(Statement::Return(Some(expr))),
                    _ => Err(CompilerError { error_number: IncompatibleType, line_col: (0, 0) }),
                },
                (Some(Err(err)), _) => Err(err),
                (Some(Ok(Expr { inner: _, ty: _, .. })), Void) => {
                    Err(CompilerError { error_number: IncompatibleType, line_col: (0, 0) })
                }
                _ => unreachable!(),
            },
            Rule::if_statement => self.parse_if(iter, in_while, ret_type),
            Rule::while_statement => self.parse_while(iter, ret_type),
            Rule::break_keyword => {
                if in_while {
                    Ok(Statement::Break)
                } else {
                    Err(CompilerError { error_number: BreakNotInLoop, line_col: iter.line_col() })
                }
            }
            Rule::continue_keyword => {
                if in_while {
                    Ok(Statement::Continue)
                } else {
                    Err(CompilerError { error_number: ContinueNotInLoop, line_col: iter.line_col() })
                }
            }
            _ => unreachable!(),
        }
    }

    fn parse_block(&mut self, block: Pair<Rule>, in_while: bool, ret_type: &Type) -> Result<Block, CompilerError> {
        self.enter_scope();
        let block = block
            .into_inner()
            .filter(|pair| !matches!(pair.as_rule(), Rule::empty_statement))
            .map(|pair| match pair.as_rule() {
                Rule::block => Ok(BlockItem::Block(self.parse_block(pair, in_while, ret_type)?)),
                Rule::expression
                | Rule::return_statement
                | Rule::if_statement
                | Rule::while_statement
                | Rule::break_keyword
                | Rule::continue_keyword => Ok(BlockItem::Statement(self.parse_statement(pair, in_while, ret_type)?)),
                Rule::const_definitions | Rule::definitions => Ok(BlockItem::Def(self.parse_definition(pair)?)),
                _ => unreachable!(),
            })
            .collect::<Result<_, _>>();
        self.exit_scope();
        block
    }

    fn parse_signature(&self, pair: Pair<Rule>) -> Result<Signature, CompilerError> {
        let mut iter = pair.into_inner();
        let return_type = match iter.next().unwrap().as_rule() {
            Rule::void_keyword => Void,
            Rule::int_keyword => Int,
            Rule::float_keyword => Float,
            _ => unreachable!(),
        };
        let id = iter.next().unwrap().as_str().to_string();
        let mut para_id = Vec::new();
        let mut para_type = Vec::new();
        for para in iter.next().unwrap().into_inner() {
            match para.as_rule() {
                Rule::var_parameter => {
                    let mut iter = para.into_inner();
                    let ty = match iter.next().unwrap().as_rule() {
                        Rule::int_keyword => Int,
                        Rule::float_keyword => Float,
                        _ => unreachable!(),
                    };
                    let id = iter.next().unwrap().as_str().to_string();
                    para_type.push(ty);
                    para_id.push(id);
                }
                Rule::ptr_parameter => {
                    let mut iter = para.into_inner();
                    let ty = match iter.next().unwrap().as_rule() {
                        Rule::int_keyword => Int,
                        Rule::float_keyword => Float,
                        _ => unreachable!(),
                    };
                    let id = iter.next().unwrap().as_str().to_string();
                    let lens = self.iter_to_vec(iter.next())?;
                    para_type.push(Pointer(Box::new(ty), lens));
                    para_id.push(id);
                }
                _ => unreachable!(),
            }
        }
        Ok((id, return_type, para_type, para_id))
    }

    fn parse_function(&mut self, func: Pair<Rule>) -> Result<Vec<Handler>, CompilerError> {
        let mut iter = func.into_inner();
        let (id, ret_type, para_type, para_id) = self.parse_signature(iter.next().unwrap())?;
        let is_entry = id.as_str() == "main";
        let handler = match iter.next() {
            Some(i) => {
                self.insert_definition(id.clone(), Function(Box::new(ret_type.clone()), para_type.clone()), None)?;
                self.enter_scope();
                let arg_handlers = para_type
                    .iter()
                    .zip(para_id.iter())
                    .map(|(ty, id)| self.insert_definition(id.clone(), ty.clone(), None))
                    .collect::<Result<Vec<_>, _>>()?;
                let block = self.parse_block(i, false, &ret_type)?;
                self.exit_scope();
                self.insert_definition(
                    id,
                    Function(Box::new(ret_type), para_type),
                    Some(Init::Function { block, is_entry, arg_handlers }),
                )
            }
            None => {
                self.exit_scope();
                self.insert_definition(id, Function(Box::new(ret_type), para_type), None)
            }
        }?;
        Ok(vec![handler])
    }

    fn parse_global_item(&mut self, pair: Pair<Rule>) -> Result<Vec<Handler>, CompilerError> {
        match pair.as_rule() {
            Rule::const_definitions | Rule::definitions => self.parse_definition(pair),
            Rule::func_decl | Rule::func_def => self.parse_function(pair),
            _ => unreachable!(),
        }
    }

    fn parse(mut self, code: &str) -> Result<TranslationUnit, CompilerError> {
        let mut ast = Vec::new();
        let mut set = HashSet::default();
        let sysy_lib = [
            (Function(Box::new(Int), Vec::new()), "getint".to_string()),
            (Function(Box::new(Int), Vec::new()), "getch".to_string()),
            (Function(Box::new(Float), Vec::new()), "getfloat".to_string()),
            (Function(Box::new(Int), vec![Pointer(Box::new(Int), Vec::new())]), "getarray".to_string()),
            (Function(Box::new(Int), vec![Pointer(Box::new(Float), Vec::new())]), "getfarray".to_string()),
            (Function(Box::new(Void), vec![Int]), "putint".to_string()),
            (Function(Box::new(Void), vec![Int]), "putch".to_string()),
            (Function(Box::new(Void), vec![Float]), "putfloat".to_string()),
            (Function(Box::new(Void), vec![Int, Pointer(Box::new(Int), Vec::new())]), "putarray".to_string()),
            (Function(Box::new(Void), vec![Int, Pointer(Box::new(Float), Vec::new())]), "putfarray".to_string()),
            (Function(Box::new(Void), vec![VAList]), "putf".to_string()),
            (Function(Box::new(Void), vec![Int]), "_sysy_starttime".to_string()),
            (Function(Box::new(Void), vec![Int]), "_sysy_stoptime".to_string()),
        ]
        .into_iter()
        .map(|(ty, id)| self.insert_definition(id, ty, None));
        for i in sysy_lib {
            let handler = i?;
            if !set.contains(&handler) {
                ast.push(handler);
                set.insert(handler);
            }
        }
        let ast_iter = SysYParser::parse(Rule::translation_unit, code)
            .unwrap()
            .filter(|pair| !matches!(pair.as_rule(), Rule::EOI))
            .map(|pair| self.parse_global_item(pair));
        for i in ast_iter {
            let i = i?;
            for handler in i {
                if !set.contains(&handler) {
                    ast.push(handler);
                    set.insert(handler);
                }
            }
        }
        Ok(TranslationUnit { ast, symbol_table: self.symbol_table })
    }
}

pub fn parse(code: &str) -> Result<TranslationUnit, CompilerError> {
    ASTBuilder::new().parse(code)
}
