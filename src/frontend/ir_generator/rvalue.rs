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

use super::{Definition, Generator};
use crate::frontend::{ast::Expr, ast::ExprInner::*, ty::Type};
use crate::{backend::chollima::*, risk};
use std::collections::VecDeque;

#[macro_export]
macro_rules! int_arith_helper {
    ($ir_generator: expr, $l: expr, $r: expr, $op: path, $expected_ty: expr) => {{
        let l_ty = &$l.ty;
        let r_ty = &$r.ty;
        match (l_ty, r_ty, $expected_ty) {
            (Type::Int, Type::Int, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Int);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Int));
                ir.push_back($op);
                ir
            }
            (Type::Int, Type::Int, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Int);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Int));
                ir.extend([$op, IRItem::CvtIF]);
                ir
            }
            _ => unreachable!(),
        }
    }};
}

#[macro_export]
macro_rules! cmp_helper {
    ($ir_generator: expr, $l: expr, $r: expr, $op_1: path, $op_2: path, $expected_ty: expr) => {{
        let l_ty = &$l.ty;
        let r_ty = &$r.ty;
        match (l_ty, r_ty, $expected_ty) {
            (Type::Int, Type::Int, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Int);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Int));
                ir.push_back($op_1);
                ir
            }
            (Type::Int, Type::Int, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Int);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Int));
                ir.extend([$op_1, IRItem::CvtIF]);
                ir
            }
            (Type::Int, Type::Float, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.push_back($op_2);
                ir
            }
            (Type::Int, Type::Float, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.extend([$op_2, IRItem::CvtIF]);
                ir
            }
            (Type::Float, Type::Int, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.push_back($op_2);
                ir
            }
            (Type::Float, Type::Int, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.extend([$op_2, IRItem::CvtIF]);
                ir
            }
            (Type::Float, Type::Float, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.push_back($op_2);
                ir
            }
            (Type::Float, Type::Float, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.extend([$op_2, IRItem::CvtIF]);
                ir
            }
            _ => unreachable!(),
        }
    }};
}

#[macro_export]
macro_rules! arith_helper {
    ($ir_generator: expr, $l: expr, $r: expr, $op_1: path, $op_2: path, $expected_ty: expr) => {{
        let l_ty = &$l.ty;
        let r_ty = &$r.ty;
        match (l_ty, r_ty, $expected_ty) {
            (Type::Int, Type::Int, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Int);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Int));
                ir.push_back($op_1);
                ir
            }
            (Type::Int, Type::Int, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Int);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Int));
                ir.extend([$op_1, IRItem::CvtIF]);
                ir
            }
            (Type::Int, Type::Float, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.extend([$op_2, IRItem::CvtFI]);
                ir
            }
            (Type::Int, Type::Float, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.push_back($op_2);
                ir
            }
            (Type::Float, Type::Int, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.extend([$op_2, IRItem::CvtFI]);
                ir
            }
            (Type::Float, Type::Int, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.push_back($op_2);
                ir
            }
            (Type::Float, Type::Float, OpType::Int) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.extend([$op_2, IRItem::CvtFI]);
                ir
            }
            (Type::Float, Type::Float, OpType::Float) => {
                let mut ir = $ir_generator.expr_rvalue(*$l, OpType::Float);
                ir.extend($ir_generator.expr_rvalue(*$r, OpType::Float));
                ir.push_back($op_2);
                ir
            }
            _ => unreachable!(),
        }
    }};
}

impl Generator {
    pub fn expr_rvalue(&self, expr: Expr, expected_ty: OpType) -> VecDeque<IRItem> {
        let Expr { inner, ty, category: _, is_const: _ } = expr;
        match inner {
            Mod(l, r) => int_arith_helper!(self, l, r, IRItem::Mod, expected_ty),

            Mul(l, r) => arith_helper!(self, l, r, IRItem::MulInt, IRItem::MulFloat, expected_ty),
            Div(l, r) => arith_helper!(self, l, r, IRItem::DivInt, IRItem::DivFloat, expected_ty),
            Add(l, r) => arith_helper!(self, l, r, IRItem::AddInt, IRItem::AddFloat, expected_ty),
            Sub(l, r) => arith_helper!(self, l, r, IRItem::SubInt, IRItem::SubFloat, expected_ty),

            ShL(l, r) => int_arith_helper!(self, l, r, IRItem::Sll, expected_ty),
            SaR(l, r) => int_arith_helper!(self, l, r, IRItem::Sar, expected_ty),
            Xor(l, r) => int_arith_helper!(self, l, r, IRItem::Xor, expected_ty),
            And(l, r) => int_arith_helper!(self, l, r, IRItem::And, expected_ty),
            Or(l, r) => int_arith_helper!(self, l, r, IRItem::Or, expected_ty),

            Eq(l, r) => cmp_helper!(self, l, r, IRItem::EqInt, IRItem::EqFloat, expected_ty),
            Neq(l, r) => cmp_helper!(self, l, r, IRItem::NeInt, IRItem::NeFloat, expected_ty),
            Grt(l, r) => cmp_helper!(self, l, r, IRItem::GtInt, IRItem::GtFloat, expected_ty),
            Geq(l, r) => cmp_helper!(self, l, r, IRItem::GeInt, IRItem::GeFloat, expected_ty),
            Les(l, r) => cmp_helper!(self, l, r, IRItem::LtInt, IRItem::LtFloat, expected_ty),
            Leq(l, r) => cmp_helper!(self, l, r, IRItem::LeInt, IRItem::LeFloat, expected_ty),

            LogicAnd(l, r) => todo!(),
            LogicOr(l, r) => todo!(),
            LogicNot(expr) => self.expr_rvalue(
                Expr {
                    inner: Neq(
                        expr,
                        Box::new(Expr {
                            inner: Integer(0),
                            ty: Type::Int,
                            category: super::ExprCategory::RValue,
                            is_const: true,
                        }),
                    ),
                    ty: Type::Int,
                    category: super::ExprCategory::RValue,
                    is_const: false,
                },
                expected_ty,
            ),

            Nega(expr) => {
                let ty = &expr.ty;
                match (ty, expected_ty) {
                    (Type::Int, OpType::Int) => {
                        let mut ir = VecDeque::from([IRItem::PushInt(0)]);
                        ir.extend(self.expr_rvalue(*expr, OpType::Int));
                        ir.push_back(IRItem::SubInt);
                        ir
                    }
                    (Type::Int, OpType::Float) => {
                        let mut ir = VecDeque::from([IRItem::PushInt(0)]);
                        ir.extend(self.expr_rvalue(*expr, OpType::Int));
                        ir.extend([IRItem::SubInt, IRItem::CvtIF]);
                        ir
                    }
                    (Type::Float, OpType::Int) => {
                        let mut ir = VecDeque::from([IRItem::PushFloat(0.0)]);
                        ir.extend(self.expr_rvalue(*expr, OpType::Float));
                        ir.extend([IRItem::SubFloat, IRItem::CvtFI]);
                        ir
                    }
                    (Type::Float, OpType::Float) => {
                        let mut ir = VecDeque::from([IRItem::PushFloat(0.0)]);
                        ir.extend(self.expr_rvalue(*expr, OpType::Float));
                        ir.push_back(IRItem::SubInt);
                        ir
                    }
                    _ => unreachable!(),
                }
            }
            Not(expr) => self.expr_rvalue(
                Expr {
                    inner: Xor(
                        expr,
                        Box::new(Expr {
                            inner: Integer(-1),
                            ty: Type::Int,
                            category: super::ExprCategory::RValue,
                            is_const: true,
                        }),
                    ),
                    ty: Type::Int,
                    category: super::ExprCategory::RValue,
                    is_const: false,
                },
                expected_ty,
            ),
            PostInc(_) => todo!(),
            PostDec(_) => todo!(),
            PreInc(_) => todo!(),
            PreDec(_) => todo!(),
            Assignment(l, r) => todo!(),
            AddAssign(l, r) => todo!(),
            SubAssign(l, r) => todo!(),
            MulAssign(l, r) => todo!(),
            DivAssign(l, r) => todo!(),
            ModAssign(l, r) => todo!(),
            AndAssign(l, r) => todo!(),
            OrAssign(l, r) => todo!(),
            XorAssign(l, r) => todo!(),
            ShLAssign(l, r) => todo!(),
            SaRAssign(l, r) => todo!(),
            Integer(i) => match expected_ty {
                OpType::Int => VecDeque::from([IRItem::PushInt(i)]),
                OpType::Float => VecDeque::from([IRItem::PushFloat(i as f32)]),
                OpType::Void => unreachable!(),
            },
            Floating(f) => match expected_ty {
                OpType::Int => VecDeque::from([IRItem::PushInt(f as i32)]),
                OpType::Float => VecDeque::from([IRItem::PushFloat(f)]),
                OpType::Void => unreachable!(),
            },
            Var(handler) => {
                let Definition { init: _, ty, id: _, is_global: _, is_arg: _ } = self.symbol_table.get(&handler).unwrap();
                match (ty, expected_ty) {
                    (Type::Int, OpType::Int) => VecDeque::from([IRItem::LoadAddr { var: handler }, IRItem::Load]),
                    (Type::Int, OpType::Float) => VecDeque::from([IRItem::LoadAddr { var: handler }, IRItem::Load, IRItem::CvtIF]),
                    (Type::Float, OpType::Int) => VecDeque::from([IRItem::LoadAddr { var: handler }, IRItem::Load, IRItem::CvtFI]),
                    (Type::Float, OpType::Float) => VecDeque::from([IRItem::LoadAddr { var: handler }, IRItem::Load]),
                    (Type::Pointer(_, _), OpType::Int) => VecDeque::from([IRItem::LoadAddr { var: handler }, IRItem::Load]),
                    (Type::Array(_, _), OpType::Int) => VecDeque::from([IRItem::LoadAddr { var: handler }]),
                    _ => unreachable!(),
                }
            }
            Func(handler, args) => {
                let num_args = args.len();
                let ty = &self.symbol_table.get(&handler).unwrap().ty;
                let (ret_ty, arg_tys) = risk!(ty, Type::Function(ret_ty, arg_tys) => (ret_ty.as_ref(), arg_tys.as_slice()));

                let mut ir: VecDeque<_> =
                    args.into_iter().zip(arg_tys).flat_map(|(expr, ty)| self.expr_rvalue(expr, expected_ty)).collect();

                match (ret_ty, expected_ty) {
                    (Type::Int, OpType::Int) => ir.push_back(IRItem::CallInt { function: handler, num_args }),

                    (Type::Int, OpType::Float) => {
                        ir.extend([IRItem::CallInt { function: handler, num_args }, IRItem::CvtIF]);
                    }
                    (Type::Float, OpType::Int) => {
                        ir.extend([IRItem::CallFloat { function: handler, num_args }, IRItem::CvtFI]);
                    }
                    (Type::Float, OpType::Float) => ir.push_back(IRItem::CallFloat { function: handler, num_args }),
                    (_, OpType::Void) => ir.push_back(IRItem::CallVoid { function: handler, num_args }),
                    _ => unreachable!(),
                };

                ir
            }
            ArrayElem(handler, subscripts) => {
                let mut ir = self.array_elem_helper(handler, subscripts);

                match (ty, expected_ty) {
                    (Type::Int, OpType::Int) | (Type::Float, OpType::Float) => ir.push_back(IRItem::Load),
                    (Type::Int, OpType::Float) => ir.extend([IRItem::Load, IRItem::CvtIF]),
                    (Type::Float, OpType::Int) => ir.extend([IRItem::Load, IRItem::CvtFI]),
                    (Type::Pointer(_, _), OpType::Int) => (),
                    _ => unreachable!(),
                }

                ir
            }
        }
    }
}
