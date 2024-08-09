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

#![allow(warnings)]
use std::fmt::{Display, Formatter, Result};

#[derive(Clone)]
pub enum Inst {
    Push(Reg),
    Pop(Reg),
    VPush(Reg),
    VPop(Reg),
    VEor(Reg, Reg, Reg),

    Blx(Reg),
    Bx(Reg),

    BxNe(Reg),
    Cmp(Reg, Reg),
    VCmpF32(Reg, Reg),

    Ldr(Reg, Reg),
    Sdr(Reg, Reg),
    Mov32(Reg, i32),
    Mov32Label(Reg, String),
    Mov(Reg, Reg),

    Load1Eq(Reg),
    Load1Ne(Reg),
    Load1Ge(Reg),
    Load1Gt(Reg),
    Load1Le(Reg),
    Load1Lt(Reg),

    VLoad1Eq(Reg),
    VLoad1Ne(Reg),
    VLoad1Ge(Reg),
    VLoad1Gt(Reg),
    VLoad1Le(Reg),
    VLoad1Lt(Reg),

    Add(Reg, Reg, Reg),
    Sub(Reg, Reg, Reg),
    Mul(Reg, Reg, Reg),
    Sdiv(Reg, Reg, Reg),

    VAddF32(Reg, Reg, Reg),
    VSubF32(Reg, Reg, Reg),
    VMulF32(Reg, Reg, Reg),
    VDivF32(Reg, Reg, Reg),

    Eor(Reg, Reg, Reg),
    Orr(Reg, Reg, Reg),
    And(Reg, Reg, Reg),
    Lsl(Reg, Reg, Reg),
    Lsr(Reg, Reg, Reg),
    Asr(Reg, Reg, Reg),
}

#[derive(Clone, Copy, PartialEq)]
pub enum Reg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11, // BP
    R12,
    R13, // SP
    R14, // LR
    R15, // PC

    S0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    S12,
    S13,
    S14,
    S15,
}

#[derive(Clone)]
pub enum Directive {
    Text,
    Global(String),
    Data,
    Zero(usize),
    Word(Vec<u32>),
}

#[derive(Clone)]
pub enum ARMItem {
    Label(String),
    Inst(Inst),
    Directive(Directive),
}

pub type ARM = Vec<ARMItem>;

impl Display for Reg {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Reg::R0 => write!(f, "r0"),
            Reg::R1 => write!(f, "r1"),
            Reg::R2 => write!(f, "r2"),
            Reg::R3 => write!(f, "r3"),
            Reg::R4 => write!(f, "r4"),
            Reg::R5 => write!(f, "r5"),
            Reg::R6 => write!(f, "r6"),
            Reg::R7 => write!(f, "r7"),
            Reg::R8 => write!(f, "r8"),
            Reg::R9 => write!(f, "r9"),
            Reg::R10 => write!(f, "r10"),
            Reg::R11 => write!(f, "r11"),
            Reg::R12 => write!(f, "r12"),
            Reg::R13 => write!(f, "r13"),
            Reg::R14 => write!(f, "r14"),
            Reg::R15 => write!(f, "r15"),

            Reg::S0 => write!(f, "s0"),
            Reg::S1 => write!(f, "s1"),
            Reg::S2 => write!(f, "s2"),
            Reg::S3 => write!(f, "s3"),
            Reg::S4 => write!(f, "s4"),
            Reg::S5 => write!(f, "s5"),
            Reg::S6 => write!(f, "s6"),
            Reg::S7 => write!(f, "s7"),
            Reg::S8 => write!(f, "s8"),
            Reg::S9 => write!(f, "s9"),
            Reg::S10 => write!(f, "s10"),
            Reg::S11 => write!(f, "s11"),
            Reg::S12 => write!(f, "s12"),
            Reg::S13 => write!(f, "s13"),
            Reg::S14 => write!(f, "s14"),
            Reg::S15 => write!(f, "s15"),
        }
    }
}

pub trait ARMTrait {
    fn add_label(&mut self, label: String);
    fn add_inst(&mut self, inst: Inst);
    fn add_directive(&mut self, directive: Directive);
}

impl ARMTrait for ARM {
    fn add_label(&mut self, label: String) {
        self.push(ARMItem::Label(label));
    }
    fn add_inst(&mut self, inst: Inst) {
        self.push(ARMItem::Inst(inst));
    }
    fn add_directive(&mut self, directive: Directive) {
        self.push(ARMItem::Directive(directive));
    }
}

impl Display for Inst {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Ldr(rd, rs) => write!(f, "ldr {rd}, [{rs}]"),
            Self::Sdr(rs_1, rs_2) => write!(f, "str {rs_1}, [{rs_2}]"),

            Self::Add(rd, rs_1, rs_2) => write!(f, "add {rd}, {rs_1}, {rs_2}"),
            Self::Sub(rd, rs_1, rs_2) => write!(f, "sub {rd}, {rs_1}, {rs_2}"),
            Self::And(rd, rs_1, rs_2) => write!(f, "and {rd}, {rs_1}, {rs_2}"),
            Self::Mul(rd, rs_1, rs_2) => write!(f, "mul {rd}, {rs_1}, {rs_2}"),
            Self::Sdiv(rd, rs_1, rs_2) => write!(f, "sdiv {rd}, {rs_1}, {rs_2}"),

            Self::Push(reg) => write!(f, "push {{{reg}}}"),
            Self::Pop(reg) => write!(f, "pop {{{reg}}}"),
            Self::VPush(reg) => write!(f, "vpush {{{reg}}}"),
            Self::VPop(reg) => write!(f, "vpop {{{reg}}}"),

            Self::Blx(reg) => write!(f, "blx {reg}"),
            Self::Bx(reg) => write!(f, "bx {reg}"),
            Self::Mov32(reg, imm) => write!(f, "mov32 {reg}, {}", *imm as u32),
            Self::Mov32Label(reg, label) => write!(f, "mov32 {reg}, {label}"),
            Self::Mov(rd, rs) => write!(f, "mov {rd}, {rs}"),

            Self::VAddF32(rd, rs_1, rs_2) => write!(f, "vadd.f32 {rd}, {rs_1}, {rs_2}"),
            Self::VSubF32(rd, rs_1, rs_2) => write!(f, "vsub.f32 {rd}, {rs_1}, {rs_2}"),
            Self::VMulF32(rd, rs_1, rs_2) => write!(f, "vmul.f32 {rd}, {rs_1}, {rs_2}"),
            Self::VDivF32(rd, rs_1, rs_2) => write!(f, "vdiv.f32 {rd}, {rs_1}, {rs_2}"),
            Self::Eor(rd, rs_1, rs_2) => write!(f, "eor {rd}, {rs_1}, {rs_2}"),
            Self::Orr(rd, rs_1, rs_2) => write!(f, "orr {rd}, {rs_1}, {rs_2}"),
            Self::And(rd, rs_1, rs_2) => write!(f, "and {rd}, {rs_1}, {rs_2}"),
            Self::Lsl(rd, rs_1, rs_2) => write!(f, "lsl {rd}, {rs_1}, {rs_2}"),
            Self::Lsr(rd, rs_1, rs_2) => write!(f, "lsr {rd}, {rs_1}, {rs_2}"),
            Self::Asr(rd, rs_1, rs_2) => write!(f, "asr {rd}, {rs_1}, {rs_2}"),
            Self::BxNe(reg) => write!(f, "bxne {reg}"),
            Self::Cmp(rd, rs) => write!(f, "cmp {rd}, {rs}"),
            Self::VCmpF32(rd, rs) => write!(f, "vcmp.f32 {rd}, {rs}"),

            Self::Load1Eq(reg) => write!(f, "moveq {reg}, #1"),
            Self::Load1Ne(reg) => write!(f, "movne {reg}, #1"),
            Self::Load1Ge(reg) => write!(f, "movge {reg}, #1"),
            Self::Load1Gt(reg) => write!(f, "movgt {reg}, #1"),
            Self::Load1Le(reg) => write!(f, "movle {reg}, #1"),
            Self::Load1Lt(reg) => write!(f, "movlt {reg}, #1"),

            Self::VEor(rd, rs_1, rs_2) => write!(f, "veor.f32 {rd}, {rs_1}, {rs_2}"),

            Self::VLoad1Eq(reg) => write!(f, "vldreq.f32 {reg}, #1"),
            Self::VLoad1Ne(reg) => write!(f, "vldrne.f32 {reg}, #1"),
            Self::VLoad1Ge(reg) => write!(f, "vldrge.f32 {reg}, #1"),
            Self::VLoad1Gt(reg) => write!(f, "vldrgt.f32 {reg}, #1"),
            Self::VLoad1Le(reg) => write!(f, "vldrle.f32 {reg}, #1"),
            Self::VLoad1Lt(reg) => write!(f, "vldrlt.f32 {reg}, #1"),
        }
    }
}

impl Display for Directive {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Text => write!(f, ".text"),
            Self::Global(label) => write!(f, ".global {label}"),
            Self::Data => write!(f, ".data"),
            Self::Zero(len) => write!(f, ".zero {len}"),
            Self::Word(nums) => {
                let data: Vec<_> = nums.iter().map(u32::to_string).collect();
                write!(f, ".word {}", data.as_slice().join(", "))
            }
        }
    }
}

impl Display for ARMItem {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Label(label) => writeln!(f, "{label}:"),
            Self::Inst(inst) => writeln!(f, "    {inst}"),
            Self::Directive(directive) => writeln!(f, "{directive}"),
        }
    }
}
