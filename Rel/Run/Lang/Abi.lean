module

public import Rel.Run.Lang.Plan
public import Rel.Kernel.Scatter
public import Rel.Kernel.Asc
public import Rel.Kernel.BitRows
public import Rel.Kernel.Db.ObjectFile
public import Rel.Kernel.Db.Csv

@[expose] public section

/-! # The kernel table `Plan.run` calls

Here, in the precompiled `RelRun`, not beside `relc`: each `kernel%` closure marshals the registers of one call, and
in an interpreted module (`Rel`) every kernel call of a run went through the IR interpreter. -/

namespace Rel.Lang.Plan

open Tab

/-- An `ownMap` answer: constructor `0`, its object `parts`, its scalars `code`, `kind`, `count` in
    declaration order, which `Instr.sproj` reads. -/
instance : Reg Db.OwnFile := ⟨.obj, fun
  | .ctor 0 #[ps] #[c, k, n] => do
    pure ⟨← Reg.get? c, ← Reg.get? k, ← Reg.get? n, ← Reg.get? ps⟩
  | _ => none, fun f => .ctor 0 #[.parts f.parts] #[.u8 f.code, .u8 f.kind, .size f.count]⟩

/-- A CSV column's shape is an enum: its constructor index in a byte. -/
instance : Reg Db.CsvShape := ⟨.u8, fun | .u8 0 => some .atom | .u8 1 => some .null | .u8 2 => some .text | .u8 3 => some .opt | _ => none,
  fun s => .u8 s.ctorIdx.toUInt8⟩

/-- The kernels a plan may call, each read off its `@[extern]` declaration: the five of design §4, the IO exports of
    `crate/RELIO.txt` (the column files, the CSV reader and writer) and the toolchain's own arithmetic on sizes,
    bytes and buffers. -/
def abi : List Kernel :=
  [kernel% Rel.Kernel.kscan, kernel% Rel.Kernel.kscatter, kernel% Rel.Kernel.kgather, kernel% Rel.Kernel.kasc,
   kernel% Rel.Kernel.kseen, kernel% Rel.Kernel.kbitrows, kernel% Rel.Db.ownWrite, kernel% Rel.Db.ownMap, kernel% Rel.Db.csvRead,
   kernel% Rel.Db.csvWrite, kernel% Rel.Db.pushPart, kernel% USize.decEq, kernel% UInt8.decEq,
   kernel% USize.add, kernel% USize.sub, kernel% USize.mul, kernel% USize.decLt, kernel% USize.div, kernel% UInt64.toUSize, kernel% USize.toUInt64, kernel% ByteArray.usize]

def abiOf (sym : String) : Option Kernel := abi.find? (·.sym == sym)

end Rel.Lang.Plan
