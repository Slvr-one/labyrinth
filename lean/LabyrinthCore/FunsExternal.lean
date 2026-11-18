-- Repo-owned models for the external operations stock Aeneas 87cfe2f5 leaves as templates.
module
public import Aeneas
public import LabyrinthCore.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open labyrinth_core

/-- Non-negative remainder. Inherits stock `IScalar.rem` semantics: `MIN % -1 = 0`, where Rust panics
    (documented model limit; every crate call site uses a positive constant divisor). -/
@[rust_fun "core::num::{i32}::rem_euclid"]
def core.num.I32.rem_euclid (x y : Std.I32) : Result Std.I32 := do
  let r ← IScalar.rem x y
  if r.val < 0 then IScalar.tryMk .I32 (r.val + (y.val.natAbs : Int)) else ok r

/-- `MIN.abs()` fails, as in Rust debug builds. Not `wrapping_abs`. -/
@[rust_fun "core::num::{i32}::abs"]
def core.num.I32.abs (x : Std.I32) : Result Std.I32 :=
  if x.val < 0 then IScalar.neg x else ok x

/-- `RangeBounds::contains`: the end bound is exclusive once `exhausted`; `&&` short-circuits. -/
@[rust_fun
  "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains"]
def core.ops.range.RangeInclusive.contains
  {Idx : Type _} {U : Type _} (_idxOrd : core.cmp.PartialOrd Idx Idx)
  (startOrd : core.cmp.PartialOrd Idx U) (itemOrd : core.cmp.PartialOrd U Idx)
  (self : core.ops.range.RangeInclusive Idx) (item : U) : Result Bool := do
  let lo ← startOrd.le self.start item
  if lo then
    if self.exhausted then itemOrd.lt item self.«end» else itemOrd.le item self.«end»
  else ok false

/-- Branch-preserving derived `Option` Debug, relative to the existing formatter helpers.
    Names are UTF-8 byte slices "None"/"Some". -/
@[rust_fun "core::option::{core::fmt::Debug<core::option::Option<@T>>}::fmt"]
def core.option.Option.Insts.CoreFmtDebug.fmt
  {T : Type _} (debugInstance : core.fmt.Debug T) (x : Option T) (formatter : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  match x with
  | none => core.fmt.Formatter.write_str formatter
      (Slice.from (α := U8) [⟨78⟩, ⟨111⟩, ⟨110⟩, ⟨101⟩] (by scalar_tac))
  | some payload =>
    core.fmt.Formatter.debug_tuple_field1_finish formatter
      (Slice.from (α := U8) [⟨83⟩, ⟨111⟩, ⟨109⟩, ⟨101⟩] (by scalar_tac))
      (Dyn.mk T debugInstance payload)

/-- References are values in the model; the `Copy` clause is what extraction passes. -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied
  {T : Type _} (_copyInst : core.marker.Copy T) (x : Option T) : Result (Option T) :=
  ok x

@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
  {T : Type _} (cloneInst : core.clone.Clone T) (x : Option T) : Result (Option T) :=
  match x with
  | none => ok none
  | some value => do
    let value' ← cloneInst.clone value
    ok (some value')

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type _} (eqInst : core.cmp.PartialEq T T) (x y : Option T) : Result Bool :=
  match x, y with
  | none, none => ok true
  | some left, some right => eqInst.eq left right
  | _, _ => ok false

/-- Content-level `Vec::clear`: the model has no capacity, so this makes no capacity claim.
    `A` is the allocator type that stock extraction passes (`alloc.alloc.Global`). -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear
  {T : Type _} (_A : Type _) (_v : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

namespace Aeneas.Std
/-- Stock Aeneas prints Charon's OUB signed division as `I32.div`, which Std does not define.
    Charon emits it only after explicit zero and `MIN / -1` checks; `IScalar.div` also fails on both. -/
def I32.div (x y : I32) : Result I32 := IScalar.div x y
end Aeneas.Std
