module
public import LabyrinthCore.ConstructorDFSInvariant
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

theorem constructor_dfs_stack_fuel_prefix (frames : List spanning_tree.Frame)
    (depth index : Nat) (frame : spanning_tree.Frame) (hi : depth ≤ index) :
    constructorDFSStackFuel depth (frames.set index frame) = constructorDFSStackFuel depth frames := by
  induction frames generalizing depth index with
  | nil => cases depth <;> simp [constructorDFSStackFuel]
  | cons first rest ih =>
    cases depth with
    | zero => rfl
    | succ depth =>
      cases index with
      | zero => omega
      | succ index =>
        simp only [List.set, constructorDFSStackFuel]
        rw [ih depth index (by omega)]

theorem constructor_dfs_stack_fuel_top (frames : List spanning_tree.Frame)
    (depth : Nat) (frame : spanning_tree.Frame) (hd : depth < frames.length) :
    constructorDFSStackFuel (depth + 1) (frames.set depth frame) =
      constructorDFSStackFuel depth frames + frame.remaining.val := by
  induction frames generalizing depth with
  | nil => simp at hd
  | cons first rest ih =>
    cases depth with
    | zero => simp [constructorDFSStackFuel]
    | succ depth =>
      have hr : depth < rest.length := by simp only [List.length_cons] at hd; omega
      simp only [List.set, constructorDFSStackFuel]
      rw [ih depth hr]
      omega

theorem constructor_dfs_stack_fuel_last (frames : List spanning_tree.Frame)
    (depth : Nat) (frame : spanning_tree.Frame) (hf : frames[depth]? = some frame) :
    constructorDFSStackFuel (depth + 1) frames =
      constructorDFSStackFuel depth frames + frame.remaining.val := by
  induction frames generalizing depth with
  | nil => simp at hf
  | cons first rest ih =>
    cases depth with
    | zero =>
      have he : first = frame := by simpa using hf
      simp [constructorDFSStackFuel, he]
    | succ depth =>
      have hr : rest[depth]? = some frame := by simpa using hf
      simp only [constructorDFSStackFuel]
      rw [ih depth hr]
      omega

/-- Popping an exhausted top frame strictly consumes the depth summand. -/
theorem constructor_dfs_measure_pop (vertices slots reached depth : Nat)
    (frames : List spanning_tree.Frame) (frame : spanning_tree.Frame)
    (hf : frames[depth]? = some frame) (hz : frame.remaining.val = 0) :
    constructorDFSMeasure vertices slots reached depth frames <
      constructorDFSMeasure vertices slots reached (depth + 1) frames := by
  unfold constructorDFSMeasure
  rw [constructor_dfs_stack_fuel_last frames depth frame hf, hz]
  omega

/-- A scan consumes one unit even when its endpoint was already discovered. -/
theorem constructor_dfs_measure_scan (vertices slots reached depth : Nat)
    (frames : List spanning_tree.Frame) (index : Usize) (frame advanced : spanning_tree.Frame)
    (hi : index.val + 1 = depth) (hb : index.val < frames.length)
    (hf : frames[index.val]? = some frame) (hpos : 0 < frame.remaining.val)
    (hr : advanced.remaining.val = frame.remaining.val - 1) :
    constructorDFSMeasure vertices slots reached depth (frames.set index.val advanced) <
      constructorDFSMeasure vertices slots reached depth frames := by
  unfold constructorDFSMeasure
  rw [← hi, constructor_dfs_stack_fuel_top frames index.val advanced hb,
    constructor_dfs_stack_fuel_last frames index.val frame hf, hr]
  omega

/-- The fresh-discovery block pays for the entire new cyclic row and its stack frame. -/
theorem constructor_dfs_measure_discover (vertices slots reached depth : Nat)
    (frames : List spanning_tree.Frame) (index push : Usize)
    (frame advanced child : spanning_tree.Frame)
    (hi : index.val + 1 = depth) (hp : push.val = depth)
    (hb : depth < frames.length) (hf : frames[index.val]? = some frame)
    (hpos : 0 < frame.remaining.val) (hr : advanced.remaining.val = frame.remaining.val - 1)
    (hchild : child.remaining.val ≤ slots) (hreached : reached < vertices) :
    constructorDFSMeasure vertices slots (reached + 1) (depth + 1)
      ((frames.set index.val advanced).set push.val child) <
      constructorDFSMeasure vertices slots reached depth frames := by
  have hib : index.val < frames.length := by omega
  unfold constructorDFSMeasure
  rw [hp, constructor_dfs_stack_fuel_top (frames.set index.val advanced) depth child
    (by simpa using hb), ← hi,
    constructor_dfs_stack_fuel_top frames index.val advanced hib,
    constructor_dfs_stack_fuel_last frames index.val frame hf, hr]
  have hsub : vertices - reached = vertices - (reached + 1) + 1 := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul]
  omega

end Labyrinth
