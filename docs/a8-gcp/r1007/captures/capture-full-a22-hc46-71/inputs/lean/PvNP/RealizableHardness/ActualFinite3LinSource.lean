import PvNP.RealizableHardness.ActualOccurrenceCounts
import Mathlib.Data.ZMod.Basic

namespace PvNP.RealizableHardness
open ActualOccurrenceAllocation
open scoped BigOperators
set_option autoImplicit false
noncomputable section

structure Finite3LinSource
    (Row Var : Type*) [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var] where
  row : Row → Fin 3 → Var
  rhs : Row → ZMod 2
  row_injective : ∀ q, Function.Injective (row q)

namespace Finite3LinSource
variable {Row Var : Type*} [Fintype Row] [Fintype Var]
  [DecidableEq Row] [DecidableEq Var]

def support (I : Finite3LinSource Row Var) (q : Row) : Finset Var :=
  Finset.univ.image (I.row q)

def badRow (I : Finite3LinSource Row Var)
    (x : Var → ZMod 2) (q : Row) : Bool :=
  decide (¬ (x (I.row q 0) + x (I.row q 1) + x (I.row q 2) = I.rhs q))

def violations (I : Finite3LinSource Row Var)
    (x : Var → ZMod 2) : Nat :=
  ∑ q : Row, if I.badRow x q then 1 else 0

theorem support_eq (I : Finite3LinSource Row Var) (q : Row) :
    I.support q = Finset.univ.image (I.row q) := rfl

end Finite3LinSource

theorem row_injective_of_support_card
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (row : Row → Fin 3 → Var) (support : Row → Finset Var)
    (hsupport : ∀ q, support q = Finset.univ.image (row q))
    (hcard : ∀ q, (support q).card = 3) :
    ∀ q, Function.Injective (row q) := by
  intro q i j hij
  have hc : (Finset.univ.image (row q)).card =
      (Finset.univ : Finset (Fin 3)).card := by
    rw [← hsupport q, hcard q, Finset.card_univ, Fintype.card_fin]
  exact (Finset.card_image_iff.mp hc) (Finset.mem_univ i) (Finset.mem_univ j) hij

namespace ActualOccurrenceAllocation.Instance
variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)

theorem rowId_card_eq_rows_length :
    Fintype.card I.RowId = I.rows.length := by
  classical
  rw [I.rows_eq_map, List.length_map,
    ← List.toFinset_card_of_nodup I.rowIndices_nodup,
    I.rowIndices_toFinset, Finset.card_univ]

end ActualOccurrenceAllocation.Instance

namespace Finite3LinSource

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

noncomputable def ofActual
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    Finite3LinSource I.RowId I.GlobalVar := by
  refine { row := I.row, rhs := I.rowRhs, row_injective := ?_ }
  apply row_injective_of_support_card I.row I.support I.support_eq I.support_card

theorem ofActual_row
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (q : I.RowId) (i : Fin 3) :
    (Finite3LinSource.ofActual I).row q i = I.row q i := rfl

theorem ofActual_support
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (q : I.RowId) :
    (Finite3LinSource.ofActual I).support q = I.support q := by
  change Finset.univ.image (I.row q) = I.support q
  exact (I.support_eq q).symm

theorem ofActual_rhs
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (q : I.RowId) :
    (Finite3LinSource.ofActual I).rhs q = I.rowRhs q := rfl

theorem ofActual_badRow
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) (q : I.RowId) :
    (Finite3LinSource.ofActual I).badRow x q =
      I.badRow x (I.row q, I.rowRhs q) := rfl

theorem ofActual_violations
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (x : I.GlobalVar → ZMod 2) :
    (Finite3LinSource.ofActual I).violations x = I.violations x := by
  rw [I.violations_eq_index_sum]
  rfl

end Finite3LinSource

end
end PvNP.RealizableHardness
