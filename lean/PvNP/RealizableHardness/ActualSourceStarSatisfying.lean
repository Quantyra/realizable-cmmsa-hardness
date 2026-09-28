import PvNP.RealizableHardness.ActualSourceStarCompleteness

/-!
A satisfying assignment accepts every presented-leaf star.

If `x` has zero violations, its honest label respects every equation on
every presented leaf, so `starAccepts_honest` applies at every arity,
including `certifiedM`. This is the satisfiable side of the star test.

It does not bound acceptance mass on an unsatisfiable instance, does not
build a `SeededMap`, and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualSourceStarSatisfying

open ActualPresentedLeafGluing
open ActualOccurrenceAllocation
open Finite3LinSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

local instance rowIdDec {N m : Nat} (I : Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance globalVarDec {N m : Nat} (I : Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

theorem badRow_of_violations_eq_zero
    {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (S : Finite3LinSource Row Var) (x : Var → ZMod 2)
    (hx : S.violations x = 0) (q : Row) :
    S.badRow x q = false := by
  classical
  unfold Finite3LinSource.violations at hx
  have hnonneg : ∀ r ∈ Finset.univ, 0 ≤ (if S.badRow x r then 1 else 0) := by
    intro r _
    split_ifs <;> decide
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hx q (Finset.mem_univ q)
  cases hbad : S.badRow x q with
  | false => rfl
  | true => simp [hbad] at hzero

theorem starAccepts_of_zero_violations
    {N m J h n k : Nat} {I : Instance N m}
    (x : I.GlobalVar → ZMod 2)
    (hx : (ofActual I).violations x = 0)
    (Ps : Fin n → PresentedLeaf I J h)
    (Cs : ∀ i, CenterSubspace ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩ k)
    (hK : ∀ i j, (Cs i).K = (Cs j).K) :
    starAccepts
      (fun i => ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩)
      (fun i => ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩)
      (fun i => LeafVertex.Rel.refl _)
      Cs Cs (fun i => rfl)
      (fun i => honestPackaged (Ps i) x
        ((honestRawLabel_respects_iff (Ps i) x).mpr
          (fun e _ => badRow_of_violations_eq_zero (ofActual I) x hx e)))
      (fun i => honestPackaged (Ps i) x
        ((honestRawLabel_respects_iff (Ps i) x).mpr
          (fun e _ => badRow_of_violations_eq_zero (ofActual I) x hx e))) := by
  exact starAccepts_honest Ps x
    (fun i => (honestRawLabel_respects_iff (Ps i) x).mpr
      (fun e _ => badRow_of_violations_eq_zero (ofActual I) x hx e))
    Cs hK

end

end PvNP.RealizableHardness.ActualSourceStarSatisfying
