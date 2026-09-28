import PvNP.RealizableHardness.ActualSourceStarSatisfying

/-!
Checks for satisfying-assignment star acceptance. The examples call the
shipped theorems at an arbitrary arity. Axioms print after. This file
does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualSourceStarSatisfyingChecks

noncomputable section

open ActualSourceStarSatisfying
open ActualPresentedLeafGluing
open ActualOccurrenceAllocation
open Finite3LinSource

local instance rowIdDec {N m : Nat} (I : Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

local instance globalVarDec {N m : Nat} (I : Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

#check badRow_of_violations_eq_zero
#check starAccepts_of_zero_violations

example {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var]
    (S : Finite3LinSource Row Var) (x : Var → ZMod 2)
    (hx : S.violations x = 0) (q : Row) :
    S.badRow x q = false :=
  badRow_of_violations_eq_zero S x hx q

example {N m J h n k : Nat} {I : Instance N m}
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
          (fun e _ => badRow_of_violations_eq_zero (ofActual I) x hx e))) :=
  starAccepts_of_zero_violations x hx Ps Cs hK

#print axioms badRow_of_violations_eq_zero
#print axioms starAccepts_of_zero_violations

end

end PvNP.RealizableHardness.ActualSourceStarSatisfyingChecks
