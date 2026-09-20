import PvNP.RealizableHardness.ActualCliqueJointLaw

namespace PvNP.RealizableHardness.ActualCliqueCollisionTransferChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

local instance checksLeafCliqueFintype {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Fintype (LeafClique I J h) :=
  Fintype.ofInjective (fun C : LeafClique I J h => C.1) Subtype.val_injective

local instance checksCliqueRepresentativeFintype {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m} (C : LeafClique I J h) :
    Fintype (CliqueRepresentative C) :=
  Fintype.ofInjective (fun v : CliqueRepresentative C => v.1) Subtype.val_injective

def emptyVs {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Fin 0 → LeafVertex I J h :=
  fun i => Fin.elim0 i

#check LabelTuple
#check IndependentChoice
#check DistinctCliques
#check CliqueCollision
#check uniformMean
#check independentLabels
#check selectedLabels
#check jointLaw_eq_of_distinctCliques

#print axioms jointLaw_eq_of_distinctCliques

example {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (vs : Fin k → LeafVertex I J h) :
    independentLabels T vs (fun i => s (cliqueOf (vs i))) =
      selectedLabels T s vs := by
  funext i
  unfold independentLabels selectedLabels selectedTable
  change transportedLeafLabel
      (cliqueOf_eq_iff.mp (s (cliqueOf (vs i))).property)
      (T (s (cliqueOf (vs i))).1) =
    transportedLeafLabel (representative_rel s (vs i))
      (T (s (cliqueOf (vs i))).1)
  have hrel :
      cliqueOf_eq_iff.mp (s (cliqueOf (vs i))).property =
        representative_rel s (vs i) :=
    Subsingleton.elim _ _
  rw [hrel]

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) :
    DistinctCliques (emptyVs (J := J) (h := h) I) := by
  intro i
  exact Fin.elim0 i

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h)
    (F : LabelTuple (emptyVs (J := J) (h := h) I) → ℚ) :
    uniformMean (RepresentativeChoice I J h)
        (fun s => F (selectedLabels T s (emptyVs (J := J) (h := h) I))) =
      uniformMean (IndependentChoice (emptyVs (J := J) (h := h) I))
        (fun r => F (independentLabels T (emptyVs (J := J) (h := h) I) r)) := by
  apply jointLaw_eq_of_distinctCliques T (emptyVs (J := J) (h := h) I)
  intro i
  exact Fin.elim0 i

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v : LeafVertex I J h) :
    DistinctCliques (fun _ : Fin 1 => v) := by
  intro i j hij
  fin_cases i
  fin_cases j
  rfl

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (v : LeafVertex I J h)
    (P : ∀ x : LeafVertex I J h, LeafLabel x → Prop) :
    uniformMean (RepresentativeChoice I J h)
        (fun s => if P v ((selectedLabels T s (fun _ : Fin 1 => v)) 0) then 1 else 0) =
      uniformMean (IndependentChoice (fun _ : Fin 1 => v))
        (fun r => if P v ((independentLabels T (fun _ : Fin 1 => v) r) 0) then 1 else 0) := by
  exact jointLaw_eq_of_distinctCliques T (fun _ : Fin 1 => v)
    (by
      intro i j hij
      fin_cases i
      fin_cases j
      rfl)
    (fun xs => if P v (xs 0) then 1 else 0)

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v w : LeafVertex I J h)
    (hvw : cliqueOf v ≠ cliqueOf w) :
    DistinctCliques (![v, w] : Fin 2 → LeafVertex I J h) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    apply hvw
    simpa using hij
  · exfalso
    apply hvw
    simpa using hij.symm
  · rfl

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (v w : LeafVertex I J h)
    (hvw : cliqueOf v ≠ cliqueOf w)
    (P : ∀ x : LeafVertex I J h, LeafLabel x → Prop) :
    uniformMean (RepresentativeChoice I J h)
        (fun s => if P ((![v, w] : Fin 2 → LeafVertex I J h) 0)
              ((selectedLabels T s (![v, w] : Fin 2 → LeafVertex I J h)) 0)
          then 1 else 0) =
      uniformMean (IndependentChoice (![v, w] : Fin 2 → LeafVertex I J h))
        (fun r => if P ((![v, w] : Fin 2 → LeafVertex I J h) 0)
              ((independentLabels T (![v, w] : Fin 2 → LeafVertex I J h) r) 0)
          then 1 else 0) := by
  exact jointLaw_eq_of_distinctCliques T (![v, w] : Fin 2 → LeafVertex I J h)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply hvw
        simpa using hij
      · exfalso
        apply hvw
        simpa using hij.symm
      · rfl)
    (fun xs => if P ((![v, w] : Fin 2 → LeafVertex I J h) 0) (xs 0) then 1 else 0)

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v : LeafVertex I J h) :
    CliqueCollision (![v, v] : Fin 2 → LeafVertex I J h) := by
  intro hdist
  have hbad : (0 : Fin 2) = 1 := hdist (by rfl)
  norm_num at hbad

end
end PvNP.RealizableHardness.ActualCliqueCollisionTransferChecks
