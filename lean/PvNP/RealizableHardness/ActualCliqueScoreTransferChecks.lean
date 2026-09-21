import PvNP.RealizableHardness.ActualCliqueScoreTransfer

namespace PvNP.RealizableHardness.ActualCliqueScoreTransferChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer

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

#check originalScore
#check selectedScore
#check collisionMass
#check exists_selectedTable_score_ge_sub_collision

#print axioms exists_selectedTable_score_ge_sub_collision

def emptyVs {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Fin 1 → Fin 0 → LeafVertex I J h :=
  fun _ i => Fin.elim0 i

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) :
    collisionMass (emptyVs (J := J) (h := h) I) = 0 := by
  have hdist (ω : Fin 1) : DistinctCliques (emptyVs (J := J) (h := h) I ω) := by
    intro i j hij
    exact Fin.elim0 i
  simp [collisionMass, uniformMean, CliqueCollision, hdist]

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h)
    (accept : (ω : Fin 1) → LabelTuple (emptyVs (J := J) (h := h) I ω) → Prop) :
    ∃ s : RepresentativeChoice I J h,
      originalScore T (emptyVs (J := J) (h := h) I) accept -
          collisionMass (emptyVs (J := J) (h := h) I) ≤
        selectedScore T s (emptyVs (J := J) (h := h) I) accept := by
  exact exists_selectedTable_score_ge_sub_collision T
    (emptyVs (J := J) (h := h) I) accept

def duplicateVs {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v : LeafVertex I J h) : Fin 1 → Fin 2 → LeafVertex I J h :=
  fun _ => ![v, v]

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v : LeafVertex I J h) :
    collisionMass (duplicateVs v) = 1 := by
  have hcollision (ω : Fin 1) : CliqueCollision (duplicateVs v ω) := by
    intro hdist
    have hbad : (0 : Fin 2) = 1 := hdist (by rfl)
    norm_num at hbad
  simp [collisionMass, hcollision, uniformMean]

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (v : LeafVertex I J h)
    (accept : (ω : Fin 1) → LabelTuple (duplicateVs v ω) → Prop) :
    ∃ s : RepresentativeChoice I J h,
      originalScore T (duplicateVs v) accept - collisionMass (duplicateVs v) ≤
        selectedScore T s (duplicateVs v) accept := by
  exact exists_selectedTable_score_ge_sub_collision T (duplicateVs v) accept

def mixedVs {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (v w : LeafVertex I J h) : Fin 2 → Fin 2 → LeafVertex I J h :=
  ![![v, w], ![v, v]]

private theorem distinctPair {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    {v w : LeafVertex I J h} (hvw : cliqueOf v ≠ cliqueOf w) :
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

private theorem duplicateCollision {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    {v : LeafVertex I J h} :
    CliqueCollision (![v, v] : Fin 2 → LeafVertex I J h) := by
  intro hdist
  have hbad : (0 : Fin 2) = 1 := hdist (by rfl)
  norm_num at hbad

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    {v w : LeafVertex I J h} (hvw : cliqueOf v ≠ cliqueOf w) :
    collisionMass (mixedVs v w) = (1 : ℚ) / 2 := by
  have h0 : ¬ CliqueCollision (mixedVs v w 0) := by
    simpa [mixedVs, CliqueCollision] using distinctPair hvw
  have h1 : CliqueCollision (mixedVs v w 1) := by
    simpa [mixedVs] using (duplicateCollision (v := v))
  unfold collisionMass uniformMean
  rw [Fin.sum_univ_two]
  simp [h0, h1]

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h)
    {v w : LeafVertex I J h} (hvw : cliqueOf v ≠ cliqueOf w)
    (accept : (ω : Fin 2) → LabelTuple (mixedVs v w ω) → Prop) :
    ∃ s : RepresentativeChoice I J h,
      originalScore T (mixedVs v w) accept - collisionMass (mixedVs v w) ≤
        selectedScore T s (mixedVs v w) accept := by
  exact exists_selectedTable_score_ge_sub_collision T (mixedVs v w) accept

example {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (v : LeafVertex I J h)
    (accept : (ω : Fin 1) → LabelTuple (duplicateVs v ω) → Prop) :
    ∃ s : RepresentativeChoice I J h,
      originalScore T (duplicateVs v) (fun ω xs => True) -
          collisionMass (duplicateVs v) ≤
        selectedScore T s (duplicateVs v) (fun ω xs => True) := by
  exact exists_selectedTable_score_ge_sub_collision T (duplicateVs v)
    (fun _ _ => True)

end
end PvNP.RealizableHardness.ActualCliqueScoreTransferChecks
