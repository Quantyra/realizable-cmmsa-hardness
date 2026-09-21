import PvNP.RealizableHardness.ActualQuestionCenterCollisionBound

namespace PvNP.RealizableHardness.ActualQuestionCenterCollisionBoundChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GaussianRatio
open PvNP.RealizableHardness.ActualQuestionCenterCollisionBound
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

local instance checksRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

#check IndexPair
#check DomainTuple
#check actualStarLeafVertices
#check domainTupleNonempty
#check domainTupleMean
#check pairCollisionMass
#check actualCliqueCollisionMass
#check actualCliqueCollisionMass_eq_collisionMass
#check drawPair_clique_eq_iff
#check pairCollisionMass_eq_card
#check pairCollisionMass_eq
#check cliqueGaussianRatio
#check normalizedFrame_pos
#check normalizedFrame_mono_ambient
#check gaussian_small_over_large_eq
#check gaussian_small_over_large_le
#check normalizedFrame_relative_mono
#check gaussian_reciprocal_le_shifted_ratio
#check pairCollisionMass_le_gaussianRatio
#check cliqueGaussianRatio_le_twoNegTwoJ
#check card_indexPair
#check cliqueCollision_iff_exists_indexPair
#check actualCliqueCollisionMass_le_pairSum
#check actualCliqueCollisionMass_le_choose_mul_ratio
#check choose_two_le_sq
#check choose_mul_twoNegTwoJ_le_twoNegJ
#check actualCliqueCollisionMass_le_twoNegJ

#print axioms pairCollisionMass_eq
#print axioms normalizedFrame_mono_ambient
#print axioms normalizedFrame_relative_mono
#print axioms gaussian_reciprocal_le_shifted_ratio
#print axioms pairCollisionMass_le_gaussianRatio
#print axioms cliqueGaussianRatio_le_twoNegTwoJ
#print axioms card_indexPair
#print axioms actualCliqueCollisionMass_le_pairSum
#print axioms actualCliqueCollisionMass_le_twoNegJ

example {N m J t k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) (p : IndexPair k) :
    pairCollisionMass q h ht hh p =
      1 / (gaussian (2*J - t) (2*h - t) : ℚ) :=
  pairCollisionMass_eq q ht hh p

def emptyQuestionCenter {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    QuestionCenter I 0 0 :=
  { U := ∅
    goodU := by simp [GoodQuestion]
    card_U := by simp
    K := ⊥
    K_le := by simp
    finrank_K := by simp
    transverse := by simp [questionEquationSpan] }

def emptyDomainDraw {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    DomainDraw (emptyQuestionCenter I) 0 :=
  { val := ⊥
    property := by
      simp [questionEquationSpan, equationSpan, emptyQuestionCenter,
        Submodule.span_empty] }

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    actualCliqueCollisionMass (emptyQuestionCenter I) 0 0 (by simp) (by simp) = 0 := by
  have hdist (draws : DomainTuple (emptyQuestionCenter I) 0 0) :
      DistinctCliques (actualStarLeafVertices (emptyQuestionCenter I) 0 draws) := by
    intro i j hij
    exact Fin.elim0 i
  have hzero (draws : DomainTuple (emptyQuestionCenter I) 0 0) :
      (if CliqueCollision (actualStarLeafVertices (emptyQuestionCenter I) 0 draws)
        then (1 : ℚ) else 0) = 0 := by
    simp [CliqueCollision, hdist draws]
  unfold actualCliqueCollisionMass domainTupleMean uniformMean
  rw [show
      (∑ draws : DomainTuple (emptyQuestionCenter I) 0 0,
        if CliqueCollision (actualStarLeafVertices (emptyQuestionCenter I) 0 draws)
        then (1 : ℚ) else 0) = 0 by
    apply Finset.sum_eq_zero
    intro draws hdraws
    exact hzero draws]
  simp

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    actualCliqueCollisionMass (emptyQuestionCenter I) 0 1 (by simp) (by simp) = 0 := by
  have hdist (draws : DomainTuple (emptyQuestionCenter I) 0 1) :
      DistinctCliques (actualStarLeafVertices (emptyQuestionCenter I) 0 draws) := by
    intro i j hij
    apply Fin.ext
    fin_cases i <;> fin_cases j <;> rfl
  have hzero (draws : DomainTuple (emptyQuestionCenter I) 0 1) :
      (if CliqueCollision (actualStarLeafVertices (emptyQuestionCenter I) 0 draws)
        then (1 : ℚ) else 0) = 0 := by
    simp [CliqueCollision, hdist draws]
  unfold actualCliqueCollisionMass domainTupleMean uniformMean
  rw [show
      (∑ draws : DomainTuple (emptyQuestionCenter I) 0 1,
        if CliqueCollision (actualStarLeafVertices (emptyQuestionCenter I) 0 draws)
        then (1 : ℚ) else 0) = 0 by
    apply Finset.sum_eq_zero
    intro draws hdraws
    exact hzero draws]
  simp

example : Fintype.card (IndexPair 0) = 0 := by
  simpa using card_indexPair 0

example : Fintype.card (IndexPair 1) = 0 := by
  simpa using card_indexPair 1

example : Fintype.card (IndexPair 2) = 1 := by
  simpa using card_indexPair 2

example : Fintype.card (IndexPair 3) = 3 := by
  simpa using card_indexPair 3

example : gaussian 4 2 = 35 := by
  norm_num [gaussian, frameProduct]

example : gaussian 6 2 = 651 := by
  norm_num [gaussian, frameProduct]

example : ((35 : ℚ) / 651) ≤ (1/2 : ℚ)^4 := by
  norm_num

example : cliqueGaussianRatio 4 2 1 ≤ (1/2 : ℚ)^8 := by
  exact cliqueGaussianRatio_le_twoNegTwoJ
    (J := 4) (h := 2) (t := 1) (by decide) (by decide) (by decide)

example :
    (Nat.choose 4 2 : ℚ) * (1/2 : ℚ)^(2*4) ≤ (1/2 : ℚ)^4 := by
  exact choose_mul_twoNegTwoJ_le_twoNegJ 4 4 (by decide)

example {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (draws : DomainTuple q h 2)
    (hdraw : draws 0 = draws 1) :
    CliqueCollision (actualStarLeafVertices q h draws) := by
  apply (cliqueCollision_iff_exists_indexPair q h draws).mpr
  refine ⟨⟨⟨0, 1⟩, by decide⟩, ?_⟩
  exact (drawPair_clique_eq_iff q h draws ⟨⟨0, 1⟩, by decide⟩).mpr hdraw

private theorem finTwo_eq_zero_or_one (i : Fin 2) :
    i = 0 ∨ i = 1 := by
  have hi : i.val ≤ 1 := by
    apply Nat.le_of_lt_succ
    simpa using i.isLt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with hi | hi
  · left
    exact Fin.ext hi
  · right
    exact Fin.ext hi

private theorem indexPair_two_coordinates (p : IndexPair 2) :
    p.1.1 = 0 ∧ p.1.2 = 1 := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  have hij' : i.val < j.val := hij
  rcases finTwo_eq_zero_or_one i with rfl | rfl
  · rcases finTwo_eq_zero_or_one j with rfl | rfl
    · exact (Nat.lt_irrefl 0 hij').elim
    · exact ⟨rfl, rfl⟩
  · rcases finTwo_eq_zero_or_one j with rfl | rfl
    · exact (Nat.not_lt_zero _ hij').elim
    · exact (Nat.lt_irrefl 1 hij').elim

example {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (draws : DomainTuple q h 2)
    (hdraw : draws 0 ≠ draws 1) :
    ¬ CliqueCollision (actualStarLeafVertices q h draws) := by
  intro hcoll
  obtain ⟨p, hp⟩ := (cliqueCollision_iff_exists_indexPair q h draws).mp hcoll
  have hpair := (drawPair_clique_eq_iff q h draws p).mp hp
  have hp01 := indexPair_two_coordinates p
  exact hdraw (by simpa [hp01.1, hp01.2] using hpair)

example {N m J t k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    [Nonempty (DomainTuple q h k)]
    (ht : t ≤ 2*h) (hh : h ≤ J) :
    actualCliqueCollisionMass q h k ht hh =
      collisionMass
        (fun draws : DomainTuple q h k => actualStarLeafVertices q h draws) :=
  actualCliqueCollisionMass_eq_collisionMass q h k ht hh

example {N m J t k h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (vs : (Fin k → LeafVertex I J h)) :
    CliqueCollision vs = ¬ DistinctCliques vs := rfl

end
end PvNP.RealizableHardness.ActualQuestionCenterCollisionBoundChecks
