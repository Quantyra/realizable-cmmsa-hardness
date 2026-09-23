import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks
import Mathlib.Tactic

/-! Checks for the bounded two-branch generic-subfamily step.

The seven-line GF(2)^3 fixture supplies a genuine large case at m=1 and a
forced hyperplane-fibre case at m=2.  The payload checks expose the actual
hyperplane, common containment, restricted injectivity, and cover-first loss.
These checks cover only D3c4a: they do not prove restriction-preserved
TwoGeneric or construct D3c4b, D3c5, a decoder, the repeated game, or CMMSA.
-/

namespace PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStepChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

example : LargeTwoGenericBranch grassLineFamily 2 1 := by
  exact largeTwoGenericBranch_of_maximum grassLineFamily 2 1
    grassLineFamily_injective (by rw [grassLine_maximum_card])

theorem grassLine_forced_small :
    HyperplaneFibreBranch grassLineFamily 2 2 := by
  have hstep := genericSubfamilyStep grassLineFamily 2 2
    grassLineFamily_injective grassLine_relcodim (by norm_num)
    (by norm_num) (by rw [grassLine_card]; norm_num)
  rcases hstep with hlarge | hsmall
  · rcases hlarge with ⟨S, hSeq, hcard, hgeneric, hinj, hcanon⟩
    rw [hSeq, grassLine_maximum_card] at hcard
    omega
  · exact hsmall

example :
    LargeTwoGenericBranch grassLineFamily 2 1 ∨
      HyperplaneFibreBranch grassLineFamily 2 1 := by
  exact genericSubfamilyStep grassLineFamily 2 1
    grassLineFamily_injective grassLine_relcodim (by norm_num)
    (by norm_num) (by rw [grassLine_card]; norm_num)

example :
    ∃ z ∈ maximumHyperplaneCover grassLineFamily 2,
      (coverFibre grassLineFamily 2 z).Nonempty ∧
      Fintype.card GrassLine3 ≤
        (maximumHyperplaneCover grassLineFamily 2).card *
          (coverFibre grassLineFamily 2 z).card ∧
      Fintype.card GrassLine3 ≤
        (2 * 2 ^ 2) * Fintype.card (coverFibre grassLineFamily 2 z) := by
  rcases grassLine_forced_small with
    ⟨z, hz, hcontain, hne, hmax, hlt, hprod, hinj, hrest, hexact⟩
  exact ⟨z, hz, hne, hprod, hexact⟩

example :
    ∃ z : MaximumCoverIndex grassLineFamily 2,
      ∃ hcontain : ∀ i, i ∈ coverFibre grassLineFamily 2 z →
        grassLineFamily i ≤ z.2.1.1,
        Function.Injective (restrictedFibreFamily grassLineFamily 2 z hcontain) := by
  rcases grassLine_forced_small with
    ⟨z, hz, hcontain, hne, hmax, hlt, hprod, hinj, hrest, hexact⟩
  exact ⟨z, hcontain, hrest⟩

example : ∃ H : Hyperplane, ∃ z : MaximumCoverIndex grassLineFamily 2,
    H = z.2.1 := by
  rcases grassLine_forced_small with
    ⟨z, hz, hcontain, hne, hmax, hlt, hprod, hinj, hrest, hexact⟩
  exact ⟨z.2.1, z, rfl⟩

def oneEdgeAdj (x y : Fin 2) : Prop := x ≠ y

def oneEdgeNeighborhood (x : Fin 2) : Finset (Fin 2) := Finset.univ.erase x

def oneEdgeDegree (x : Fin 2) : Nat := (oneEdgeNeighborhood x).card

def oneEdgeIndependent (S : Finset (Fin 2)) : Prop :=
  ∀ ⦃x y : Fin 2⦄, x ∈ S → y ∈ S → oneEdgeAdj x y → x = y

def oneEdgeM : Nat := 2

theorem oneEdgeNeighborhood_mem_iff (x y : Fin 2) :
    y ∈ oneEdgeNeighborhood x ↔ oneEdgeAdj x y := by
  simp [oneEdgeNeighborhood, oneEdgeAdj, eq_comm]

theorem oneEdgeDegree_eq_one (x : Fin 2) : oneEdgeDegree x = 1 := by
  simp [oneEdgeDegree, oneEdgeNeighborhood]

theorem oneEdgeIndependent_card_le_one {S : Finset (Fin 2)}
    (hS : oneEdgeIndependent S) : S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  · exact hS hx hy (by simpa [oneEdgeAdj] using hxy)

theorem oneEdge_false_degree_kill :
    (∀ x : Fin 2, oneEdgeDegree x ≤ 2 / oneEdgeM) ∧
      ¬ ∃ S : Finset (Fin 2), oneEdgeIndependent S ∧ oneEdgeM ≤ S.card := by
  constructor
  · intro x
    rw [oneEdgeDegree_eq_one]
    norm_num [oneEdgeM]
  · rintro ⟨S, hS, hcard⟩
    have hle := oneEdgeIndependent_card_le_one hS
    norm_num [oneEdgeM] at hcard
    omega

#check subtypeFamily
#check subtypeFamily_injective
#check restrictedFibreFamily
#check restrictedFibreFamily_injective
#check LargeTwoGenericBranch
#check HyperplaneFibreBranch
#check largeTwoGenericBranch_of_maximum
#check hyperplaneFibreBranch_of_maximum
#check genericSubfamilyStep
#check grassLine_forced_small
#check oneEdgeAdj
#check oneEdgeNeighborhood
#check oneEdgeDegree
#check oneEdgeIndependent
#check oneEdgeM
#check oneEdgeNeighborhood_mem_iff
#check oneEdgeDegree_eq_one
#check oneEdgeIndependent_card_le_one
#check oneEdge_false_degree_kill

#print axioms subtypeFamily_injective
#print axioms restrictedFibreFamily_injective
#print axioms largeTwoGenericBranch_of_maximum
#print axioms hyperplaneFibreBranch_of_maximum
#print axioms genericSubfamilyStep
#print axioms grassLine_forced_small
#print axioms oneEdgeNeighborhood_mem_iff
#print axioms oneEdgeDegree_eq_one
#print axioms oneEdgeIndependent_card_le_one
#print axioms oneEdge_false_degree_kill

end
end PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStepChecks
