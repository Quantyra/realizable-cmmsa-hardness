import PvNP.RealizableHardness.ActualEdgeBlockStar

/-!
Checks for the arity-`certifiedM` Dinur edge-block mass.
The examples call the shipped theorems on an arbitrary 3CNF.
Axioms print after. This file does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualEdgeBlockStarChecks

open ActualEdgeBlockStar
open ActualDinurShrinkingCeiling
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open Complexity.SAT

#check edgeBlockArity
#check edgeBlockLen
#check edgeBlockAcceptanceMass
#check edgeBlockAcceptanceMass_eq_one_of_sat
#check edgeBlockAcceptanceMass_le_modified_pcp

example {φ : CNF} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) (L : Nat) :
    ∃ a : (manuscriptGap φ).Assignment, edgeBlockAcceptanceMass φ L a = 1 :=
  edgeBlockAcceptanceMass_eq_one_of_sat h3 hsat L

example {φ : CNF} (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (manuscriptGap φ).Assignment) :
    edgeBlockAcceptanceMass φ L a ≤
      ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ :=
  edgeBlockAcceptanceMass_le_modified_pcp h3 hunsat L a

#print axioms edgeBlockAcceptanceMass_eq_one_of_sat
#print axioms edgeBlockAcceptanceMass_le_modified_pcp

end PvNP.RealizableHardness.ActualEdgeBlockStarChecks
