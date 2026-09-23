import PvNP.RealizableHardness.ActualMZ24D3c5Precomposition

namespace PvNP.RealizableHardness.ActualMZ24D3c5PrecompositionChecks

open PvNP.RealizableHardness.ActualMZ24D3c5Precomposition
open PvNP.RealizableHardness.ActualFiniteLaw

#check Ecap
#check L5
#check L6
#check Ecap_addback
#check L6_addback
#check height_pos
#check cap_sensitive_J_count
#check guarded_loss_ledger
#check complementCandidateEvent
#check complementCandidatePair_W_eq
#check complementCandidateEvent_mass_ge
#check complementAgreementCarrierEvent
#check complementCandidateEvent_subset_agreement

-- Negative guard fixture: at D=R=c=h=1 the cap exponent is only 47.
example : Ecap 1 1 1 1 = 47 := by norm_num [Ecap]
example : 50 * 1 * 1 * 1 + L6 1 1 1 1 0 = 2064 := by
  norm_num [L6, L5]
example : ¬ 50 * 1 * 1 * 1 + L6 1 1 1 1 0 ≤ Ecap 1 1 1 1 := by
  norm_num [Ecap, L6, L5]

-- Positive numerical reserve fixture; this checks only the frozen arithmetic.
example : 3*2 + 1000*(2+1)*1^5 + 1 + 5 ≤ 10*302 := by norm_num
example : 50*2*302*1^5 + L6 2 302 2 1 1 ≤ Ecap 1 2 2 302 := by
  norm_num [Ecap, L6, L5]

-- Two indexed tests can each succeed with mass one while disagreeing as
-- subsets; the event for one component has zero mass in the other.
example :
    eventMass (dirac (0 : Fin 2)) {0} = 1 ∧
    eventMass (dirac (1 : Fin 2)) {1} = 1 ∧
    eventMass (dirac (1 : Fin 2)) {0} = 0 ∧
    eventMass (dirac (0 : Fin 2)) {1} = 0 ∧
    ({0} : Finset (Fin 2)) ≠ {1} := by
  norm_num [eventMass, dirac]

#print axioms height_pos
#print axioms cap_sensitive_J_count
#print axioms guarded_loss_ledger
#print axioms Ecap_addback
#print axioms L6_addback
#print axioms complementCandidateEvent_mass_ge
#print axioms complementCandidatePair_W_eq
#print axioms complementCandidateEvent_subset_agreement

end PvNP.RealizableHardness.ActualMZ24D3c5PrecompositionChecks
