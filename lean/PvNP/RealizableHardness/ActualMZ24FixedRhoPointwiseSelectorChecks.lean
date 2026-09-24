import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector

namespace PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelectorChecks

open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
open PvNP.RealizableHardness.ActualMZ24D3c5Precomposition
open PvNP.RealizableHardness.ActualMZ24SourceCapGuards
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualFiniteLaw

#check manuscriptXi
#check fixedRho
#check fixedDeltaCount
#check Dof
#check Rof
#check fixedRho_pos
#check fixedRho_le_xi_div_4000
#check fixedRho_le_one_div_4000
#check thousand_mul_fixedRho_le_xi_div_four
#check fixedDeltaCount_eq
#check fixedRho_eq_inverse_bOf
#check Dof_eq_denominator_deltaCount
#check Rof_eq_ten_Dof
#check Rof_eq_ten_m_div_fixedRho
#check Rof_integral
#check two_le_Rof
#check bOf_dvd_hBlock_fixed
#check fixedRho_hBlock_integral
#check twice_complement_fixedRho_hBlock_integral
#check fixedRho_source_cap_guard_spec
#check fixedRhoHeightFloor
#check fixedRhoCutoff
#check fixedRho_selector_eventually_exists
#check fixedRho_selector_eventually_ge_256
#check fixedRho_selected_reserve
#check FixedRhoSelectedGuardBundle
#check fixedRho_selected_guard_bundle

-- Fixed-rho positivity and inverse/count identities are deliberately not
-- generalized to m=0, where rational division has a zero denominator.
example : fixedRho 0 = 0 := by norm_num [fixedRho]
example : fixedDeltaCount 0 = 0 := by norm_num [fixedDeltaCount, fixedRho]
example : ¬ 0 < fixedRho 0 := by norm_num [fixedRho]
example : ¬ (Dof 0 : Rat) * fixedDeltaCount 0 = 1 := by
  norm_num [Dof, fixedDeltaCount, fixedRho]
example : ¬ 2 ≤ Rof 0 := by norm_num [Rof, Dof]

-- The denominator is specific to rho=1/(4000 m^2).  A smaller rho fails
-- integrality even on the odd bOf-multiple h=bOf(1).
example : bOf 1 = 4000 := by norm_num [bOf]
example : ¬ ∃ n : Nat, (1 / (8000 : Rat)) * (4000 : Rat) = n := by
  rintro ⟨n, hn⟩
  have hnat : (1 : Nat) = 2 * n := by
    exact_mod_cast (show (1 : Rat) = 2 * (n : Rat) by norm_num at hn ⊢; linarith)
  omega

-- Negative arithmetic guard and the frozen positive reserve/cap fixture.
example : Ecap 1 1 1 1 = 47 := by norm_num [Ecap]
example : 50 * 1 * 1 * 1 + L6 1 1 1 1 0 = 2064 := by norm_num [L6, L5]
example : ¬ 50 * 1 * 1 * 1 + L6 1 1 1 1 0 ≤ Ecap 1 1 1 1 := by
  norm_num [Ecap, L6, L5]
example : 3*2 + 1000*(2+1)*1^5 + 1 + 5 ≤ 10*302 := by norm_num
example : 50*2*302*1^5 + L6 2 302 2 1 1 ≤ Ecap 1 2 2 302 := by
  norm_num [Ecap, L6, L5]

#print axioms fixedRho_hBlock_integral
#print axioms twice_complement_fixedRho_hBlock_integral
#print axioms Rof_eq_ten_m_div_fixedRho
#print axioms fixedRho_selector_eventually_ge_256
#print axioms fixedRho_selected_reserve
#print axioms fixedRho_selected_guard_bundle

end PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelectorChecks
