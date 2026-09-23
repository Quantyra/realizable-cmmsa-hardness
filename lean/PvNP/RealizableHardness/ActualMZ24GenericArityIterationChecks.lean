import PvNP.RealizableHardness.ActualMZ24GenericArityIteration
import PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCountChecks

/-! Boundary and force checks for fixed-ambient generic-arity iteration. -/

namespace PvNP.RealizableHardness.ActualMZ24GenericArityIterationChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping
open PvNP.RealizableHardness.ActualMZ24GenericArityIteration
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamilyChecks
open PvNP.RealizableHardness.ActualMZ24IntersectionTaggedCountChecks

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {I : Type*} [Fintype I]

theorem t_two_zero_upgrades_fixture
    (W : I → Submodule (ZMod 2) V) (C : Finset I) (r c : Nat) :
    arityCarrier W C r (2 - 2) = C ∧
      arityExponent r c (2 - 2) = 0 := by
  simp [arityCarrier, arityExponent]

theorem t_three_exact_accumulated_exponent_fixture :
    phaseABaseExponent 1 + arityExponent 1 1 (3 - 2) = 10 := by
  norm_num [phaseABaseExponent, arityExponent, arityPower]

theorem t_three_public_budget_fixture :
    3 * 1 * ((1 + 1) * Nat.factorial (3 - 1)) = 12 := by
  norm_num

theorem t_four_factorial_tail_fixture : factorialTail 4 = 8 := by
  norm_num [factorialTail, Finset.sum_Ico_succ_top]

theorem t_four_factorial_tail_endpoint_fixture :
    3 + factorialTail 4 ≤ 3 * Nat.factorial (4 - 1) :=
  three_add_factorialTail_le 4 (by norm_num)

theorem empty_carrier_guard_fixture :
    ¬ (∅ : Finset (Fin 1)).Nonempty := by simp

theorem zero_residual_guard_fixture : ¬ 0 < (0 : Nat) := by omega

theorem threeLine_actual_iteration_fixture :
    threeLineCarrier.card ≤
      2 ^ (0 + arityExponent 1 1 1) *
        (arityCarrier threeLineFamily threeLineCarrier 1 1).card ^
          arityPower 1 1 := by
  apply arityCarrier_iterated_card_le threeLineFamily threeLineCarrier
    1 1 threeLineCarrier.card 0 1
  · norm_num
  · simp [threeLineCarrier]
  · exact threeLine_current_genericUpToOn
  · norm_num [threeLineCarrier]

theorem coordinate_actual_iteration_fixture :
    coordinateCarrier.card ≤
      2 ^ (0 + arityExponent 1 1 2) *
        (arityCarrier coordinateFamily coordinateCarrier 1 2).card ^
          arityPower 1 2 := by
  apply arityCarrier_iterated_card_le coordinateFamily coordinateCarrier
    1 1 coordinateCarrier.card 0 2
  · norm_num
  · simp [coordinateCarrier]
  · exact coordinateFamily_genericUpTo2
  · norm_num [coordinateCarrier]

theorem coordinate_subtype_closure_fixture :
    let J := arityCarrier coordinateFamily coordinateCarrier 1 (tD 0 - 2)
    J ⊆ coordinateCarrier ∧ J.Nonempty ∧
      GenericUpTo
        (ActualMZ24MaximalGenericSubfamily.carrierFamily coordinateFamily J)
        (tD 0) 1 ∧
      coordinateCarrier.card ≤
        2 ^ (3 * 1 * genericityPower 0 1) *
          J.card ^ genericityPower 0 1 := by
  apply fixedAmbient_tD_closure_subtype coordinateFamily coordinateCarrier
    0 1 1 coordinateCarrier.card
  · norm_num
  · norm_num
  · simp [coordinateCarrier]
  · exact coordinateFamily_genericUpTo2
  · norm_num [phaseABudget, phaseABaseExponent, coordinateCarrier]

#check arityCarrier
#check arityPower
#check arityExponent
#check factorialTail
#check arityCarrier_subset_previous
#check arityCarrier_subset_initial
#check arityCarrier_generic
#check arityCarrier_nonempty
#check arityCarrier_step_card_le
#check arityPower_eq
#check arityExponent_eq
#check arityCarrier_iterated_card_le
#check three_add_factorialTail_le
#check accumulated_exponent_le
#check two_le_tD
#check arityPower_tD
#check accumulated_exponent_tD_le
#check fixedAmbient_tD_closure
#check fixedAmbient_tD_closure_subtype
#check t_two_zero_upgrades_fixture
#check t_three_exact_accumulated_exponent_fixture
#check t_three_public_budget_fixture
#check t_four_factorial_tail_fixture
#check t_four_factorial_tail_endpoint_fixture
#check empty_carrier_guard_fixture
#check zero_residual_guard_fixture
#check threeLine_actual_iteration_fixture
#check coordinate_actual_iteration_fixture
#check coordinate_subtype_closure_fixture

#print axioms arityCarrier_generic
#print axioms arityCarrier_nonempty
#print axioms arityCarrier_step_card_le
#print axioms arityPower_eq
#print axioms arityExponent_eq
#print axioms arityCarrier_iterated_card_le
#print axioms three_add_factorialTail_le
#print axioms accumulated_exponent_le
#print axioms two_le_tD
#print axioms arityPower_tD
#print axioms accumulated_exponent_tD_le
#print axioms fixedAmbient_tD_closure
#print axioms fixedAmbient_tD_closure_subtype
#print axioms t_two_zero_upgrades_fixture
#print axioms t_three_exact_accumulated_exponent_fixture
#print axioms t_three_public_budget_fixture
#print axioms t_four_factorial_tail_fixture
#print axioms t_four_factorial_tail_endpoint_fixture
#print axioms empty_carrier_guard_fixture
#print axioms zero_residual_guard_fixture
#print axioms threeLine_actual_iteration_fixture
#print axioms coordinate_actual_iteration_fixture
#print axioms coordinate_subtype_closure_fixture

end
end PvNP.RealizableHardness.ActualMZ24GenericArityIterationChecks
