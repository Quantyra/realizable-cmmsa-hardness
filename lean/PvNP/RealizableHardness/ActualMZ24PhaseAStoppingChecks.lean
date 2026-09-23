import PvNP.RealizableHardness.ActualMZ24PhaseAStopping
import PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamilyChecks
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks

/-! Boundary and force checks for the arithmetic Phase-A stopping layer. -/

namespace PvNP.RealizableHardness.ActualMZ24PhaseAStoppingChecks

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem phaseA_m_one_root_fixture : IsPhaseARoot 64 1 1 := by
  constructor
  · norm_num
  constructor
  · norm_num [phaseABudget, phaseABaseExponent]
  · intro q hq hq1
    omega

theorem phaseA_m_one_positive_survival_fixture :
    1 ≤ 64 := by
  exact phaseA_root_le_stage 64 1 1 0 64 phaseA_m_one_root_fixture
    (by norm_num) (by norm_num) (by norm_num [phaseALoss, phaseAResidualSum])

def phaseAOneTrace (_ : Nat) : Nat := 64

theorem phaseA_m_one_supplied_trace_fixture :
    1 ≤ phaseAOneTrace 0 := by
  apply phaseA_root_survives_small_trace phaseAOneTrace 1 1 0
  · simpa [phaseAOneTrace] using phaseA_m_one_root_fixture
  · norm_num
  · norm_num [phaseAOneTrace]
  · intro q hq
    omega

theorem phaseA_m_two_root_fixture : IsPhaseARoot 65 1 2 := by
  constructor
  · norm_num
  constructor
  · norm_num [phaseABudget, phaseABaseExponent]
  · intro q hq hq2
    have hq1 : q = 1 := by omega
    subst q
    norm_num [phaseABudget, phaseABaseExponent]

theorem phaseA_m_two_barrier_fixture :
    2 ^ (0 + 1) * 2 ^ phaseAResidualSum 1 0 ≤
      phaseABudget 1 * (2 - 1) ^ (1 + 1) :=
  phaseA_root_barrier 1 2 0 (by norm_num) (by norm_num)

theorem phaseA_m_two_predecessor_minimality_barrier_fixture :
    phaseABudget 1 * (2 - 1) ^ (1 + 1) < 65 ∧
      2 ^ (0 + 1) * 2 ^ phaseAResidualSum 1 0 ≤
        phaseABudget 1 * (2 - 1) ^ (1 + 1) := by
  exact ⟨phaseA_m_two_root_fixture.2.2 1 (by norm_num) (by norm_num),
    phaseA_m_two_barrier_fixture⟩

theorem phaseA_c3_s2_residual_fixture :
    phaseAResidualSum 3 2 = 3 + 2 := by
  norm_num [phaseAResidualSum, Finset.sum_range_succ]

theorem phaseA_terminal_residual_zero_fixture :
    phaseAResidualSum 3 3 = 3 + 2 + 1 ∧ 3 - 3 = 0 ∧ ¬ 3 < 3 := by
  norm_num [phaseAResidualSum, Finset.sum_range_succ]

abbrev StopV :=
  ActualMZ24HyperplaneSupportChecks.FixtureV

def codimOneFamily (_ : Fin 1) : Submodule (ZMod 2) StopV :=
  ActualMZ24HyperplaneSupportChecks.coordinateHyperplane

theorem codimOneFamily_injective : Function.Injective codimOneFamily := by
  intro i j hij
  exact Subsingleton.elim i j

theorem codimOneFamily_relativeCodim (i : Fin 1) :
    relativeCodim (codimOneFamily i) = 1 := by
  exact ActualMZ24HyperplaneSupportChecks.coordinateHyperplane_relativeCodim

theorem codimOne_stops_twoGeneric_fixture :
    TwoGeneric codimOneFamily 1 :=
  twoGeneric_of_injective_relativeCodim_one codimOneFamily
    codimOneFamily_injective codimOneFamily_relativeCodim

theorem codimOne_maximum_univ_fixture :
    maximumCarrier codimOneFamily 1 = Finset.univ :=
  maximumCarrier_eq_univ_of_injective_relativeCodim_one codimOneFamily
    codimOneFamily_injective codimOneFamily_relativeCodim

theorem codimOne_large_branch_fixture :
    LargeTwoGenericBranch codimOneFamily 1 1 := by
  exact largeTwoGenericBranch_of_injective_relativeCodim_one codimOneFamily
    codimOneFamily_injective codimOneFamily_relativeCodim 1 (by norm_num)

example : phaseAResidualSum 3 3 = 6 := by
  norm_num [phaseAResidualSum, Finset.sum_range_succ]

example : ¬ 3 < 3 := by omega

#check phaseABaseExponent
#check phaseABudget
#check phaseAResidualSum
#check phaseALoss
#check IsPhaseARoot
#check phaseARoot
#check phaseARoot_spec
#check phaseAResidualSum_succ
#check phaseAResidualSum_le_mul
#check phaseALoss_zero
#check phaseALoss_succ
#check phaseA_root_barrier
#check phaseA_accumulated_small
#check phaseA_root_le_stage
#check phaseA_root_survives_small_trace
#check phaseA_final_card_bound
#check phaseA_residual_pos
#check phaseA_last_residual
#check phaseA_no_zero_state
#check twoGeneric_of_injective_relativeCodim_one
#check maximumCarrier_eq_univ_of_injective_relativeCodim_one
#check largeTwoGenericBranch_of_injective_relativeCodim_one
#check phaseA_m_one_root_fixture
#check phaseA_m_one_positive_survival_fixture
#check phaseA_m_one_supplied_trace_fixture
#check phaseA_m_two_root_fixture
#check phaseA_m_two_barrier_fixture
#check phaseA_m_two_predecessor_minimality_barrier_fixture
#check phaseA_c3_s2_residual_fixture
#check phaseA_terminal_residual_zero_fixture
#check codimOne_stops_twoGeneric_fixture
#check codimOne_maximum_univ_fixture
#check codimOne_large_branch_fixture

#print axioms phaseARoot_spec
#print axioms phaseA_root_barrier
#print axioms phaseA_accumulated_small
#print axioms phaseA_root_le_stage
#print axioms phaseA_root_survives_small_trace
#print axioms phaseA_final_card_bound
#print axioms twoGeneric_of_injective_relativeCodim_one
#print axioms maximumCarrier_eq_univ_of_injective_relativeCodim_one
#print axioms largeTwoGenericBranch_of_injective_relativeCodim_one
#print axioms phaseA_m_one_root_fixture
#print axioms phaseA_m_one_positive_survival_fixture
#print axioms phaseA_m_one_supplied_trace_fixture
#print axioms phaseA_m_two_root_fixture
#print axioms phaseA_m_two_barrier_fixture
#print axioms phaseA_m_two_predecessor_minimality_barrier_fixture
#print axioms phaseA_c3_s2_residual_fixture
#print axioms phaseA_terminal_residual_zero_fixture
#print axioms codimOne_stops_twoGeneric_fixture
#print axioms codimOne_maximum_univ_fixture
#print axioms codimOne_large_branch_fixture

end
end PvNP.RealizableHardness.ActualMZ24PhaseAStoppingChecks
