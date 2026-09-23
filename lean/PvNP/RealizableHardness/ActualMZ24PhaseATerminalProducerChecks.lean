import PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducer
import PvNP.RealizableHardness.ActualMZ24PhaseATypedStepChecks
import PvNP.RealizableHardness.ActualMZ24HyperplaneSupportChecks

namespace PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducerChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
open PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducer
open PvNP.RealizableHardness.ActualMZ24PhaseATypedStepChecks

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-! The autonomous `m=1` example terminates at the initial state.  The
manually supplied small successor from the typed-step checks remains a
separate residual-one stopping example. -/

noncomputable def autonomousLineTerminal :
    PhaseATerminal lineFamily3 advice3 2 1 1 :=
  phaseATerminalProducer lineFamily3 advice3
    (by intro i; rfl)
    lineFamily3_codim lineFamily3_injective
    (N := 1) (m := 1) (by norm_num)
    root3 (by norm_num)

private theorem autonomousLineTerminal_r : autonomousLineTerminal.r = 2 := by
  have hspec := phaseATerminalProducer_m_one_spec lineFamily3 advice3
    (by intro i; rfl) lineFamily3_codim lineFamily3_injective
    (N := 1) (m := 1) (by norm_num) root3 (by norm_num) rfl
  simpa [autonomousLineTerminal] using hspec.1

example : autonomousLineTerminal.s = 0 := by
  have hspec := phaseATerminalProducer_m_one_spec lineFamily3 advice3
    (by intro i; rfl) lineFamily3_codim lineFamily3_injective
    (N := 1) (m := 1) (by norm_num) root3 (by norm_num) rfl
  simpa [autonomousLineTerminal] using hspec.2.1

example : Module.finrank (ZMod 2) autonomousLineTerminal.E = 3 := by
  have h := PhaseATerminal.finrank_eq_sub_add lineFamily3 advice3
    autonomousLineTerminal lineFamily3_codim
  rw [autonomousLineTerminal_r] at h
  have hv : Module.finrank (ZMod 2) F2Three = 3 := by
    simp [F2Three, Module.finrank_pi]
  rw [hv] at h
  norm_num at h ⊢
  exact h

example : (PhaseAGeometry.QE lineFamily3 advice3
    autonomousLineTerminal.toPhaseAGeometry).val.map
      autonomousLineTerminal.E.subtype = advice3.val :=
  PhaseAGeometry.QE_map_recovery lineFamily3 advice3
    autonomousLineTerminal.toPhaseAGeometry

example (i : autonomousLineTerminal.Index) :
    (PhaseAGeometry.family lineFamily3 advice3
      autonomousLineTerminal.toPhaseAGeometry i).map
      autonomousLineTerminal.E.subtype = lineFamily3 i.1 :=
  PhaseAGeometry.family_map_recovery lineFamily3 advice3
    autonomousLineTerminal.toPhaseAGeometry i

example : autonomousLineTerminal.C.Nonempty :=
  autonomousLineTerminal.carrier_nonempty

example : 1 ≤ phaseABudget 2 * autonomousLineTerminal.C.card ^ 3 :=
  PhaseATerminal.phaseA_seed lineFamily3 advice3 autonomousLineTerminal root3

example : GenericUpToOn
    (PhaseAGeometry.family lineFamily3 advice3
      autonomousLineTerminal.toPhaseAGeometry)
    (Finset.univ : Finset autonomousLineTerminal.Index) 2
    autonomousLineTerminal.r :=
  PhaseATerminal.genericOn_univ lineFamily3 advice3 autonomousLineTerminal

/-! A two-index, distinct codimension-one family verifies that the terminal
output keeps both indices and exposes their pair genericity. -/

abbrev PairV := Fin 3 → ZMod 2
abbrev PairI := Fin 2

def pairCoordinateForm (j : Fin 3) : Module.Dual (ZMod 2) PairV :=
  LinearMap.proj j

def pairCoordinatePlane (j : Fin 3) : Submodule (ZMod 2) PairV :=
  LinearMap.ker (pairCoordinateForm j)

theorem pairCoordinateForm_ne_zero (j : Fin 3) : pairCoordinateForm j ≠ 0 := by
  intro h
  let ej : PairV := fun i => if i = j then 1 else 0
  have he : pairCoordinateForm j ej = 1 := by simp [pairCoordinateForm, ej]
  rw [h] at he
  simp at he

theorem pairCoordinatePlane_relativeCodim (j : Fin 3) :
    relativeCodim (pairCoordinatePlane j) = 1 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero
    (pairCoordinateForm_ne_zero j)
  unfold relativeCodim ActualMaximalPairLadder.codim pairCoordinatePlane at *
  have hV : Module.finrank (ZMod 2) PairV = 3 := by
    simp [PairV, Module.finrank_pi]
  omega

def pairFamily (i : PairI) : Submodule (ZMod 2) PairV :=
  pairCoordinatePlane (if i.val = 0 then 0 else 1)

theorem pairFamily_codim (i : PairI) :
    Module.finrank (ZMod 2) PairV - Module.finrank (ZMod 2) (pairFamily i) = 1 := by
  fin_cases i
  · change relativeCodim (pairCoordinatePlane (0 : Fin 3)) = 1
    exact pairCoordinatePlane_relativeCodim 0
  · change relativeCodim (pairCoordinatePlane (1 : Fin 3)) = 1
    exact pairCoordinatePlane_relativeCodim 1

theorem pairFamily_injective : Function.Injective pairFamily := by
  intro i j hij
  have hplane : pairCoordinatePlane (0 : Fin 3) ≠ pairCoordinatePlane 1 := by
    intro heq
    let e0 : PairV := fun k => if k = 0 then 1 else 0
    have he : e0 ∈ pairCoordinatePlane 1 := by
      simp [pairCoordinatePlane, pairCoordinateForm, e0]
    have hn : e0 ∉ pairCoordinatePlane 0 := by
      simp [pairCoordinatePlane, pairCoordinateForm, e0]
    exact hn (heq ▸ he)
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hplane (by simpa [pairFamily] using hij))
  · exact False.elim (hplane (by simpa [pairFamily] using hij.symm))
  · rfl

def pairAdvice : Grass PairV 0 := ⟨⊥, by simp⟩

theorem pairAdvice_le (i : PairI) : pairAdvice.val ≤ pairFamily i := bot_le

theorem pairIndexGuard : 2 ≤ Fintype.card PairI := by
  norm_num [PairI]

theorem pairCodimPos : 0 < (1 : Nat) := by
  norm_num

theorem pairRoot : IsPhaseARoot 2 1 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num [phaseABudget, phaseABaseExponent]
  · intro q hq hq1
    omega

noncomputable def pairState : PhaseAState pairFamily pairAdvice 1 2 1 :=
  initialPhaseAState pairFamily pairAdvice
    pairAdvice_le pairFamily_codim pairIndexGuard

noncomputable def pairStateFamily : pairState.Index →
    Submodule (ZMod 2) pairState.E :=
  PhaseAGeometry.family pairFamily pairAdvice pairState.toPhaseAGeometry

theorem pairStateFamily_relativeCodim (i : pairState.Index) :
    relativeCodim (pairStateFamily i) = 1 := by
  change relativeCodim
    (PhaseAGeometry.family pairFamily pairAdvice pairState.toPhaseAGeometry i) = 1
  rw [PhaseAState.family_relativeCodim pairFamily pairAdvice pairState
    pairFamily_codim i]
  norm_num [pairState, initialPhaseAState]

noncomputable def pairLarge : LargeTwoGenericBranch pairStateFamily 1 1 :=
  largeTwoGenericBranch_of_injective_relativeCodim_one pairStateFamily
    (PhaseAState.family_injective pairFamily pairAdvice pairState pairFamily_injective)
    pairStateFamily_relativeCodim 1 (by
      rw [PhaseAGeometry.index_card pairFamily pairAdvice pairState.toPhaseAGeometry]
      norm_num [pairState, initialPhaseAState])

noncomputable def pairSelectedCarrier : Finset pairState.Index :=
  Classical.choose pairLarge

theorem pairLarge_spec :
    pairSelectedCarrier = maximumCarrier pairStateFamily 1 ∧
      1 ≤ pairSelectedCarrier.card ∧
      TwoGenericOn pairStateFamily pairSelectedCarrier 1 ∧
      Function.Injective (ActualMZ24GenericSubfamilyStep.subtypeFamily
        pairStateFamily pairSelectedCarrier) ∧
      TwoGeneric (ActualMZ24GenericSubfamilyStep.subtypeFamily
        pairStateFamily pairSelectedCarrier) 1 :=
  Classical.choose_spec pairLarge

noncomputable def pairTerminal : PhaseATerminal pairFamily pairAdvice 1 2 1 :=
  terminalOfSelectedLarge pairFamily pairAdvice pairState (by norm_num)
    (by norm_num [pairState, initialPhaseAState]) pairSelectedCarrier
    pairLarge_spec.2.1 pairLarge_spec.2.2.2.2

theorem pairTerminal_card_two : pairTerminal.C.card = 2 := by
  have hmax := maximumCarrier_eq_univ_of_injective_relativeCodim_one
    pairStateFamily
    (PhaseAState.family_injective pairFamily pairAdvice pairState pairFamily_injective)
    pairStateFamily_relativeCodim
  have hidx : Fintype.card pairState.Index = 2 := by
    rw [PhaseAGeometry.index_card pairFamily pairAdvice pairState.toPhaseAGeometry]
    norm_num [pairState, initialPhaseAState]
  calc
    pairTerminal.C.card = pairSelectedCarrier.card := by
      simpa [pairTerminal] using
        (terminalOfSelectedLarge_card pairFamily pairAdvice pairState
          (by norm_num) (by norm_num [pairState, initialPhaseAState])
          pairSelectedCarrier pairLarge_spec.2.1 pairLarge_spec.2.2.2.2)
    _ = 2 := by
      calc
        pairSelectedCarrier.card =
            (Finset.univ : Finset pairState.Index).card :=
          congrArg Finset.card (pairLarge_spec.1.trans hmax)
        _ = 2 := by simpa using hidx

theorem pairTerminal_pair_generic (i j : pairTerminal.Index) (hij : i ≠ j) :
    Module.finrank (ZMod 2) pairTerminal.E -
      Module.finrank (ZMod 2)
        ((PhaseAGeometry.family pairFamily pairAdvice pairTerminal.toPhaseAGeometry i ⊓
          PhaseAGeometry.family pairFamily pairAdvice pairTerminal.toPhaseAGeometry j) :
            Submodule (ZMod 2) pairTerminal.E) =
        2 * pairTerminal.r := by
  exact genericUpTo_pair pairTerminal.generic_two (by norm_num) hij

/-! The autonomous producer output—not only the selected-carrier adapter—
retains both indices and their pair genericity. -/

noncomputable def pairAutonomousTerminal :
    PhaseATerminal pairFamily pairAdvice 1 2 1 :=
  phaseATerminalProducer pairFamily pairAdvice
    pairAdvice_le pairFamily_codim pairFamily_injective
    (N := 2) (m := 1) pairIndexGuard pairRoot pairCodimPos

theorem pairAutonomousTerminal_card_two :
    pairAutonomousTerminal.C.card = 2 := by
  have hspec := phaseATerminalProducer_m_one_spec pairFamily pairAdvice
    pairAdvice_le pairFamily_codim pairFamily_injective
    (N := 2) (m := 1) pairIndexGuard pairRoot pairCodimPos rfl
  let X0 : PhaseAState pairFamily pairAdvice 1 2 1 :=
    initialPhaseAState pairFamily pairAdvice pairAdvice_le pairFamily_codim pairIndexGuard
  let F0 : X0.Index → Submodule (ZMod 2) X0.E :=
    PhaseAGeometry.family pairFamily pairAdvice X0.toPhaseAGeometry
  have hF0codim : ∀ i : X0.Index, relativeCodim (F0 i) = 1 := by
    intro i
    change relativeCodim
      (PhaseAGeometry.family pairFamily pairAdvice X0.toPhaseAGeometry i) = 1
    rw [PhaseAState.family_relativeCodim pairFamily pairAdvice X0 pairFamily_codim i]
    norm_num [X0, initialPhaseAState]
  have hmax : maximumCarrier F0 1 = Finset.univ :=
    maximumCarrier_eq_univ_of_injective_relativeCodim_one F0
      (PhaseAState.family_injective pairFamily pairAdvice X0 pairFamily_injective)
      hF0codim
  have hcard : pairAutonomousTerminal.C.card = (maximumCarrier F0 1).card := by
    simpa only [pairAutonomousTerminal, X0, F0] using hspec.2.2
  rw [hmax, Finset.card_univ] at hcard
  have hidx : Fintype.card X0.Index = 2 := by
    rw [PhaseAGeometry.index_card pairFamily pairAdvice X0.toPhaseAGeometry]
    norm_num [X0, initialPhaseAState]
  simpa [hidx] using hcard

theorem pairAutonomousTerminal_carrier_eq_univ :
    pairAutonomousTerminal.C = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [pairAutonomousTerminal_card_two]
  simp [PairI]

theorem pairAutonomousTerminal_has_distinct_indices :
    ∃ i j : pairAutonomousTerminal.Index, i ≠ j := by
  let i : pairAutonomousTerminal.Index :=
    ⟨0, by rw [pairAutonomousTerminal_carrier_eq_univ]; simp⟩
  let j : pairAutonomousTerminal.Index :=
    ⟨1, by rw [pairAutonomousTerminal_carrier_eq_univ]; simp⟩
  have hij : i ≠ j := by
    intro heq
    have hv := congrArg Subtype.val heq
    norm_num [i, j] at hv
  exact ⟨i, j, hij⟩

theorem pairAutonomousTerminal_pair_generic
    (i j : pairAutonomousTerminal.Index) (hij : i ≠ j) :
    Module.finrank (ZMod 2) pairAutonomousTerminal.E -
      Module.finrank (ZMod 2)
        ((PhaseAGeometry.family pairFamily pairAdvice
          pairAutonomousTerminal.toPhaseAGeometry i ⊓
          PhaseAGeometry.family pairFamily pairAdvice
            pairAutonomousTerminal.toPhaseAGeometry j) :
          Submodule (ZMod 2) pairAutonomousTerminal.E) =
      2 * pairAutonomousTerminal.r :=
  genericUpTo_pair pairAutonomousTerminal.generic_two (by norm_num) hij

#print axioms phaseAAdvance
#print axioms phaseATerminalFromState
#print axioms phaseATerminalProducer
#print axioms phaseATerminalProducerOfCard
#print axioms autonomousLineTerminal
#print axioms pairTerminal
#print axioms pairAutonomousTerminal

#check terminalOfLargeBranch
#check codimOneTerminal
#check pairStateFamily
#check pairLarge
#check terminalOfSelectedLarge
#check terminalOfSelectedLarge_card
#check codimOneTerminalSelected
#check pairAutonomousTerminal_card_two
#check pairAutonomousTerminal_pair_generic

end
end PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducerChecks
