import PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
import Mathlib.Tactic

namespace PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducer

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
open PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24MaximalTwoGenericSubfamily

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

universe uV uI

variable {V : Type uV} {I : Type uI}
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]
variable {a0 c N m : Nat}
variable (W0 : I → Submodule (ZMod 2) V) (Q0 : Grass V a0)

namespace PhaseAGeometry

theorem index_card (X : PhaseAGeometry W0 Q0 c) :
    Fintype.card X.Index = X.C.card := by
  simp [PhaseAGeometry.Index]

end PhaseAGeometry

namespace PhaseAState

theorem root_le_index_card (X : PhaseAState W0 Q0 c N m)
    (hroot : IsPhaseARoot N c m) (hr : 0 < X.r) :
    m ≤ Fintype.card X.Index := by
  rw [PhaseAGeometry.index_card W0 Q0 X.toPhaseAGeometry]
  exact PhaseAState.root_le_card W0 Q0 X hroot hr

theorem family_injective (X : PhaseAState W0 Q0 c N m)
    (hinj : Function.Injective W0) :
    Function.Injective (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) :=
  PhaseAGeometry.family_injective W0 Q0 X.toPhaseAGeometry hinj

theorem family_relativeCodim (X : PhaseAState W0 Q0 c N m)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c) :
    ∀ i : X.Index,
      relativeCodim (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry i) = X.r := by
  intro i
  rw [relativeCodim_eq_finrank_sub]
  exact PhaseAGeometry.family_relativeCodim W0 Q0 X.toPhaseAGeometry hcodim i

end PhaseAState

inductive PhaseAAdvance (X : PhaseAState W0 Q0 c N m) : Type (max uV uI) where
  | terminalAtOne (T : PhaseATerminal W0 Q0 c N m)
      (residual_eq : X.r = 1)
      (terminal_card_eq_maximum : T.C.card =
        (maximumCarrier (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) X.r).card)
      (terminal_residual_eq : T.r = X.r)
      (terminal_stage_eq : T.s = X.s)
  | terminalAtMaximum (T : PhaseATerminal W0 Q0 c N m)
      (residual_ge_two : 2 ≤ X.r)
      (maximum_card_ge : m ≤
        (maximumCarrier (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) X.r).card)
      (terminal_card_eq_maximum : T.C.card =
        (maximumCarrier (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) X.r).card)
      (terminal_residual_eq : T.r = X.r)
      (terminal_stage_eq : T.s = X.s)
  | descend (Y : PhaseAState W0 Q0 c N m)
      (residual_ge_two : 2 ≤ X.r)
      (maximum_card_lt :
        (maximumCarrier (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) X.r).card < m)
      (m_ne_one : m ≠ 1)
      (residual_eq : Y.r = X.r - 1)
      (stage_eq : Y.s = X.s + 1)
      (residual_pos : 0 < Y.r)
      (residual_lt : Y.r < X.r)

/-! The accepted adapter remains available unchanged.  This selected-carrier
variant carries the same terminal geometry and genericity fields, but keeps
the chosen carrier as data so its cardinality bridge does not depend on
reducing the adapter's existential proof recursor. -/
noncomputable def terminalOfSelectedLarge
    (X : PhaseAState W0 Q0 c N m) (hm : 1 ≤ m) (hr : 0 < X.r)
    (S : Finset X.Index) (hmS : m ≤ S.card)
    (htwo : TwoGeneric
      (ActualMZ24GenericSubfamilyStep.subtypeFamily
        (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) S) X.r) :
    PhaseATerminal W0 Q0 c N m := by
  classical
  let C' := flattenCarrier X.C S
  let T : PhaseAGeometry W0 Q0 c :=
    ⟨X.E, C', X.s, X.r,
      (flattenCarrier_nonempty_iff X.C S).2 (by
        apply Finset.card_pos.mp
        have : 0 < S.card := lt_of_lt_of_le (by omega) hmS
        exact this),
      (by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact X.member_le j.1 j.2),
      X.advice_le, X.residual_add_stage, X.ambient_finrank_add_stage⟩
  let e := flattenCarrierEquiv X.C S
  have heq :
      ActualMZ24GenericSubfamilyStep.subtypeFamily
        (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) S =
        PhaseAGeometry.family W0 Q0 T ∘ e := by
    funext j
    have hval := flattenCarrierEquiv_original_value X.C S j
    change (W0 j.1.1).comap X.E.subtype =
      (W0 (e j).1).comap X.E.subtype
    rw [hval]
  have hgeneric : GenericUpTo (PhaseAGeometry.family W0 Q0 T) 2 X.r := by
    have h := genericUpTo_reindex
      (ActualMZ24GenericSubfamilyStep.subtypeFamily
        (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) S)
      e.symm e.symm.injective htwo
    rw [heq] at h
    have hcomp :
        ((PhaseAGeometry.family W0 Q0 T ∘ e) ∘ e.symm) =
          PhaseAGeometry.family W0 Q0 T := by
      funext i
      simp
    rw [hcomp] at h
    exact h
  have hflat : C'.card = S.card := flattenCarrier_card X.C S
  have hmC' : m ≤ C'.card := by rw [hflat]; exact hmS
  exact ⟨T, hr, hgeneric, hmC'⟩

theorem terminalOfSelectedLarge_card
    (X : PhaseAState W0 Q0 c N m) (hm : 1 ≤ m) (hr : 0 < X.r)
    (S : Finset X.Index) (hmS : m ≤ S.card)
    (htwo : TwoGeneric
      (ActualMZ24GenericSubfamilyStep.subtypeFamily
        (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) S) X.r) :
    (terminalOfSelectedLarge W0 Q0 X hm hr S hmS htwo).C.card = S.card := by
  change (flattenCarrier X.C S).card = S.card
  exact flattenCarrier_card X.C S

noncomputable def codimOneTerminalSelected
    (X : PhaseAState W0 Q0 c N m) (hm : 1 ≤ m) (hrone : X.r = 1)
    (S : Finset X.Index) (hmS : m ≤ S.card)
    (htwo : TwoGeneric
      (ActualMZ24GenericSubfamilyStep.subtypeFamily
        (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) S) X.r) :
    PhaseATerminal W0 Q0 c N m := by
  have hpos : 0 < X.r := by omega
  exact terminalOfSelectedLarge W0 Q0 X hm hpos S hmS htwo

noncomputable def phaseAAdvance
    (X : PhaseAState W0 Q0 c N m)
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0)
    (hroot : IsPhaseARoot N c m)
    (hr : 0 < X.r) :
    PhaseAAdvance W0 Q0 X := by
  classical
  let F : X.Index → Submodule (ZMod 2) X.E :=
    PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry
  let maxC := maximumCarrier F X.r
  have hmIndex : m ≤ Fintype.card X.Index :=
    PhaseAState.root_le_index_card W0 Q0 X hroot hr
  have hIndex : 0 < Fintype.card X.Index :=
    lt_of_lt_of_le hroot.1 hmIndex
  have hrelative : ∀ i : X.Index, relativeCodim (F i) = X.r :=
    PhaseAState.family_relativeCodim W0 Q0 X hcodim
  have hmaxNonempty : maxC.Nonempty :=
    maximumCarrier_nonempty_of_card_pos F X.r hrelative hIndex
  have hmaxCardPos : 0 < maxC.card := Finset.card_pos.mpr hmaxNonempty
  have hmaxTerminal (htwo : 2 ≤ X.r) (hmax : m ≤ maxC.card) :
      PhaseAAdvance W0 Q0 X := by
    let hlarge : LargeTwoGenericBranch F X.r m :=
      largeTwoGenericBranch_of_maximum F X.r m
        (PhaseAState.family_injective W0 Q0 X hinj) hmax
    let S : Finset X.Index := Classical.choose hlarge
    have hspec := Classical.choose_spec hlarge
    let T : PhaseATerminal W0 Q0 c N m :=
      terminalOfSelectedLarge W0 Q0 X hroot.1 hr S hspec.2.1
        hspec.2.2.2.2
    have hcard : T.C.card = maxC.card := by
      calc
        T.C.card = S.card :=
          terminalOfSelectedLarge_card W0 Q0 X hroot.1 hr S hspec.2.1
            hspec.2.2.2.2
        _ = maxC.card := congrArg Finset.card hspec.1
    have hTr : T.r = X.r := by simp [T, terminalOfSelectedLarge]
    have hTs : T.s = X.s := by simp [T, terminalOfSelectedLarge]
    exact .terminalAtMaximum T htwo hmax (by simpa [maxC, F] using hcard)
      hTr hTs
  by_cases hone : X.r = 1
  ·
    have hrelativeOne : ∀ i : X.Index, relativeCodim (F i) = 1 := by
      intro i
      rw [hrelative i, hone]
    have hlarge : LargeTwoGenericBranch F X.r m := by
      simpa [hone] using
        (largeTwoGenericBranch_of_injective_relativeCodim_one F
          (PhaseAState.family_injective W0 Q0 X hinj)
          (by intro i; exact hrelativeOne i) m hmIndex)
    let S : Finset X.Index := Classical.choose hlarge
    have hspec := Classical.choose_spec hlarge
    let T : PhaseATerminal W0 Q0 c N m :=
      codimOneTerminalSelected W0 Q0 X (Nat.succ_le_iff.mpr hroot.1)
        hone S hspec.2.1 hspec.2.2.2.2
    have hcard : T.C.card = maxC.card := by
      calc
        T.C.card = S.card :=
          terminalOfSelectedLarge_card W0 Q0 X (Nat.succ_le_iff.mpr hroot.1)
            hr S hspec.2.1 hspec.2.2.2.2
        _ = maxC.card := by simpa [S, maxC] using congrArg Finset.card hspec.1
    have hTr : T.r = X.r := by
      simp [T, codimOneTerminalSelected, terminalOfSelectedLarge]
    have hTs : T.s = X.s := by
      simp [T, codimOneTerminalSelected, terminalOfSelectedLarge]
    exact .terminalAtOne T hone (by simpa [maxC, F, hone] using hcard) hTr hTs
  · have htwo : 2 ≤ X.r := by omega
    by_cases hmone : m = 1
    · have hmax : m ≤ maxC.card := by
        calc
          m = 1 := hmone
          _ ≤ maxC.card := hmaxCardPos
      exact hmaxTerminal htwo hmax
    · by_cases hmax : m ≤ maxC.card
      · exact hmaxTerminal htwo hmax
      · have hsmall : maxC.card < m := by omega
        have hbranch : HyperplaneFibreBranch F X.r m :=
          hyperplaneFibreBranch_of_maximum F X.r m hrelative hr hIndex hsmall
            (PhaseAState.family_injective W0 Q0 X hinj)
        let B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m :=
          smallWitnessOfHyperplaneFibreBranch W0 Q0 X.toPhaseAGeometry m hbranch
        let Y : PhaseAState W0 Q0 c N m :=
          PhaseAState.smallSuccessor W0 Q0 X hQW htwo B
        have hy_r : Y.r = X.r - 1 :=
          PhaseAState.smallSuccessor_residual W0 Q0 X hQW htwo B
        have hy_s : Y.s = X.s + 1 :=
          PhaseAState.smallSuccessor_stage W0 Q0 X hQW htwo B
        have hy_pos : 0 < Y.r :=
          PhaseAState.smallSuccessor_residual_pos W0 Q0 X hQW htwo B
        have hy_lt : Y.r < X.r := by rw [hy_r]; omega
        exact .descend Y htwo (by simpa [maxC, F] using hsmall) hmone
          hy_r hy_s hy_pos hy_lt

theorem phaseAAdvance_m_one_no_descent
    (X : PhaseAState W0 Q0 c N m) (hroot : IsPhaseARoot N c m)
    (hadvance : PhaseAAdvance W0 Q0 X) (hm : m = 1) :
    match hadvance with
    | .terminalAtOne _ _ _ _ _ => True
    | .terminalAtMaximum _ _ _ _ _ _ => True
    | .descend _ _ _ hm_ne_one _ _ _ _ => False := by
  cases hadvance with
  | terminalAtOne => trivial
  | terminalAtMaximum => trivial
  | descend _ _ _ hm_ne_one _ _ _ _ => exact hm_ne_one hm

noncomputable def phaseATerminalFromState
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0)
    (hroot : IsPhaseARoot N c m)
    (X : PhaseAState W0 Q0 c N m)
    (hr : 0 < X.r) :
    PhaseATerminal W0 Q0 c N m := by
  classical
  exact match phaseAAdvance W0 Q0 X hQW hcodim hinj hroot hr with
  | .terminalAtOne T _ _ _ _ => T
  | .terminalAtMaximum T _ _ _ _ _ => T
  | .descend Y _ _ _ _ _ hYpos _ =>
      phaseATerminalFromState hQW hcodim hinj hroot Y hYpos
termination_by X.r
decreasing_by
  assumption

theorem phaseATerminalFromState_m_one_spec
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0)
    (hroot : IsPhaseARoot N c m)
    (X : PhaseAState W0 Q0 c N m) (hr : 0 < X.r)
    (hm : m = 1) :
    (phaseATerminalFromState W0 Q0 hQW hcodim hinj hroot X hr).r = X.r ∧
      (phaseATerminalFromState W0 Q0 hQW hcodim hinj hroot X hr).s = X.s ∧
      (phaseATerminalFromState W0 Q0 hQW hcodim hinj hroot X hr).C.card =
        (maximumCarrier (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry)
          X.r).card := by
  classical
  cases hstep : phaseAAdvance W0 Q0 X hQW hcodim hinj hroot hr with
  | terminalAtOne T hres hcard hTr hTs =>
      rw [phaseATerminalFromState]
      simp only [hstep]
      exact ⟨hTr, hTs, hcard⟩
  | terminalAtMaximum T htwo hmax hcard hTr hTs =>
      rw [phaseATerminalFromState]
      simp only [hstep]
      exact ⟨hTr, hTs, hcard⟩
  | descend Y htwo hsmall hmne hres hs hpos hlt =>
      exact False.elim (hmne hm)

noncomputable def phaseATerminalProducer
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0)
    [Nonempty I]
    (hN : N ≤ Fintype.card I)
    (hroot : IsPhaseARoot N c m)
    (hc : 0 < c) :
    PhaseATerminal W0 Q0 c N m := by
  let X : PhaseAState W0 Q0 c N m :=
    initialPhaseAState (m := m) W0 Q0 hQW hcodim hN
  have hspec := initialPhaseAState_spec (m := m) W0 Q0 hQW hcodim hN
  have hr : 0 < X.r := by
    rw [hspec.2.2.2]
    exact hc
  exact phaseATerminalFromState W0 Q0 hQW hcodim hinj hroot X hr

theorem phaseATerminalProducer_m_one_spec
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0)
    [Nonempty I]
    (hN : N ≤ Fintype.card I)
    (hroot : IsPhaseARoot N c m)
    (hc : 0 < c) (hm : m = 1) :
    (phaseATerminalProducer W0 Q0 hQW hcodim hinj hN hroot hc).r = c ∧
      (phaseATerminalProducer W0 Q0 hQW hcodim hinj hN hroot hc).s = 0 ∧
      (phaseATerminalProducer W0 Q0 hQW hcodim hinj hN hroot hc).C.card =
        (maximumCarrier
          (PhaseAGeometry.family W0 Q0
            (initialPhaseAState (m := m) W0 Q0 hQW hcodim hN).toPhaseAGeometry)
          c).card := by
  classical
  let X : PhaseAState W0 Q0 c N m :=
    initialPhaseAState (m := m) W0 Q0 hQW hcodim hN
  have hspec := initialPhaseAState_spec (m := m) W0 Q0 hQW hcodim hN
  have hr : 0 < X.r := by rw [hspec.2.2.2]; exact hc
  have hpres := phaseATerminalFromState_m_one_spec
    W0 Q0 hQW hcodim hinj hroot X hr hm
  simpa [phaseATerminalProducer, X, hspec.2.2.1, hspec.2.2.2] using hpres

noncomputable def phaseATerminalProducerOfCard
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0)
    [Nonempty I]
    (hc : 0 < c) :
    PhaseATerminal W0 Q0 c (Fintype.card I) (phaseARoot (Fintype.card I) c) :=
  phaseATerminalProducer W0 Q0 hQW hcodim hinj
    (N := Fintype.card I) (m := phaseARoot (Fintype.card I) c)
    (hN := le_rfl) (phaseARoot_spec (Fintype.card I) c) hc

end
end PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducer
