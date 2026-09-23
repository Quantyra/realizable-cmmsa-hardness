import PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
import PvNP.RealizableHardness.ActualMZ24PhaseAStoppingChecks
import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCoverChecks

namespace PvNP.RealizableHardness.ActualMZ24PhaseATypedStepChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
open PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I] {a0 c N m : Nat}
variable (W0 : I → Submodule (ZMod 2) V) (Q0 : Grass V a0)

#check PhaseAGeometry
#check PhaseAGeometry.Index
#check PhaseAGeometry.indexEmbedding
#check PhaseAGeometry.family
#check PhaseAGeometry.QE
#check PhaseAGeometry.family_map_recovery
#check PhaseAGeometry.family_finrank
#check PhaseAGeometry.family_injective
#check PhaseAGeometry.QE_map_recovery
#check PhaseAGeometry.QE_le_family
#check PhaseAGeometry.family_relativeCodim
#check PhaseAGeometry.r_le_c
#check PhaseAGeometry.s_le_c
#check PhaseAGeometry.r_eq_c_sub_s
#check PhaseAGeometry.s_eq_c_sub_r
#check PhaseAGeometry.originalCodim_le_finrank
#check PhaseAGeometry.finrank_E_add_c_sub_r
#check PhaseAGeometry.finrank_eq_sub_add
#check PhaseAState
#check initialPhaseAState
#check initialPhaseAState_spec
#check PhaseAState.root_le_card
#check PhaseAState.smallSuccessor_E
#check PhaseAState.smallSuccessor_C
#check PhaseAState.smallSuccessor_stage
#check PhaseAState.smallSuccessor_residual
#check PhaseAState.smallSuccessor_card
#check PhaseAState.smallSuccessor_residual_pos
#check PhaseASmallWitness
#check smallWitnessOfHyperplaneFibreBranch
#check PhaseAState.smallSuccessor
#check PhaseATerminal
#check PhaseATerminal.family_injective
#check PhaseATerminal.phaseA_seed
#check PhaseATerminal.genericOn_univ
#check PhaseATerminal.universe_nonempty
#check PhaseATerminal.index_card
#check PhaseATerminal.c_le_ambient_finrank
#check PhaseATerminal.finrank_eq_sub_add
#check PhaseATerminal.phaseA_seed_univ
#check terminalOfLargeBranch
#check codimOneTerminal

/-! F₂²: one genuine guarded step from residual two to residual one. -/
abbrev F2Two := Fin 2 → ZMod 2
abbrev OneIndex := Fin 1

def zeroFamily2 (_ : OneIndex) : Submodule (ZMod 2) F2Two := ⊥

def zeroAdvice2 : Grass F2Two 0 := ⟨⊥, by simp⟩

theorem zeroFamily2_codim (i : OneIndex) :
    Module.finrank (ZMod 2) F2Two -
      Module.finrank (ZMod 2) (zeroFamily2 i) = 2 := by
  rw [zeroFamily2, finrank_bot]
  simp [F2Two, Module.finrank_pi]

noncomputable def phaseA2Initial :
    PhaseAState zeroFamily2 zeroAdvice2 2 1 1 :=
  initialPhaseAState zeroFamily2 zeroAdvice2
    (by intro i; exact bot_le) (by intro i; exact zeroFamily2_codim i)
    (by norm_num)

noncomputable def phaseA2Hyperplane :
    Hyperplane (V := phaseA2Initial.E) := by
  have hne : (⊥ : Submodule (ZMod 2) phaseA2Initial.E) ≠ ⊤ := by
    intro h
    have hdim := congrArg
      (fun W : Submodule (ZMod 2) phaseA2Initial.E => Module.finrank (ZMod 2) W) h
    have hE : Module.finrank (ZMod 2) phaseA2Initial.E = 2 := by
      have hstage := phaseA2Initial.ambient_finrank_add_stage
      have hs : phaseA2Initial.s = 0 := by
        norm_num [phaseA2Initial, initialPhaseAState]
      have hV : Module.finrank (ZMod 2) F2Two = 2 := by
        simp [F2Two, Module.finrank_pi]
      rw [hs, hV] at hstage
      omega
    rw [finrank_bot, finrank_top, hE] at hdim
    norm_num at hdim
  exact (Classical.choice
    (exists_hyperplane_containing_of_ne_top (V := phaseA2Initial.E)
      (W := (⊥ : Submodule (ZMod 2) phaseA2Initial.E)) hne)).1

def phaseA2Witness :
    PhaseASmallWitness zeroFamily2 zeroAdvice2 phaseA2Initial.toPhaseAGeometry 1 :=
  { H := phaseA2Hyperplane
    S := {⟨0, Finset.mem_univ 0⟩}
    nonempty := by simp
    contains := by
      intro i hi
      simpa [PhaseAGeometry.family,
        ActualMZ24PhaseARestrictionSupport.restrictFamily,
        ActualMZ24PhaseARestrictionSupport.restrictToAmbient, zeroFamily2] using
          (bot_le : (⊥ : Submodule (ZMod 2) phaseA2Initial.E) ≤ phaseA2Hyperplane.1)
    loss := by norm_num [phaseA2Initial, initialPhaseAState] }

noncomputable def phaseA2Successor :
    PhaseAState zeroFamily2 zeroAdvice2 2 1 1 :=
  PhaseAState.smallSuccessor zeroFamily2 zeroAdvice2 phaseA2Initial
    (by intro i; exact bot_le)
    (by norm_num [phaseA2Initial, initialPhaseAState]) phaseA2Witness

theorem phaseA2_successor_residual : phaseA2Successor.r = 1 := by
  norm_num [phaseA2Successor, PhaseAState.smallSuccessor,
    phaseA2Initial, initialPhaseAState]

theorem phaseA2_successor_nonempty : phaseA2Successor.C.Nonempty :=
  phaseA2Successor.carrier_nonempty

theorem phaseA2_successor_loss_card : phaseA2Successor.C.card = 1 := by
  simpa [phaseA2Successor, phaseA2Witness] using
    (PhaseAState.smallSuccessor_card zeroFamily2 zeroAdvice2 phaseA2Initial
      (by intro i; exact bot_le)
      (by norm_num [phaseA2Initial, initialPhaseAState]) phaseA2Witness)

theorem phaseA2_successor_residual_positive : 0 < phaseA2Successor.r :=
  PhaseAState.smallSuccessor_residual_pos zeroFamily2 zeroAdvice2 phaseA2Initial
    (by intro i; exact bot_le)
    (by norm_num [phaseA2Initial, initialPhaseAState]) phaseA2Witness

theorem residual_one_has_no_guard (X : PhaseAState W0 Q0 c N m)
    (hone : X.r = 1) : ¬ 2 ≤ X.r := by omega

/-! Codimension one reaches the separate terminal large-branch wrapper. -/
abbrev StopV := ActualMZ24HyperplaneSupportChecks.FixtureV

def stopAdvice : Grass StopV 0 := ⟨⊥, by simp⟩

theorem codimOneOriginalCodim (i : Fin 1) :
    Module.finrank (ZMod 2) StopV -
      Module.finrank (ZMod 2)
        (ActualMZ24PhaseAStoppingChecks.codimOneFamily i) = 1 := by
  simpa only [relativeCodim_eq_finrank_sub] using
    ActualMZ24PhaseAStoppingChecks.codimOneFamily_relativeCodim i

theorem rootOne : IsPhaseARoot 1 1 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num [phaseABudget, phaseABaseExponent]
  · intro q hq hq1
    omega

noncomputable def codimOneState :
    PhaseAState ActualMZ24PhaseAStoppingChecks.codimOneFamily stopAdvice 1 1 1 :=
  initialPhaseAState ActualMZ24PhaseAStoppingChecks.codimOneFamily stopAdvice
    (by intro i; exact bot_le)
    (by intro i; exact codimOneOriginalCodim i)
    (by norm_num)

noncomputable def codimOneTerminalFixture :
    PhaseATerminal ActualMZ24PhaseAStoppingChecks.codimOneFamily stopAdvice 1 1 1 :=
  codimOneTerminal ActualMZ24PhaseAStoppingChecks.codimOneFamily stopAdvice
    codimOneState (by norm_num) rootOne rfl
    codimOneOriginalCodim
    ActualMZ24PhaseAStoppingChecks.codimOneFamily_injective

example : codimOneTerminalFixture.r = 1 := by
  have hpos := codimOneTerminalFixture.residual_pos
  have hsum := codimOneTerminalFixture.residual_add_stage
  omega
example :
    GenericUpToOn
      (PhaseAGeometry.family ActualMZ24PhaseAStoppingChecks.codimOneFamily
        stopAdvice codimOneTerminalFixture.toPhaseAGeometry)
      (Finset.univ : Finset codimOneTerminalFixture.Index) 2
      codimOneTerminalFixture.r := by
  exact PhaseATerminal.genericOn_univ
    ActualMZ24PhaseAStoppingChecks.codimOneFamily stopAdvice codimOneTerminalFixture
example : 1 ≤ phaseABudget 1 *
    (Finset.univ : Finset codimOneTerminalFixture.Index).card ^ 2 :=
  PhaseATerminal.phaseA_seed_univ
    ActualMZ24PhaseAStoppingChecks.codimOneFamily stopAdvice
    codimOneTerminalFixture rootOne

/-! F₂³: a nonzero advice line and a retained line inside a plane. -/
abbrev F2Three := Fin 3 → ZMod 2

def e2 : F2Three := fun i => if i = 2 then 1 else 0

theorem e2_ne_zero : e2 ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [e2] at h2

def adviceLine3 : Submodule (ZMod 2) F2Three := (ZMod 2) ∙ e2

theorem adviceLine3_finrank :
    Module.finrank (ZMod 2) adviceLine3 = 1 :=
  finrank_span_singleton e2_ne_zero

def advice3 : Grass F2Three 1 := ⟨adviceLine3, adviceLine3_finrank⟩

theorem adviceLine3_le_coordinatePlane :
    adviceLine3 ≤
      ActualMZ24HyperplaneSupportChecks.coordinateHyperplane := by
  apply Submodule.span_le.mpr
  intro x hx
  have hx' : x = e2 := Set.mem_singleton_iff.mp hx
  subst x
  simp [ActualMZ24HyperplaneSupportChecks.coordinateHyperplane,
    ActualMZ24HyperplaneSupportChecks.coordinateForm, e2]

def lineFamily3 (_ : OneIndex) : Submodule (ZMod 2) F2Three := adviceLine3

theorem lineFamily3_injective : Function.Injective lineFamily3 := by
  intro i j hij
  exact Subsingleton.elim i j

theorem lineFamily3_codim (i : OneIndex) :
    Module.finrank (ZMod 2) F2Three -
      Module.finrank (ZMod 2) (lineFamily3 i) = 2 := by
  have hv : Module.finrank (ZMod 2) F2Three = 3 := by
    simp [F2Three, Module.finrank_pi]
  rw [lineFamily3, adviceLine3_finrank]
  omega

noncomputable def phaseA3Initial :
    PhaseAState lineFamily3 advice3 2 1 1 :=
  initialPhaseAState lineFamily3 advice3
    (by intro i; exact le_rfl) (by intro i; exact lineFamily3_codim i)
    (by norm_num)

def phaseA3Hyperplane : Hyperplane (V := phaseA3Initial.E) := by
  let E := phaseA3Initial.E
  let H := restrictToAmbient E
    ActualMZ24HyperplaneSupportChecks.coordinateHyperplane (by
      dsimp [E, phaseA3Initial, initialPhaseAState]
      exact le_top)
  refine ⟨H, ?_⟩
  unfold IsHyperplane
  dsimp only [H]
  rw [relativeCodim_eq_finrank_sub, restrictToAmbient_finrank]
  have hdim : Module.finrank (ZMod 2) F2Three = 3 := by
    simp [F2Three, Module.finrank_pi]
  have hE : Module.finrank (ZMod 2) E = 3 := by
    have hstage := phaseA3Initial.ambient_finrank_add_stage
    have hs : phaseA3Initial.s = 0 := by
      norm_num [phaseA3Initial, initialPhaseAState]
    rw [hs, hdim] at hstage
    change Module.finrank (ZMod 2) E = 3
    omega
  have hplane3 : 3 - Module.finrank (ZMod 2)
      ActualMZ24HyperplaneSupportChecks.coordinateHyperplane = 1 := by
    simpa only [relativeCodim_eq_finrank_sub, hdim] using
      ActualMZ24HyperplaneSupportChecks.coordinateHyperplane_relativeCodim
  rw [hE]
  exact hplane3

theorem phaseA3Family_le_plane (i : phaseA3Initial.Index) :
    PhaseAGeometry.family lineFamily3 advice3 phaseA3Initial.toPhaseAGeometry i ≤
      phaseA3Hyperplane.1 := by
  intro x hx
  unfold phaseA3Hyperplane
  change phaseA3Initial.E.subtype x ∈
    ActualMZ24HyperplaneSupportChecks.coordinateHyperplane
  apply adviceLine3_le_coordinatePlane
  change phaseA3Initial.E.subtype x ∈ adviceLine3 at hx
  exact hx

def phaseA3Witness :
    PhaseASmallWitness lineFamily3 advice3 phaseA3Initial.toPhaseAGeometry 1 :=
  { H := phaseA3Hyperplane
    S := {⟨(0 : OneIndex), Finset.mem_univ 0⟩}
    nonempty := by simp
    contains := by intro i hi; exact phaseA3Family_le_plane i
    loss := by norm_num [phaseA3Initial, initialPhaseAState] }

noncomputable def phaseA3Successor :
    PhaseAState lineFamily3 advice3 2 1 1 :=
  PhaseAState.smallSuccessor lineFamily3 advice3 phaseA3Initial
    (by intro i; exact le_rfl)
    (by norm_num [phaseA3Initial, initialPhaseAState]) phaseA3Witness

theorem phaseA3_advice_rank_preserved :
    Module.finrank (ZMod 2)
      (PhaseAGeometry.QE lineFamily3 advice3 phaseA3Successor.toPhaseAGeometry).val = 1 := by
  change Module.finrank (ZMod 2)
    (restrictToAmbient phaseA3Successor.E advice3.val phaseA3Successor.advice_le) = 1
  rw [restrictToAmbient_finrank]
  exact adviceLine3_finrank

theorem phaseA3_successor_residual : phaseA3Successor.r = 1 := by
  norm_num [phaseA3Successor, PhaseAState.smallSuccessor,
    phaseA3Initial, initialPhaseAState]

theorem root3 : IsPhaseARoot 1 2 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num [phaseABudget, phaseABaseExponent]
  · intro q hq hq1
    omega

noncomputable def phaseA3Terminal :
    PhaseATerminal lineFamily3 advice3 2 1 1 :=
  codimOneTerminal lineFamily3 advice3 phaseA3Successor (by norm_num) root3 rfl
    lineFamily3_codim lineFamily3_injective

theorem phaseA3_terminal_seed :
    1 ≤ phaseABudget 2 * phaseA3Terminal.C.card ^ 3 :=
  PhaseATerminal.phaseA_seed lineFamily3 advice3 phaseA3Terminal root3

theorem phaseA3_terminal_seed_univ :
    1 ≤ phaseABudget 2 *
      (Finset.univ : Finset phaseA3Terminal.Index).card ^ 3 :=
  PhaseATerminal.phaseA_seed_univ lineFamily3 advice3 phaseA3Terminal root3

theorem phaseA3_terminal_family_recovery (i : phaseA3Terminal.Index) :
    (PhaseAGeometry.family lineFamily3 advice3 phaseA3Terminal.toPhaseAGeometry i).map
      phaseA3Terminal.E.subtype = lineFamily3 i.1 :=
  PhaseAGeometry.family_map_recovery lineFamily3 advice3
    phaseA3Terminal.toPhaseAGeometry i

theorem phaseA3_terminal_finrank_identity :
    Module.finrank (ZMod 2) phaseA3Terminal.E =
      Module.finrank (ZMod 2) F2Three - 2 + phaseA3Terminal.r :=
  PhaseATerminal.finrank_eq_sub_add lineFamily3 advice3 phaseA3Terminal
    lineFamily3_codim

#print axioms PhaseAGeometry.family_map_recovery
#print axioms PhaseAGeometry.family_relativeCodim
#print axioms PhaseAState.smallSuccessor
#print axioms terminalOfLargeBranch
#print axioms PhaseATerminal.phaseA_seed

end
end PvNP.RealizableHardness.ActualMZ24PhaseATypedStepChecks
