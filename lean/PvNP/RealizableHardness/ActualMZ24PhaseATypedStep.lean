import PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
import PvNP.RealizableHardness.ActualMZ24PhaseAStopping
import PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
import Mathlib.Tactic

/-! One guarded, typed Phase-A restriction step and a terminal large-branch adapter.
    This increment is nonrecursive and chooses no advice complement. -/

namespace PvNP.RealizableHardness.ActualMZ24PhaseATypedStep

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyStep
open PvNP.RealizableHardness.ActualMZ24MaximalGenericSubfamily
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyCover
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMaximalPairLadder

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]
variable {a0 c N m : Nat}
variable (W0 : I → Submodule (ZMod 2) V) (Q0 : Grass V a0)

structure PhaseAGeometry (c : Nat) where
  E : Submodule (ZMod 2) V
  C : Finset I
  s : Nat
  r : Nat
  carrier_nonempty : C.Nonempty
  member_le : ∀ i, i ∈ C → W0 i ≤ E
  advice_le : Q0.val ≤ E
  residual_add_stage : r + s = c
  ambient_finrank_add_stage :
    Module.finrank (ZMod 2) E + s = Module.finrank (ZMod 2) V

namespace PhaseAGeometry

variable (X : PhaseAGeometry W0 Q0 c)

abbrev Index := {i : I // i ∈ X.C}

def indexEmbedding : X.Index ↪ I := originalIndexEmbedding X.C

def family : X.Index → Submodule (ZMod 2) X.E :=
  ActualMZ24PhaseARestrictionSupport.restrictFamily X.E
    (fun i : X.Index => W0 i.1) (fun i => X.member_le i.1 i.2)

def QE : Grass X.E a0 :=
  restrictGrass X.E Q0 X.advice_le

theorem family_map_recovery (i : X.Index) :
    (PhaseAGeometry.family W0 Q0 X i).map X.E.subtype = W0 i.1 :=
  ActualMZ24PhaseARestrictionSupport.restrictFamily_map_recovery X.E
    (fun j : X.Index => W0 j.1) (fun j => X.member_le j.1 j.2) i

theorem family_finrank (i : X.Index) :
    Module.finrank (ZMod 2) (PhaseAGeometry.family W0 Q0 X i) =
      Module.finrank (ZMod 2) (W0 i.1) :=
  ActualMZ24PhaseARestrictionSupport.restrictFamily_finrank X.E
    (fun j : X.Index => W0 j.1) (fun j => X.member_le j.1 j.2) i

theorem family_injective (hinj : Function.Injective W0) :
    Function.Injective (PhaseAGeometry.family W0 Q0 X) := by
  have hindex : Function.Injective (fun i : X.Index => W0 i.1) := by
    intro i j hij
    apply Subtype.ext
    exact hinj hij
  exact ActualMZ24PhaseARestrictionSupport.restrictFamily_injective X.E
    (fun j : X.Index => W0 j.1) (fun j => X.member_le j.1 j.2) hindex

theorem QE_map_recovery : (PhaseAGeometry.QE W0 Q0 X).val.map X.E.subtype = Q0.val :=
  restrictGrass_map_recovery X.E Q0 X.advice_le

theorem QE_le_family (hQW : ∀ i, Q0.val ≤ W0 i) (i : X.Index) :
    (PhaseAGeometry.QE W0 Q0 X).val ≤ PhaseAGeometry.family W0 Q0 X i := by
  intro x hx
  exact hQW i.1 hx

theorem family_relativeCodim
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c) (i : X.Index) :
    Module.finrank (ZMod 2) X.E -
      Module.finrank (ZMod 2) (PhaseAGeometry.family W0 Q0 X i) = X.r := by
  have hc := hcodim i.1
  have hle : Module.finrank (ZMod 2) (W0 i.1) ≤
      Module.finrank (ZMod 2) X.E :=
    Submodule.finrank_mono (X.member_le i.1 i.2)
  rw [PhaseAGeometry.family_finrank W0 Q0 X i]
  have hstage := X.residual_add_stage
  have hdim := X.ambient_finrank_add_stage
  omega

theorem r_le_c : X.r ≤ c := by
  have h := X.residual_add_stage
  omega

theorem s_le_c : X.s ≤ c := by
  have h := X.residual_add_stage
  omega

theorem r_eq_c_sub_s : X.r = c - X.s := by
  have h := X.residual_add_stage
  omega

theorem s_eq_c_sub_r : X.s = c - X.r := by
  have h := X.residual_add_stage
  omega

include X in
theorem originalCodim_le_finrank
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c) :
    c ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨i, hi⟩ := X.carrier_nonempty
  have h := hcodim i
  omega

theorem finrank_E_add_c_sub_r :
    Module.finrank (ZMod 2) X.E + (c - X.r) =
      Module.finrank (ZMod 2) V := by
  have h := X.residual_add_stage
  have hdim := X.ambient_finrank_add_stage
  omega

theorem finrank_eq_sub_add
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c) :
  Module.finrank (ZMod 2) X.E =
      Module.finrank (ZMod 2) V - c + X.r := by
  have hc := PhaseAGeometry.originalCodim_le_finrank W0 Q0 X hcodim
  have hdim := PhaseAGeometry.finrank_E_add_c_sub_r W0 Q0 X
  have hrc := PhaseAGeometry.r_le_c W0 Q0 X
  omega

theorem original_member_le_nested
    (H : Hyperplane (V := X.E)) (i : X.Index)
    (hfamily : PhaseAGeometry.family W0 Q0 X i ≤ H.1) :
    W0 i.1 ≤ nestedAmbient X.E H := by
  intro x hx
  let xE : X.E := ⟨x, X.member_le i.1 i.2 hx⟩
  have hxE : X.E.subtype xE ∈ W0 i.1 := by simpa [xE] using hx
  let y : PhaseAGeometry.family W0 Q0 X i := ⟨xE, hxE⟩
  have hy : (y.1 : X.E) ∈ H.1 := hfamily y.2
  change x ∈ H.1.map X.E.subtype
  exact ⟨y.1, hy, rfl⟩

end PhaseAGeometry

structure PhaseASmallWitness (X : PhaseAGeometry W0 Q0 c) (m : Nat) where
  H : Hyperplane (V := X.E)
  S : Finset X.Index
  nonempty : S.Nonempty
  contains : ∀ i, i ∈ S → PhaseAGeometry.family W0 Q0 X i ≤ H.1
  loss : X.C.card ≤ (m * 2 ^ X.r) * S.card

structure PhaseAState (c N m : Nat) extends PhaseAGeometry W0 Q0 c where
  accumulated : N ≤ phaseALoss c m s * C.card

namespace PhaseAState

variable (X : PhaseAState W0 Q0 c N m)

theorem root_le_card (hroot : IsPhaseARoot N c m) (hr : 0 < X.r) :
    m ≤ X.C.card := by
  apply phaseA_root_le_stage N c m X.s X.C.card hroot
  · have := X.residual_add_stage
    omega
  · exact Finset.card_pos.mpr X.carrier_nonempty
  · exact X.accumulated

noncomputable def smallSuccessor
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    PhaseAState W0 Q0 c N m := by
  let E' := nestedAmbient X.E B.H
  let C' := flattenCarrier X.C B.S
  have hCne : C'.Nonempty :=
    (flattenCarrier_nonempty_iff X.C B.S).2 B.nonempty
  have hmember : ∀ i, i ∈ C' → W0 i ≤ E' := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact PhaseAGeometry.original_member_le_nested W0 Q0 X.toPhaseAGeometry
      B.H j (B.contains j hj)
  have hQ : Q0.val ≤ E' := by
    obtain ⟨j, hj⟩ := B.nonempty
    exact (hQW j.1).trans
      (PhaseAGeometry.original_member_le_nested W0 Q0 X.toPhaseAGeometry
        B.H j (B.contains j hj))
  have hstage := X.residual_add_stage
  have hres : X.r - 1 + (X.s + 1) = c := by omega
  have hdim : Module.finrank (ZMod 2) E' + (X.s + 1) =
      Module.finrank (ZMod 2) V := by
    dsimp [E']
    have h := X.ambient_finrank_add_stage
    have hh := nestedAmbient_finrank_add_one X.E B.H
    omega
  have hstep : X.s < c := by
    have := X.residual_add_stage
    omega
  have hacc : N ≤ phaseALoss c m (X.s + 1) * C'.card := by
    have hfactor : m * 2 ^ (c - X.s) = m * 2 ^ X.r := by
      have hpow : c - X.s = X.r := by
        have h := X.residual_add_stage
        omega
      rw [hpow]
    have hcard := flattenCarrier_card X.C B.S
    have hloss : X.C.card ≤
        (m * 2 ^ (c - X.s)) * B.S.card := by
      rw [hfactor]
      exact B.loss
    rw [phaseALoss_succ c m X.s hstep, hcard]
    calc
      N ≤ phaseALoss c m X.s * X.C.card := X.accumulated
      _ ≤ phaseALoss c m X.s *
          ((m * 2 ^ (c - X.s)) * B.S.card) :=
        Nat.mul_le_mul_left _ hloss
      _ = phaseALoss c m X.s * (m * 2 ^ (c - X.s)) * B.S.card := by ring
  refine ⟨⟨E', C', X.s + 1, X.r - 1, hCne, hmember, hQ, hres, hdim⟩, hacc⟩

theorem smallSuccessor_E
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    (PhaseAState.smallSuccessor W0 Q0 X hQW hr B).E = nestedAmbient X.E B.H := rfl

theorem smallSuccessor_C
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    (PhaseAState.smallSuccessor W0 Q0 X hQW hr B).C = flattenCarrier X.C B.S := rfl

theorem smallSuccessor_stage
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    (PhaseAState.smallSuccessor W0 Q0 X hQW hr B).s = X.s + 1 := rfl

theorem smallSuccessor_residual
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    (PhaseAState.smallSuccessor W0 Q0 X hQW hr B).r = X.r - 1 := rfl

theorem smallSuccessor_card
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    (PhaseAState.smallSuccessor W0 Q0 X hQW hr B).C.card = B.S.card := by
  rw [PhaseAState.smallSuccessor_C W0 Q0 X hQW hr B, flattenCarrier_card]

theorem smallSuccessor_residual_pos
    (hQW : ∀ i, Q0.val ≤ W0 i) (hr : 2 ≤ X.r)
    (B : PhaseASmallWitness W0 Q0 X.toPhaseAGeometry m) :
    0 < (PhaseAState.smallSuccessor W0 Q0 X hQW hr B).r := by
  rw [PhaseAState.smallSuccessor_residual W0 Q0 X hQW hr B]
  omega

end PhaseAState

noncomputable def initialPhaseAState
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    [Nonempty I] (hN : N ≤ Fintype.card I) :
    PhaseAState W0 Q0 c N m := by
  let E := (⊤ : Submodule (ZMod 2) V)
  let C := (Finset.univ : Finset I)
  have hne : C.Nonempty := Finset.univ_nonempty
  have hdim : Module.finrank (ZMod 2) E + 0 = Module.finrank (ZMod 2) V := by
    simp [E]
  have hacc : N ≤ phaseALoss c m 0 * C.card := by
    rw [phaseALoss_zero]
    simpa [C] using hN
  exact ⟨⟨E, C, 0, c, hne, (by intro i hi; exact le_top), le_top,
    by omega, hdim⟩, hacc⟩

theorem initialPhaseAState_spec
    (hQW : ∀ i, Q0.val ≤ W0 i)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    [Nonempty I] (hN : N ≤ Fintype.card I) :
    (initialPhaseAState (m := m) W0 Q0 hQW hcodim hN).E = ⊤ ∧
    (initialPhaseAState (m := m) W0 Q0 hQW hcodim hN).C = Finset.univ ∧
    (initialPhaseAState (m := m) W0 Q0 hQW hcodim hN).s = 0 ∧
    (initialPhaseAState (m := m) W0 Q0 hQW hcodim hN).r = c := by
  exact ⟨rfl, rfl, rfl, rfl⟩

noncomputable def smallWitnessOfHyperplaneFibreBranch
    (X : PhaseAGeometry W0 Q0 c) (m : Nat)
    (h : HyperplaneFibreBranch (PhaseAGeometry.family W0 Q0 X) X.r m) :
    PhaseASmallWitness W0 Q0 X m := by
  let z : MaximumCoverIndex (PhaseAGeometry.family W0 Q0 X) X.r :=
    Classical.choose h
  have hzspec := Classical.choose_spec h
  have hz : z ∈ maximumHyperplaneCover (PhaseAGeometry.family W0 Q0 X) X.r :=
    hzspec.1
  let hcontain : ∀ i, i ∈ coverFibre (PhaseAGeometry.family W0 Q0 X) X.r z →
      (PhaseAGeometry.family W0 Q0 X) i ≤ z.2.1.1 :=
    Classical.choose hzspec.2
  have hcspec := Classical.choose_spec hzspec.2
  have hne := hcspec.1
  have hloss := hcspec.2.2.2.2.2.2
  refine ⟨z.2.1, coverFibre (PhaseAGeometry.family W0 Q0 X) X.r z, hne, ?_, ?_⟩
  · intro i hi
    exact (coverFibre_mem_iff (PhaseAGeometry.family W0 Q0 X) X.r z i).mp hi
  · simpa only [z, Fintype.card_coe] using hloss

structure PhaseATerminal (c N m : Nat)
    extends toPhaseAGeometry : PhaseAGeometry W0 Q0 c where
  residual_pos : 0 < r
  generic_two :
    GenericUpTo (PhaseAGeometry.family W0 Q0 toPhaseAGeometry) 2 r
  root_le_card : m ≤ C.card

namespace PhaseATerminal

variable (T : PhaseATerminal W0 Q0 c N m)

theorem index_card : Fintype.card T.Index = T.C.card := by
  simp [PhaseAGeometry.Index]

include T in
theorem c_le_ambient_finrank
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c) :
    c ≤ Module.finrank (ZMod 2) V :=
  PhaseAGeometry.originalCodim_le_finrank W0 Q0 T.toPhaseAGeometry hcodim

theorem finrank_eq_sub_add
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c) :
    Module.finrank (ZMod 2) T.E =
      Module.finrank (ZMod 2) V - c + T.r :=
  PhaseAGeometry.finrank_eq_sub_add W0 Q0 T.toPhaseAGeometry hcodim

theorem family_injective :
    Function.Injective (PhaseAGeometry.family W0 Q0 T.toPhaseAGeometry) := by
  intro i j hij
  by_contra hne
  have hpair := genericUpTo_pair T.generic_two (by norm_num) hne
  have hsingle := genericUpTo_singleton T.generic_two (by norm_num) i
  have hinter : PhaseAGeometry.family W0 Q0 T.toPhaseAGeometry i ⊓
      PhaseAGeometry.family W0 Q0 T.toPhaseAGeometry j =
      PhaseAGeometry.family W0 Q0 T.toPhaseAGeometry i := by
    rw [hij, inf_idem]
  rw [hinter] at hpair
  have hpos := T.residual_pos
  omega

theorem phaseA_seed (hroot : IsPhaseARoot N c m) :
    N ≤ phaseABudget c * T.C.card ^ (c + 1) :=
  phaseA_final_card_bound N c m T.C.card hroot T.root_le_card

theorem genericOn_univ :
    GenericUpToOn (PhaseAGeometry.family W0 Q0 T.toPhaseAGeometry)
      (Finset.univ : Finset T.Index) 2 T.r := by
  intro s hs hsub hcard
  exact T.generic_two s hs hcard

theorem universe_nonempty : (Finset.univ : Finset T.Index).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_univ, T.index_card]
  exact Finset.card_pos.mpr T.carrier_nonempty

theorem phaseA_seed_univ (hroot : IsPhaseARoot N c m) :
    N ≤ phaseABudget c *
      (Finset.univ : Finset T.Index).card ^ (c + 1) := by
  simpa only [Finset.card_univ, T.index_card] using
    PhaseATerminal.phaseA_seed W0 Q0 T hroot

end PhaseATerminal

noncomputable def terminalOfLargeBranch
    (X : PhaseAState W0 Q0 c N m) (hm : 1 ≤ m) (hr : 0 < X.r)
    (hlarge : LargeTwoGenericBranch (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) X.r m) :
    PhaseATerminal W0 Q0 c N m := by
  let S : Finset X.Index := Classical.choose hlarge
  have hlarge_spec := Classical.choose_spec hlarge
  rcases hlarge_spec with ⟨hS, hmS, htwoOn, hinj, htwo⟩
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

noncomputable def codimOneTerminal
    (X : PhaseAState W0 Q0 c N m) (hm : 1 ≤ m)
    (hroot : IsPhaseARoot N c m) (hrone : X.r = 1)
    (hcodim : ∀ i, Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) (W0 i) = c)
    (hinj : Function.Injective W0) :
    PhaseATerminal W0 Q0 c N m := by
  have hpos : 0 < X.r := by omega
  have hrelative : ∀ i : X.Index,
      relativeCodim (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry i) = 1 := by
    intro i
    rw [relativeCodim_eq_finrank_sub]
    rw [PhaseAGeometry.family_relativeCodim W0 Q0 X.toPhaseAGeometry hcodim i, hrone]
  have hlarge : LargeTwoGenericBranch
      (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry) X.r m := by
    have hmC : m ≤ X.C.card := PhaseAState.root_le_card W0 Q0 X hroot hpos
    have hmIndex : m ≤ Fintype.card X.Index := by
      simpa [PhaseAGeometry.Index] using hmC
    simpa [hrone] using
      (largeTwoGenericBranch_of_injective_relativeCodim_one
        (PhaseAGeometry.family W0 Q0 X.toPhaseAGeometry)
        (PhaseAGeometry.family_injective W0 Q0 X.toPhaseAGeometry hinj)
        (by intro i; exact hrelative i) m hmIndex)
  exact terminalOfLargeBranch W0 Q0 X hm hpos hlarge

end
end PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
