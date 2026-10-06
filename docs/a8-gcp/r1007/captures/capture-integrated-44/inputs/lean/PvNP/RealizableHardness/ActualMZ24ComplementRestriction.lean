import PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
import Mathlib.LinearAlgebra.Projection

namespace PvNP.RealizableHardness.ActualMZ24ComplementRestriction

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
open PvNP.RealizableHardness.ActualMaximalPairLadder
open Submodule

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a b d : Nat}
variable {Q : Grass V a}

noncomputable def relCodim (A W : Submodule (ZMod 2) V) : Nat :=
  Module.finrank (ZMod 2) A - Module.finrank (ZMod 2) W

structure AdviceComplement (Q : Grass V a) where
  A : Submodule (ZMod 2) V
  isCompl : IsCompl Q.val A

def complementSubspace (C : AdviceComplement Q) (W : Submodule (ZMod 2) V)
    : Submodule (ZMod 2) C.A :=
  W.comap C.A.subtype

def lift (C : AdviceComplement Q) (S : Submodule (ZMod 2) C.A) :
    Submodule (ZMod 2) V :=
  S.map C.A.subtype

theorem lift_complementSubspace (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    lift C (complementSubspace C W) = W ⊓ C.A := by
  calc
    lift C (complementSubspace C W) =
        (W.comap C.A.subtype).map C.A.subtype := rfl
    _ = C.A ⊓ W := Submodule.map_comap_subtype C.A W
    _ = W ⊓ C.A := inf_comm _ _

theorem reconstruction_sup (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Q.val ⊔ lift C (complementSubspace C W) = W := by
  rw [lift_complementSubspace C W hQW]
  rw [inf_comm]
  rw [← sup_inf_assoc_of_le C.A hQW, C.isCompl.sup_eq_top, top_inf_eq]

noncomputable def complementComponentEquiv (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    complementSubspace C W ≃ₗ[ZMod 2] C.A.comap W.subtype :=
  { toFun := fun x => ⟨⟨x.1, x.2⟩, x.1.2⟩
    invFun := fun y => ⟨⟨y.1, y.2⟩, y.1.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

theorem complementSubspace_finrank (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Module.finrank (ZMod 2) (complementSubspace C W) + a =
      Module.finrank (ZMod 2) W := by
  have hc := isCompl_comap_subtype_of_isCompl_of_le C.isCompl hQW
  have hd := Submodule.finrank_add_eq_of_isCompl hc
  have hq : Module.finrank (ZMod 2) (Q.val.comap W.subtype) = a := by
    rw [(Submodule.comapSubtypeEquivOfLe hQW).finrank_eq, Q.property]
  have ha : Module.finrank (ZMod 2) (C.A.comap W.subtype) =
      Module.finrank (ZMod 2) (complementSubspace C W) :=
    (complementComponentEquiv C W hQW).finrank_eq.symm
  rw [hq, ha] at hd
  simpa [Nat.add_comm] using hd

theorem complementSubspace_codim (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Module.finrank (ZMod 2) C.A -
        Module.finrank (ZMod 2) (complementSubspace C W) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W := by
  have hc := Submodule.finrank_add_eq_of_isCompl C.isCompl
  rw [Q.property] at hc
  have hw := complementSubspace_finrank C W hQW
  omega

theorem complementSubspace_eq_iff (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    complementSubspace C W = ⊥ ↔ W ⊓ C.A = ⊥ := by
  constructor
  · intro h
    have h' : lift C (complementSubspace C W) = ⊥ := by
      rw [h]
      simp [lift]
    rw [lift_complementSubspace C W hQW] at h'
    exact h'
  · intro h
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : (x.1 : V) ∈ W ⊓ C.A := ⟨hx, x.2⟩
    rw [h] at hx'
    have hx0 : (x.1 : V) = 0 := by simpa using hx'
    exact Subtype.ext hx0

theorem complementSubspace_ne_iff (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    complementSubspace C W ≠ ⊥ ↔ W ⊓ C.A ≠ ⊥ := by
  exact not_congr (complementSubspace_eq_iff C W hQW)

theorem lift_le_of_le (C : AdviceComplement Q)
    {W : Submodule (ZMod 2) V} (hQW : Q.val ≤ W)
    {S : Submodule (ZMod 2) C.A}
    (hS : S ≤ complementSubspace C W) : lift C S ≤ W := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact hS hy

theorem lift_finrank (C : AdviceComplement Q)
    (S : Submodule (ZMod 2) C.A) :
    Module.finrank (ZMod 2) (lift C S) = Module.finrank (ZMod 2) S := by
  change Module.finrank (ZMod 2) (S.map C.A.subtype) =
    Module.finrank (ZMod 2) S
  exact Submodule.finrank_map_subtype_eq C.A S

theorem complementSubspace_sup_lift (C : AdviceComplement Q)
    (S : Submodule (ZMod 2) C.A) :
    complementSubspace C (Q.val ⊔ lift C S) = S := by
  change (Q.val ⊔ S.map C.A.subtype).comap C.A.subtype = S
  rw [sup_comm]
  apply Submodule.comap_map_sup_of_comap_le
  intro x hx
  have hbot : C.A.subtype x ∈ (⊥ : Submodule (ZMod 2) V) :=
    C.isCompl.disjoint.le_bot ⟨hx, x.property⟩
  have hx0 : C.A.subtype x = 0 := by simpa using hbot
  have hx' : x = (0 : C.A) := Subtype.ext hx0
  simpa [hx']

theorem complementSubspace_lift (C : AdviceComplement Q)
    (S : Submodule (ZMod 2) C.A) :
    complementSubspace C (Q.val ⊔ lift C S) = S :=
  complementSubspace_sup_lift C S

def bottomGrass (A : Submodule (ZMod 2) V) : Grass A 0 :=
  ⟨⊥, by simp⟩

private def grassRankCast {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {m n : Nat} (h : m = n) : Grass U m ≃ Grass U n where
  toFun L := ⟨L.val, by simpa [h] using L.property⟩
  invFun L := ⟨L.val, by simpa [h] using L.property⟩
  left_inv L := by apply Subtype.ext; rfl
  right_inv L := by apply Subtype.ext; rfl

noncomputable def containingSubspaceEquiv (C : AdviceComplement Q)
    (d : Nat) (had : a ≤ d) :
    {L : Grass V d // Q.val ≤ L.val} ≃
      Grass C.A (d - a) := by
  exact {
    toFun := fun L => ⟨complementSubspace C L.1.val, by
      have hc := complementSubspace_finrank C L.1.val L.2
      rw [L.1.property] at hc
      exact Nat.eq_sub_of_add_eq hc⟩
    invFun := fun R => ⟨⟨Q.val ⊔ lift C R.val, by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq Q.val (lift C R.val)
      have hdis : Disjoint Q.val (lift C R.val) := by
        exact C.isCompl.disjoint.mono_right (by
          intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          exact y.property)
      rw [hdis.eq_bot, finrank_bot, add_zero] at hd
      rw [Q.property, lift_finrank C R.val, R.property] at hd
      simpa [Nat.add_sub_of_le had] using hd⟩,
      le_sup_left⟩
    left_inv := by
      intro L
      apply Subtype.ext
      apply Subtype.ext
      change Q.val ⊔ lift C (complementSubspace C L.1.val) = L.1.val
      exact reconstruction_sup C L.1.val L.2
    right_inv := by
      intro R
      apply Subtype.ext
      exact complementSubspace_sup_lift C R.val }

noncomputable def complementContainingGrassEquiv (C : AdviceComplement Q)
    (b : Nat) :
    {L : Grass V (a + b) // Q.val ≤ L.val} ≃ Grass C.A b := by
  exact (containingSubspaceEquiv C (a + b) (Nat.le_add_right a b)).trans
    (grassRankCast (Nat.add_sub_cancel_left a b))

theorem complementContainingGrassEquiv_apply (C : AdviceComplement Q)
    (b : Nat) (L : {L : Grass V (a + b) // Q.val ≤ L.val}) :
    (complementContainingGrassEquiv C b L).val =
      complementSubspace C L.1.val := by
  rfl

theorem complementContainingGrassEquiv_lift (C : AdviceComplement Q)
    (b : Nat) (R : Grass C.A b) :
    Q.val ⊔ lift C R.val =
      ((complementContainingGrassEquiv C b).symm R).1.val := by
  rfl

def complementInclusion (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) :
    complementSubspace C W →ₗ[ZMod 2] W :=
  { toFun := fun x => ⟨C.A.subtype x.1, x.2⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

def complementToPair (C : AdviceComplement Q)
    (P : DecodedPair Q d) :
    DecodedPair (bottomGrass C.A) (d - a) :=
  { W := complementSubspace C P.W
    hQW := bot_le
    g := P.g.comp (complementInclusion C P.W) }

def complementPair (C : AdviceComplement Q)
    (P : DecodedPair Q d) : DecodedPair (bottomGrass C.A) (d - a) :=
  complementToPair C P

noncomputable def complementZoomEquiv (C : AdviceComplement Q)
    (P : DecodedPair Q d) (had : a ≤ d) :
    Zoom Q P ≃ Zoom (bottomGrass C.A) (complementPair C P) := by
  let E := containingSubspaceEquiv C d had
  exact {
    toFun := fun z => ⟨E ⟨z.1, z.2.1⟩, ⟨bot_le, by
      exact Submodule.comap_mono z.2.2⟩⟩
    invFun := fun z => ⟨(E.symm z.1).1, ⟨(E.symm z.1).2, by
      change Q.val ⊔ lift C z.1.val ≤ P.W
      rw [← reconstruction_sup C P.W P.hQW]
      simpa [lift] using
        (sup_le le_sup_left ((Submodule.map_mono z.2.2).trans le_sup_right))⟩⟩
    left_inv := by
      intro z
      apply Subtype.ext
      exact congrArg
        (fun L : {L : Grass V d // Q.val ≤ L.val} => L.1)
        (E.left_inv ⟨z.1, z.2.1⟩)
    right_inv := by
      intro z
      apply Subtype.ext
      exact E.right_inv z.1 }

noncomputable def complementQuerySpace (C : AdviceComplement Q)
    (d b : Nat) (hb : a + b = d) (L : Grass C.A b) : Grass V d :=
  ⟨Q.val ⊔ lift C L.val, by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq Q.val (lift C L.val)
    have hdis : Disjoint Q.val (lift C L.val) := by
      exact C.isCompl.disjoint.mono_right (by
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact y.property)
    rw [hdis.eq_bot, finrank_bot, add_zero] at hd
    rw [Q.property, lift_finrank C L.val, L.property] at hd
    simpa [hb] using hd⟩

noncomputable def complementQueryInclusion (C : AdviceComplement Q)
    (d b : Nat) (hb : a + b = d) (L : Grass C.A b) :
    L.val →ₗ[ZMod 2] (complementQuerySpace C d b hb L).val :=
  { toFun := fun x => ⟨C.A.subtype x.1, by
      change C.A.subtype x.1 ∈ Q.val ⊔ lift C L.val
      exact (le_sup_right : lift C L.val ≤ Q.val ⊔ lift C L.val)
        ⟨x.1, x.2, rfl⟩⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

theorem complementQueryInclusion_apply (C : AdviceComplement Q)
    (d b : Nat) (hb : a + b = d) (L : Grass C.A b)
    (x : L.val) :
    ((complementQueryInclusion C d b hb L) x : V) = C.A.subtype x := rfl

noncomputable def complementTable
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (C : AdviceComplement Q) (had : a ≤ d)
    {b : Nat} (hb : a + b = d) :
    (L : Grass C.A b) → Module.Dual (ZMod 2) L.val :=
  fun L =>
    (T (complementQuerySpace C d b hb L)).comp
      (complementQueryInclusion C d b hb L)

private theorem dependentTable_apply
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    {K L : Grass V d} (h : K = L) (x : K.val) :
    T K x = T L (h ▸ x) := by
  cases h
  rfl

private theorem grassCast_coe
    {K L : Grass V d} (h : K = L) (x : K.val) :
    (((h ▸ x : L.val) : V)) = (x : V) := by
  cases h
  rfl

theorem agreesOn_complement
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (C : AdviceComplement Q) (P : DecodedPair Q d) (had : a ≤ d)
    (hb : a + (d - a) = d) (z : Zoom Q P)
    (hz : AgreesOn (T := T) z.1 z.2.2) :
    AgreesOn (T := complementTable T C had hb)
      (complementZoomEquiv C P had z).1
      (complementZoomEquiv C P had z).2.2 := by
  let E := containingSubspaceEquiv C d had
  let y := complementZoomEquiv C P had z
  let K := complementQuerySpace C d (d - a) hb y.1
  have hK : K = z.1 := by
    apply Subtype.ext
    change Q.val ⊔ lift C y.1.val = z.1.val
    change Q.val ⊔ lift C (E ⟨z.1, z.2.1⟩).val = z.1.val
    exact congrArg (fun L : {L : Grass V d // Q.val ≤ L.val} => L.1.val)
      (E.left_inv ⟨z.1, z.2.1⟩)
  intro x
  let x' : K.val :=
    complementQueryInclusion C d (d - a) hb y.1 x
  let hxz : z.1.val := hK ▸ x'
  have hz' := hz hxz
  calc
    (complementTable T C had hb) y.1 x = T K x' := by
      rfl
    _ = T z.1 hxz := by simpa [hxz] using (dependentTable_apply T hK x')
    _ = P.g ⟨hxz.1, z.2.2 hxz.property⟩ := hz'
    _ = (complementPair C P).g
        ⟨(x : C.A), (complementZoomEquiv C P had z).2.2 x.property⟩ := by
      change P.g _ = P.g _
      apply congrArg P.g
      apply Subtype.ext
      change hxz.1 = C.A.subtype x
      simpa [hxz] using
        ((grassCast_coe hK x').trans
          (complementQueryInclusion_apply C d (d - a) hb y.1 x))

theorem complement_agreement_le
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (C : AdviceComplement Q) (P : DecodedPair Q d) (had : a ≤ d)
    (hb : a + (d - a) = d) :
    agreement T Q P ≤
      agreement (complementTable T C had hb)
        (bottomGrass C.A) (complementPair C P) := by
  classical
  let E := complementZoomEquiv C P had
  let f : AgreeingZoom T Q P →
      AgreeingZoom (complementTable T C had hb)
        (bottomGrass C.A) (complementPair C P) := fun z =>
    ⟨E z.1, agreesOn_complement T C P had hb z.1 z.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact E.injective (congrArg Subtype.val hxy)
  have hnum : Fintype.card (AgreeingZoom T Q P) ≤
      Fintype.card (AgreeingZoom (complementTable T C had hb)
        (bottomGrass C.A) (complementPair C P)) :=
    Fintype.card_le_of_injective f hf
  have hden : Fintype.card (Zoom Q P) =
      Fintype.card (Zoom (bottomGrass C.A) (complementPair C P)) :=
    Fintype.card_congr E
  by_cases hzero : Fintype.card (Zoom Q P) = 0
  · have hzero' : Fintype.card
        (Zoom (bottomGrass C.A) (complementPair C P)) = 0 := by
      rw [← hden, hzero]
    rw [agreement_eq_zero_of_empty T Q P hzero,
      agreement_eq_zero_of_empty (complementTable T C had hb)
        (bottomGrass C.A) (complementPair C P) hzero']
  · have hzero' : Fintype.card
        (Zoom (bottomGrass C.A) (complementPair C P)) ≠ 0 := by
      rw [← hden]
      exact hzero
    rw [agreement_eq_fraction_of_nonempty T Q P hzero,
      agreement_eq_fraction_of_nonempty (complementTable T C had hb)
        (bottomGrass C.A) (complementPair C P) hzero']
    rw [← hden]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hnum
    · positivity

end
end PvNP.RealizableHardness.ActualMZ24ComplementRestriction
