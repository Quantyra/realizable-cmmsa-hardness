import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Tactic

/-! D3c4a1 bounded support: actual codimension-one carriers and restriction.

This file records only the hyperplane/normal-line and one-step restriction
geometry.  It deliberately contains no maximal TwoGeneric selection, pair
obstruction, global cover, largest-fibre argument, or final dichotomy.
-/

namespace PvNP.RealizableHardness.ActualMZ24HyperplaneSupport

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The already-certified ambient codimension, exposed under the geometric name.
It is intentionally not a new dimension convention. -/
abbrev relativeCodim (W : Submodule (ZMod 2) V) : Nat :=
  ActualMaximalPairLadder.codim W

lemma relativeCodim_eq_finrank_sub (W : Submodule (ZMod 2) V) :
    relativeCodim W = Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) W := rfl

lemma dualAnnihilator_finrank (W : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) W.dualAnnihilator = relativeCodim W := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  unfold relativeCodim ActualMaximalPairLadder.codim
  omega

/-- A hyperplane is a subspace of relative codimension one. -/
def IsHyperplane (H : Submodule (ZMod 2) V) : Prop :=
  relativeCodim H = 1

/-- The subtype of actual hyperplanes in the fixed finite ambient space. -/
abbrev Hyperplane := {H : Submodule (ZMod 2) V // IsHyperplane H}

/-- A hyperplane containing a prescribed subspace. -/
abbrev ContainingHyperplane (W : Submodule (ZMod 2) V) :=
  {H : Hyperplane (V := V) // W ≤ H.1}

/-- The finite carrier used by the bounded count. -/
noncomputable def containingHyperplanes (W : Submodule (ZMod 2) V) :
    Finset (ContainingHyperplane W) := Finset.univ

theorem isCoatom_iff_relativeCodim_eq_one
    (H : Submodule (ZMod 2) V) :
    IsCoatom H ↔ relativeCodim H = 1 := by
  constructor
  · intro hH
    have hs : IsSimpleModule (ZMod 2) (V ⧸ H) :=
      (isSimpleModule_iff_isCoatom (R := ZMod 2) (M := V) (m := H)).mpr hH
    have hq : Module.finrank (ZMod 2) (V ⧸ H) = 1 :=
      (isSimpleModule_iff_finrank_eq_one (R := ZMod 2) (M := V ⧸ H)).mp hs
    have hd := H.finrank_quotient_add_finrank
    unfold relativeCodim ActualMaximalPairLadder.codim
    omega
  · intro hH
    apply (isSimpleModule_iff_isCoatom (R := ZMod 2) (M := V) (m := H)).mp
    apply (isSimpleModule_iff_finrank_eq_one (R := ZMod 2) (M := V ⧸ H)).mpr
    have hd := H.finrank_quotient_add_finrank
    unfold relativeCodim ActualMaximalPairLadder.codim at hH
    omega

theorem hyperplane_isCoatom (H : Hyperplane (V := V)) :
    IsCoatom H.1 :=
  (isCoatom_iff_relativeCodim_eq_one H.1).mpr H.2

lemma hyperplane_ne_top (H : Hyperplane (V := V)) : H.1 ≠ (⊤ : Submodule (ZMod 2) V) := by
  intro htop
  have hcod : relativeCodim H.1 = 1 := H.2
  rw [htop] at hcod
  simp [relativeCodim, ActualMaximalPairLadder.codim] at hcod

theorem exists_hyperplane_containing_of_ne_top
    (W : Submodule (ZMod 2) V) (hW : W ≠ (⊤ : Submodule (ZMod 2) V)) :
    Nonempty (ContainingHyperplane W) := by
  have hlt : Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) V := by
    simpa only [finrank_top] using
      (Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hW))
  have hpos : 0 < relativeCodim W := by
    unfold relativeCodim ActualMaximalPairLadder.codim
    omega
  letI : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun g => g.toFun) (by
      intro f g h
      apply LinearMap.ext
      exact fun x => congrFun h x)
  letI : Fintype W.dualAnnihilator := Fintype.ofFinite _
  have hline : Nonempty (Grass W.dualAnnihilator 1) := by
    apply grass_nonempty_of_le (V := W.dualAnnihilator)
    rw [dualAnnihilator_finrank]
    omega
  let L : Grass W.dualAnnihilator 1 := Classical.choice hline
  let L' : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) :=
    L.1.map W.dualAnnihilator.subtype
  have hLdim : Module.finrank (ZMod 2) L' = 1 := by
    rw [Submodule.finrank_map_subtype_eq]
    exact L.2
  have hLle : L' ≤ W.dualAnnihilator := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro x hx
    exact x.property
  let H : Submodule (ZMod 2) V := L'.dualCoannihilator
  have hWH : W ≤ H := by
    intro x hx
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    exact (Submodule.mem_dualAnnihilator (W := W) φ).mp (hLle hφ) x hx
  have hcod : relativeCodim H = 1 := by
    have ha := Subspace.finrank_add_finrank_dualCoannihilator_eq L'
    have hd := Subspace.dual_finrank_eq (K := ZMod 2) (V := V)
    dsimp [H]
    unfold relativeCodim ActualMaximalPairLadder.codim
    omega
  exact ⟨⟨⟨H, hcod⟩, hWH⟩⟩

/-- The normal line of a hyperplane is its dual annihilator. -/
noncomputable def hyperplaneNormalLine (H : Hyperplane (V := V)) :
    Grass (Module.Dual (ZMod 2) V) 1 :=
  ⟨H.1.dualAnnihilator, by
    rw [dualAnnihilator_finrank]
    exact H.2⟩

theorem hyperplaneNormalLine_injective :
    Function.Injective (hyperplaneNormalLine (V := V)) := by
  intro H K hHK
  apply Subtype.ext
  apply Subspace.dualAnnihilator_inj.mp
  exact congrArg Subtype.val hHK

/-- The normal line of a containing hyperplane lies in the annihilator of W. -/
noncomputable def containingHyperplaneNormalLine
    (W : Submodule (ZMod 2) V) (H : ContainingHyperplane W) :
    {L : Grass (Module.Dual (ZMod 2) V) 1 //
      L.1 ≤ W.dualAnnihilator} :=
  ⟨hyperplaneNormalLine H.1,
    (Subspace.dualAnnihilator_le_dualAnnihilator_iff).2 H.2⟩

theorem containingHyperplaneNormalLine_injective (W : Submodule (ZMod 2) V) :
    Function.Injective (containingHyperplaneNormalLine (V := V) W) := by
  intro H K hHK
  apply Subtype.ext
  apply Subtype.ext
  apply Subspace.dualAnnihilator_inj.mp
  exact congrArg Subtype.val (congrArg Subtype.val hHK)

/-- A line in the annihilator of `A` cuts out a hyperplane containing `A`. -/
noncomputable def containingHyperplaneOfNormalLine
    (A : Submodule (ZMod 2) V)
    (L : {L : Grass (Module.Dual (ZMod 2) V) 1 //
      L.1 ≤ A.dualAnnihilator}) : ContainingHyperplane A := by
  letI : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun g => g.toFun) (by
      intro f g h
      apply LinearMap.ext
      exact fun x => congrFun h x)
  let H : Submodule (ZMod 2) V := L.1.1.dualCoannihilator
  have hcod : relativeCodim H = 1 := by
    rw [← dualAnnihilator_finrank]
    change Module.finrank (ZMod 2)
      L.1.1.dualCoannihilator.dualAnnihilator = 1
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact L.1.2
  have hAH : A ≤ H :=
    (Submodule.le_dualAnnihilator_iff_le_dualCoannihilator).mp L.2
  exact ⟨⟨H, hcod⟩, hAH⟩

/-- Containing hyperplanes are exactly the normal lines in the annihilator. -/
noncomputable def containingHyperplaneNormalLineEquiv
    (A : Submodule (ZMod 2) V) :
    ContainingHyperplane A ≃
      {L : Grass (Module.Dual (ZMod 2) V) 1 //
        L.1 ≤ A.dualAnnihilator} where
  toFun := containingHyperplaneNormalLine A
  invFun := containingHyperplaneOfNormalLine A
  left_inv := by
    intro H
    apply Subtype.ext
    apply Subtype.ext
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv := by
    intro L
    apply Subtype.ext
    apply Subtype.ext
    exact Subspace.dualCoannihilator_dualAnnihilator_eq

theorem gaussian_one_of_pos {n : Nat} (hn : 0 < n) :
    gaussian n 1 = 2^n - 1 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  simp [gaussian, frameProduct, hn, hn1, hn0]

theorem gaussian_one_all (n : Nat) : gaussian n 1 = 2^n - 1 := by
  by_cases hn : n = 0
  · subst n
    norm_num [gaussian, frameProduct]
  · exact gaussian_one_of_pos (Nat.pos_of_ne_zero hn)

/-- Exact binary count, including the zero-codimension (`A = ⊤`) case. -/
theorem card_containingHyperplanes_eq_two_pow_sub_one
    (A : Submodule (ZMod 2) V) :
    (containingHyperplanes A).card = 2 ^ relativeCodim A - 1 := by
  letI : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun g => g.toFun) (by
      intro f g h
      apply LinearMap.ext
      exact fun x => congrFun h x)
  calc
    (containingHyperplanes A).card = Fintype.card (ContainingHyperplane A) := by
      simp [containingHyperplanes]
    _ = Fintype.card {L : Grass (Module.Dual (ZMod 2) V) 1 //
        L.1 ≤ A.dualAnnihilator} :=
      Fintype.card_congr (containingHyperplaneNormalLineEquiv A)
    _ = gaussian (Module.finrank (ZMod 2) A.dualAnnihilator) 1 := by
      simpa only [Nat.card_eq_fintype_card] using
        (card_contained (a := 1) A.dualAnnihilator)
    _ = 2 ^ relativeCodim A - 1 := by
      rw [gaussian_one_all, dualAnnihilator_finrank]

theorem card_containingHyperplanes_lt_two_pow
    (W : Submodule (ZMod 2) V) (hW : W ≠ (⊤ : Submodule (ZMod 2) V)) :
    (containingHyperplanes W).card < 2 ^ relativeCodim W := by
  letI : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun g => g.toFun) (by
      intro f g h
      apply LinearMap.ext
      exact fun x => congrFun h x)
  have hi := Fintype.card_le_of_injective
    (fun H : ContainingHyperplane W => containingHyperplaneNormalLine W H)
    (containingHyperplaneNormalLine_injective W)
  have hc : Fintype.card {L : Grass (Module.Dual (ZMod 2) V) 1 //
      L.1 ≤ W.dualAnnihilator} = gaussian (Module.finrank (ZMod 2) W.dualAnnihilator) 1 := by
    simpa only [Nat.card_eq_fintype_card] using
      (card_contained (a := 1) W.dualAnnihilator)
  have hpos : 0 < relativeCodim W := by
    have hlt : Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) V := by
      simpa only [finrank_top] using
        (Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hW))
    unfold relativeCodim ActualMaximalPairLadder.codim
    omega
  have hgauss : gaussian (Module.finrank (ZMod 2) W.dualAnnihilator) 1 =
      2 ^ relativeCodim W - 1 := by
    have hdualpos : 0 < Module.finrank (ZMod 2) W.dualAnnihilator := by
      rw [dualAnnihilator_finrank]
      exact hpos
    rw [gaussian_one_of_pos hdualpos]
    rw [dualAnnihilator_finrank]
  have hpow : 0 < 2 ^ relativeCodim W := Nat.two_pow_pos _
  have hsub : 2 ^ relativeCodim W - 1 < 2 ^ relativeCodim W :=
    Nat.sub_lt hpow (by omega)
  have hcard : (containingHyperplanes W).card ≤ 2 ^ relativeCodim W - 1 := by
    have hi' : Fintype.card (ContainingHyperplane W) ≤
        Fintype.card {L : Grass (Module.Dual (ZMod 2) V) 1 //
          L.1 ≤ W.dualAnnihilator} := hi
    calc
      (containingHyperplanes W).card = Fintype.card (ContainingHyperplane W) := by
        simp [containingHyperplanes]
      _ ≤ Fintype.card {L : Grass (Module.Dual (ZMod 2) V) 1 //
          L.1 ≤ W.dualAnnihilator} := hi'
      _ = gaussian (Module.finrank (ZMod 2) W.dualAnnihilator) 1 := hc
      _ = 2 ^ relativeCodim W - 1 := hgauss
  exact hcard.trans_lt hsub

/-- Restriction of a subspace lying in a hyperplane, with the ambient type changed
to the hyperplane subtype. -/
def restrictToHyperplane (H : Hyperplane (V := V))
    (W : Submodule (ZMod 2) V) (hWH : W ≤ H.1) :
    Submodule (ZMod 2) H.1 := W.comap H.1.subtype

theorem restrictToHyperplane_map_recovery (H : Hyperplane (V := V))
    (W : Submodule (ZMod 2) V) (hWH : W ≤ H.1) :
    (restrictToHyperplane H W hWH).map H.1.subtype = W := by
  unfold restrictToHyperplane
  rw [Submodule.map_comap_subtype]
  exact inf_eq_right.mpr hWH

theorem restrictToHyperplane_finrank (H : Hyperplane (V := V))
    (W : Submodule (ZMod 2) V) (hWH : W ≤ H.1) :
    Module.finrank (ZMod 2) (restrictToHyperplane H W hWH) =
      Module.finrank (ZMod 2) W := by
  rw [← Submodule.finrank_map_subtype_eq]
  rw [restrictToHyperplane_map_recovery]

theorem relativeCodim_restrict_add_one (H : Hyperplane (V := V))
    (W : Submodule (ZMod 2) V) (hWH : W ≤ H.1) :
    relativeCodim (restrictToHyperplane H W hWH) + 1 = relativeCodim W := by
  have hHcod : relativeCodim H.1 = 1 := H.2
  unfold relativeCodim ActualMaximalPairLadder.codim at hHcod
  have hH : Module.finrank (ZMod 2) H.1 + 1 = Module.finrank (ZMod 2) V := by
    omega
  have hWrank : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) H.1 :=
    Submodule.finrank_mono hWH
  rw [relativeCodim_eq_finrank_sub, relativeCodim_eq_finrank_sub]
  rw [restrictToHyperplane_finrank]
  omega

theorem relativeCodim_restrict_pred (H : Hyperplane (V := V))
    (W : Submodule (ZMod 2) V) (hWH : W ≤ H.1)
    (hpos : 0 < relativeCodim W) :
    relativeCodim (restrictToHyperplane H W hWH) = relativeCodim W - 1 := by
  have h := relativeCodim_restrict_add_one H W hWH
  omega

def restrictFamily {I : Type*} (H : Hyperplane (V := V))
    (W : I → Submodule (ZMod 2) V) (hW : ∀ i, W i ≤ H.1) :
    I → Submodule (ZMod 2) H.1 :=
  fun i => restrictToHyperplane H (W i) (hW i)

theorem restrictFamily_injective {I : Type*}
    (H : Hyperplane (V := V)) (W : I → Submodule (ZMod 2) V)
    (hW : ∀ i, W i ≤ H.1) (hinj : Function.Injective W) :
    Function.Injective (restrictFamily H W hW) := by
  intro i j hij
  apply hinj
  have hm := congrArg (fun S : Submodule (ZMod 2) H.1 => S.map H.1.subtype) hij
  change (restrictToHyperplane H (W i) (hW i)).map H.1.subtype =
      (restrictToHyperplane H (W j) (hW j)).map H.1.subtype at hm
  rw [restrictToHyperplane_map_recovery, restrictToHyperplane_map_recovery] at hm
  exact hm

theorem restrictFamily_relativeCodim_add_one {I : Type*}
    (H : Hyperplane (V := V)) (W : I → Submodule (ZMod 2) V)
    (hW : ∀ i, W i ≤ H.1) (i : I) :
    relativeCodim (restrictFamily H W hW i) + 1 = relativeCodim (W i) :=
  relativeCodim_restrict_add_one H (W i) (hW i)

end
end PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
