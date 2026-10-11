import PvNP.RealizableHardness.ActualStarAffineFunctionalSelection
import PvNP.RealizableHardness.SubmoduleFunctionalGluing
import PvNP.RealizableHardness.ActualFiniteLaw
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact random-extension cost for the actual affine fiber of a decoded
linear functional. Rank stability makes restriction a bijection onto the
compatible retained labels; each fixed such label has mass 2^(-codim W). -/
namespace PvNP.RealizableHardness.ActualRandomExtensionSuccess

open PvNP.RealizableHardness
open ActualStarAffineFunctionalSelection SubmoduleFunctionalGluing ActualFiniteLaw
open ActualMaximalPairLadder
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]

/-- The exact codimension equality in the retained ambient implies that
the original decoded space and retained space span the original ambient. -/
theorem sup_eq_top_of_rank_stability (W V : Submodule (ZMod 2) E)
    (hrank : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W ⊓ V) =
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W) :
    W ⊔ V = ⊤ := by
  letI : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  have hW : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) E := W.finrank_le
  have hI : Module.finrank (ZMod 2) (W ⊓ V) ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_mono inf_le_right
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W V
  apply Submodule.eq_top_of_finrank_eq
  omega

/-- Gluing compatible labels when the two actual subspaces span E gives
exactly one ambient extension of g with the prescribed restriction to V. -/
theorem existsUnique_extension_with_restriction
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (f : Module.Dual (ZMod 2) V) (hspan : W ⊔ V = ⊤)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    ∃! F : FunctionalExtensionFiber W g, F.1.comp V.subtype = f := by
  obtain ⟨Fsup, hFsup, _⟩ := existsUnique_glue_on_sup W V g f hagree
  let intoSup : E →ₗ[ZMod 2] ↥(W ⊔ V) :=
    { toFun := fun x => ⟨x, by rw [hspan]; trivial⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let F := Fsup.comp intoSup
  have hFW : F.comp W.subtype = g := by
    ext x
    exact LinearMap.congr_fun hFsup.1 x
  have hFV : F.comp V.subtype = f := by
    ext x
    exact LinearMap.congr_fun hFsup.2 x
  refine ⟨⟨F, hFW⟩, hFV, ?_⟩
  intro G hGV
  apply Subtype.ext
  ext x
  change G.1 x = F x
  have hx : x ∈ W ⊔ V := by rw [hspan]; trivial
  obtain ⟨w, hw, v, hv, hsum⟩ := Submodule.mem_sup.mp hx
  have hGw : G.1 w = g ⟨w, hw⟩ := LinearMap.congr_fun G.2 ⟨w, hw⟩
  have hGv : G.1 v = f ⟨v, hv⟩ := LinearMap.congr_fun hGV ⟨v, hv⟩
  have hFw : F w = g ⟨w, hw⟩ := LinearMap.congr_fun hFW ⟨w, hw⟩
  have hFv : F v = f ⟨v, hv⟩ := LinearMap.congr_fun hFV ⟨v, hv⟩
  rw [← hsum, map_add, map_add, hGw, hGv, hFw, hFv]

/-- Uniform sampling from the full actual affine extension fiber. -/
def ambientExtensionLaw (W : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W) :
    FiniteLaw (FunctionalExtensionFiber W g) := by
  haveI : Nonempty (FunctionalExtensionFiber W g) :=
    ⟨⟨Classical.choose (LinearMap.exists_extend g), Classical.choose_spec (LinearMap.exists_extend g)⟩⟩
  exact uniformLaw (FunctionalExtensionFiber W g)

def restrictionSuccessEvent (W V : Submodule (ZMod 2) E)
    (g : Module.Dual (ZMod 2) W) (f : Module.Dual (ZMod 2) V) :
    Finset (FunctionalExtensionFiber W g) :=
  Finset.univ.filter fun F => F.1.comp V.subtype = f

theorem restrictionSuccessEvent_card_eq_one
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (f : Module.Dual (ZMod 2) V) (hspan : W ⊔ V = ⊤)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    (restrictionSuccessEvent W V g f).card = 1 := by
  obtain ⟨F, hF, hUnique⟩ := existsUnique_extension_with_restriction W V g f hspan hagree
  apply Finset.card_eq_one.mpr
  refine ⟨F, ?_⟩
  ext G
  simp only [restrictionSuccessEvent, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  exact ⟨fun hG => hUnique G hG, fun hGF => by simpa only [hGF] using hF⟩

theorem extension_restriction_success_mass
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (f : Module.Dual (ZMod 2) V) (hspan : W ⊔ V = ⊤)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f) =
      1 / (2 : Rat)^(codim W) := by
  have hcard := restrictionSuccessEvent_card_eq_one W V g f hspan hagree
  have htotal := functionalExtensionFiber_card W g rfl
  unfold eventMass ambientExtensionLaw
  simp only [uniformLaw_apply, Finset.sum_const, nsmul_eq_mul, hcard,
    Nat.cast_one, one_mul, htotal, Nat.cast_pow, Nat.cast_ofNat, codim]

theorem rank_stable_extension_success_mass
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (f : Module.Dual (ZMod 2) V)
    (hrank : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W ⊓ V) =
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f) =
      1 / (2 : Rat)^(codim W) :=
  extension_restriction_success_mass W V g f (sup_eq_top_of_rank_stability W V hrank) hagree

theorem rank_stable_extension_success_lower
    (W V : Submodule (ZMod 2) E) (g : Module.Dual (ZMod 2) W)
    (f : Module.Dual (ZMod 2) V) (r : Nat) (hr : codim W ≤ r)
    (hrank : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (W ⊓ V) =
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    1 / (2 : Rat)^r ≤
      eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f) := by
  rw [rank_stable_extension_success_mass W V g f hrank hagree]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ (by norm_num) hr)

/-- Every ambient extension preserves every prescribed value within W;
the source equation-span inclusion is one later specialization. -/
theorem every_extension_preserves_contained_label
    (H W : Submodule (ZMod 2) E) (hHW : H ≤ W)
    (g : Module.Dual (ZMod 2) W) (rhs : Module.Dual (ZMod 2) H)
    (hg : g.comp (Submodule.inclusion hHW) = rhs)
    (F : FunctionalExtensionFiber W g) : F.1.comp H.subtype = rhs := by
  ext x
  calc
    F.1 x.1 = g ⟨x.1, hHW x.2⟩ := LinearMap.congr_fun F.2 ⟨x.1, hHW x.2⟩
    _ = rhs x := LinearMap.congr_fun hg x

end
end PvNP.RealizableHardness.ActualRandomExtensionSuccess
