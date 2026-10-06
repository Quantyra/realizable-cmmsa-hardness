import PvNP.RealizableHardness.ActualOrdinaryStarMatchingFiber

namespace PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection

open scoped BigOperators
open GrassmannCounting ActualFiniteLaw ActualSourceStarLaw
open ActualOrdinaryStarMatchingFiber ActualOrdinaryStarSelection
open ActualStarAffineFunctionalSelection
open ActualStarAcceptedGoodMass ActualChangedAmbient8SBoundary
open ActualFiniteIncidenceSampling
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

private noncomputable instance dualFinite : Finite (Module.Dual (ZMod 2) V) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) V => f.toFun) (by
    intro f g h
    apply LinearMap.ext
    intro x
    exact congrFun h x)

private noncomputable instance dualFintype : Fintype (Module.Dual (ZMod 2) V) :=
  Fintype.ofFinite _

private theorem dual_card :
    Fintype.card (Module.Dual (ZMod 2) V) =
      2 ^ Module.finrank (ZMod 2) V := by
  classical
  have hbot : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = 0 :=
    finrank_bot (ZMod 2) V
  have hc := functionalExtensionFiber_card
    (⊥ : Submodule (ZMod 2) V)
    (0 : (⊥ : Submodule (ZMod 2) V) →ₗ[ZMod 2] ZMod 2) hbot
  let e : FunctionalExtensionFiber (⊥ : Submodule (ZMod 2) V) 0 ≃
      Module.Dual (ZMod 2) V :=
    { toFun := fun f => f.1
      invFun := fun f => ⟨f, by
        ext x
        have hx : (x : V) ∈ (⊥ : Submodule (ZMod 2) V) := x.property
        rw [Submodule.mem_bot] at hx
        simp [hx]⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, hc]
  simp

def matchingStarMass {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (f : Module.Dual (ZMod 2) V) : ℚ :=
  eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV)
    (Finset.univ.filter fun z : StarTuple (V := V) t d m => MatchesStar C T z f)

def matchingCenterMass {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (C : CenterTable (V := V) t)
    (f : Module.Dual (ZMod 2) V) : ℚ :=
  eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV)
    (Finset.univ.filter fun z : StarTuple (V := V) t d m =>
      f.comp z.1.val.subtype = C z.1)

theorem matchingStarMass_le_centerMass {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (f : Module.Dual (ZMod 2) V) :
    matchingStarMass (m := m) htd hdV C T f ≤
      matchingCenterMass (m := m) htd hdV C f := by
  unfold matchingStarMass matchingCenterMass
  apply ActualStarAcceptedGoodMass.eventMass_mono
  intro z hz
  have hm := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.1⟩

private theorem starLaw_eventMass_eq_card {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (Extension K d))
    (E : Finset (StarTuple (V := V) t d m)) :
    eventMass (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV) E =
      (E.card : ℚ) / Fintype.card (StarTuple (V := V) t d m) := by
  letI : Nonempty (Grass V t) := hcenter
  letI : Nonempty (StarTuple (V := V) t d m) :=
    ⟨⟨Classical.choice hcenter, fun _ => Classical.choice (hleaf _)⟩⟩
  change eventMass (uniformLaw (StarTuple (V := V) t d m)) E = _
  exact eventMass_uniform_eq_card E

private theorem matching_count_on_good {t d m : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m) (hz : goodStar C T z) :
    (Finset.univ.filter fun f : Module.Dual (ZMod 2) V =>
      MatchesStar C T z f).card =
      2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t))) := by
  have hc := matchingStar_fibre_card C T z hz.1 hz.2
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc

theorem matchingStarMass_sum_ge_good {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (Extension K d))
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d) :
    goodStarMass (V := V) htd hdV m C T *
      (2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t))) : ℚ) ≤
        ∑ f : Module.Dual (ZMod 2) V,
          matchingStarMass (m := m) htd hdV C T f := by
  classical
  let Ω := StarTuple (V := V) t d m
  let G : Finset Ω := Finset.univ.filter (goodStar C T)
  let M := 2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t)))
  have hsum : (∑ f : Module.Dual (ZMod 2) V,
      (Finset.univ.filter fun z : Ω => MatchesStar C T z f).card) =
      ∑ z : Ω, (Finset.univ.filter fun f : Module.Dual (ZMod 2) V =>
        MatchesStar C T z f).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hnat : G.card * M ≤
      ∑ f : Module.Dual (ZMod 2) V,
        (Finset.univ.filter fun z : Ω => MatchesStar C T z f).card := by
    rw [hsum]
    calc
      G.card * M = ∑ z : Ω, if z ∈ G then M else 0 := by
        simp [Finset.sum_ite, G]
      _ ≤ ∑ z : Ω, (Finset.univ.filter fun f : Module.Dual (ZMod 2) V =>
          MatchesStar C T z f).card := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : z ∈ G
        · simp only [if_pos hz]
          exact le_of_eq (by
            simpa only [M] using
              (matching_count_on_good C T z (Finset.mem_filter.mp hz).2).symm)
        · simp [hz]
  have hΩ : 0 < (Fintype.card Ω : ℚ) := by
    haveI : Nonempty Ω :=
      ⟨⟨Classical.choice hcenter, fun _ => Classical.choice (hleaf _)⟩⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hGood : goodStarMass (V := V) htd hdV m C T =
      (G.card : ℚ) / Fintype.card Ω := by
    exact starLaw_eventMass_eq_card htd hdV hcenter hleaf G
  have hX : (∑ f : Module.Dual (ZMod 2) V,
      matchingStarMass (m := m) htd hdV C T f) =
      (∑ f : Module.Dual (ZMod 2) V,
        ((Finset.univ.filter fun z : Ω => MatchesStar C T z f).card : ℚ)) /
          Fintype.card Ω := by
    simp_rw [matchingStarMass,
      starLaw_eventMass_eq_card htd hdV hcenter hleaf]
    rw [Finset.sum_div]
  rw [hGood, hX]
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hΩ).mpr (by exact_mod_cast hnat)

private theorem center_matching_count {t d m : Nat}
    (C : CenterTable (V := V) t) (z : StarTuple (V := V) t d m) :
    (Finset.univ.filter fun f : Module.Dual (ZMod 2) V =>
      f.comp z.1.val.subtype = C z.1).card =
        2 ^ (Module.finrank (ZMod 2) V - t) := by
  have hc := functionalExtensionFiber_card z.1.val (C z.1) z.1.property
  simpa only [FunctionalExtensionFiber, Fintype.card_subtype] using hc

theorem matchingCenterMass_sum_eq {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (Extension K d))
    (C : CenterTable (V := V) t) :
    (∑ f : Module.Dual (ZMod 2) V,
      matchingCenterMass (m := m) htd hdV C f) =
        (2 ^ (Module.finrank (ZMod 2) V - t) : ℚ) := by
  classical
  let Ω := StarTuple (V := V) t d m
  let M := 2 ^ (Module.finrank (ZMod 2) V - t)
  have hsum : (∑ f : Module.Dual (ZMod 2) V,
      (Finset.univ.filter fun z : Ω =>
        f.comp z.1.val.subtype = C z.1).card) =
      ∑ z : Ω, (Finset.univ.filter fun f : Module.Dual (ZMod 2) V =>
        f.comp z.1.val.subtype = C z.1).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hX : (∑ f : Module.Dual (ZMod 2) V,
      matchingCenterMass (m := m) htd hdV C f) =
      (∑ f : Module.Dual (ZMod 2) V,
        ((Finset.univ.filter fun z : Ω =>
          f.comp z.1.val.subtype = C z.1).card : ℚ)) /
          Fintype.card Ω := by
    simp_rw [matchingCenterMass,
      starLaw_eventMass_eq_card htd hdV hcenter hleaf]
    rw [Finset.sum_div]
  have hΩ : (Fintype.card Ω : ℚ) ≠ 0 := by
    haveI : Nonempty Ω :=
      ⟨⟨Classical.choice hcenter, fun _ => Classical.choice (hleaf _)⟩⟩
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  rw [hX]
  have hsumQ := congrArg (fun x : Nat => (x : ℚ)) hsum
  push_cast at hsumQ
  rw [hsumQ]
  simp_rw [center_matching_count C]
  simp [M, Finset.sum_const, hΩ]

theorem exists_weighted_matching_functional {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (Extension K d))
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (ε : ℚ) (hε : 0 ≤ ε)
    (hgood : ε / 2 ≤ goodStarMass (V := V) htd hdV m C T) :
    ∃ f : Module.Dual (ZMod 2) V,
      let X := matchingStarMass (m := m) htd hdV C T f
      let β := matchingCenterMass (m := m) htd hdV C f
      let M : ℚ := 2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t)))
      let B : ℚ := 2 ^ (Module.finrank (ZMod 2) V - t)
      let F : ℚ := 2 ^ Module.finrank (ZMod 2) V
      (ε / 4) * (M / B) * β + (ε / 4) * (M / F) ≤ X ∧ X ≤ β := by
  classical
  let M : ℚ := 2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t)))
  let B : ℚ := 2 ^ (Module.finrank (ZMod 2) V - t)
  let F : ℚ := 2 ^ Module.finrank (ZMod 2) V
  let c : ℚ := (ε / 4) * (M / B)
  let b : ℚ := (ε / 4) * (M / F)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : B ≠ 0 := by dsimp [B]; positivity
  have hF : F ≠ 0 := by dsimp [F]; positivity
  have hX := matchingStarMass_sum_ge_good (m := m) htd hdV hcenter hleaf C T
  have hβ := matchingCenterMass_sum_eq (m := m) htd hdV hcenter hleaf C
  change goodStarMass (V := V) htd hdV m C T * M ≤
    ∑ f : Module.Dual (ZMod 2) V,
      matchingStarMass (m := m) htd hdV C T f at hX
  change (∑ f : Module.Dual (ZMod 2) V,
      matchingCenterMass (m := m) htd hdV C f) = B at hβ
  have hεM : ε / 2 * M ≤ goodStarMass (V := V) htd hdV m C T * M :=
    mul_le_mul_of_nonneg_right hgood hM
  have hsum :
      (∑ _f : Module.Dual (ZMod 2) V, b) ≤
        ∑ f : Module.Dual (ZMod 2) V,
          (matchingStarMass (m := m) htd hdV C T f -
            c * matchingCenterMass (m := m) htd hdV C f) := by
    have hcard : (Fintype.card (Module.Dual (ZMod 2) V) : ℚ) = F := by
      change (Fintype.card (Module.Dual (ZMod 2) V) : ℚ) =
        (2 ^ Module.finrank (ZMod 2) V : ℚ)
      exact_mod_cast dual_card (V := V)
    have hleft : (∑ _f : Module.Dual (ZMod 2) V, b) = ε / 4 * M := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hcard]
      dsimp [b]
      field_simp [hF]
    have hright : (∑ f : Module.Dual (ZMod 2) V,
        (matchingStarMass (m := m) htd hdV C T f -
          c * matchingCenterMass (m := m) htd hdV C f)) =
        (∑ f : Module.Dual (ZMod 2) V,
          matchingStarMass (m := m) htd hdV C T f) - c * B := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hβ]
    rw [hleft, hright]
    have hcB : c * B = ε / 4 * M := by
      dsimp [c]
      field_simp [hB]
    rw [hcB]
    linarith
  obtain ⟨f, _hfmem, hf⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _ : Module.Dual (ZMod 2) V => b)
    (g := fun f => matchingStarMass (m := m) htd hdV C T f -
      c * matchingCenterMass (m := m) htd hdV C f)
    Finset.univ_nonempty hsum
  refine ⟨f, ?_⟩
  dsimp only
  constructor
  · change c * matchingCenterMass (m := m) htd hdV C f + b ≤
      matchingStarMass (m := m) htd hdV C T f
    linarith
  · exact matchingStarMass_le_centerMass htd hdV C T f

theorem ordinary_star_selects_weighted_functional {t d m E : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (hguard : m * (d - t) + E + 2 ≤ Module.finrank (ZMod 2) V - t)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (hscore : successMargin E ≤
      ActualChangedAmbient8SBoundary.StarDensity (k := m) hcenter hleaf C T) :
    ∃ f : Module.Dual (ZMod 2) V,
      let X := matchingStarMass (m := m) htd hdV C T f
      let β := matchingCenterMass (m := m) htd hdV C f
      let M : ℚ := 2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t)))
      let B : ℚ := 2 ^ (Module.finrank (ZMod 2) V - t)
      let F : ℚ := 2 ^ Module.finrank (ZMod 2) V
      (successMargin E / 4) * (M / B) * β +
        (successMargin E / 4) * (M / F) ≤ X ∧ X ≤ β := by
  have hε : 0 ≤ successMargin E := by
    unfold successMargin
    positivity
  have hgood := ordinary_good_mass_gt_half htd hdV hk hguard
    hcenter hleaf C T hscore
  exact exists_weighted_matching_functional htd hdV hcenter hleaf C T
    (successMargin E) hε (le_of_lt hgood)

end
end PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
