import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
import PvNP.RealizableHardness.ActualStarAcceptedGoodMass

/-! Ordinary all-ambient star law at the fixed-table inverse input. -/
namespace PvNP.RealizableHardness.ActualOrdinaryStarSelection

open scoped BigOperators
open GrassmannCounting ActualFiniteLaw ActualSourceStarLaw
open ActualChangedAmbient8SBoundary ActualStarAcceptedGoodMass
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

private theorem star_accepts_iff {t d m : Nat}
    (C : Labels (V := V) t) (T : Labels (V := V) d)
    (z : StarTuple (V := V) t d m) :
    StarAccepts C T z.1 z.2 ↔ accepts C T z := by
  constructor
  · intro h i
    ext x
    exact (h i x).symm
  · intro h i x
    have hi := congrArg (fun F : Module.Dual (ZMod 2) z.1.val => F x) (h i)
    exact hi.symm

private theorem ordinary_star_point_mass {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (K : Grass V t) (Ls : Fin m → LeafOver K d) :
    (starLaw (V := V) (t := t) (d := d) (m := m) htd hdV).mass ⟨K,Ls⟩ =
      (@uniformLaw (Grass V t) inferInstance hcenter).mass K *
        (@uniformLaw (Fin m → LeafOver K d) inferInstance
          ⟨fun _ => Classical.choice (hleaf K)⟩).mass Ls := by
  letI : Nonempty (Grass V t) := hcenter
  letI : Nonempty (Fin m → LeafOver K d) := ⟨fun _ => Classical.choice (hleaf K)⟩
  rw [starLaw_mass (V := V) htd hdV ⟨K,Ls⟩,
    uniformLaw_apply, uniformLaw_apply,
    starTuple_card (V := V) htd hdV]
  have hc : Fintype.card (Fin m → LeafOver K d) =
      gaussian (Module.finrank (ZMod 2) V - t) (d - t) ^ m := by
    change Fintype.card (Fin m → Extension K d) = _
    rw [Fintype.card_fun]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact extension_card (V := V) K htd ▸ rfl
  rw [hc]
  simp only [Nat.cast_mul, one_div, mul_inv_rev]
  ring

theorem starDensity_eq_acceptanceMass {t d m : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d) :
    StarDensity (k := m) hcenter hleaf C T =
      acceptanceMass (V := V) htd hdV m C T := by
  classical
  unfold StarDensity acceptanceMass eventMass
  rw [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro K _
  apply Finset.sum_congr rfl
  intro Ls _
  rw [ordinary_star_point_mass htd hdV hcenter hleaf K Ls]
  by_cases ha : accepts C T ⟨K,Ls⟩
  · have hs : StarAccepts C T K Ls :=
      (star_accepts_iff C T ⟨K,Ls⟩).mpr ha
    simp [ha, hs]
  · have hs : ¬ StarAccepts C T K Ls := by
      exact (star_accepts_iff C T ⟨K,Ls⟩).not.mpr ha
    simp [ha, hs]

theorem ordinary_good_mass_gt_half {t d m E : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (hguard : m * (d - t) + E + 2 ≤ Module.finrank (ZMod 2) V - t)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d)
    (hscore : successMargin E ≤ StarDensity (k := m) hcenter hleaf C T) :
    successMargin E / 2 < goodStarMass (V := V) htd hdV m C T := by
  let mu := starLaw (V := V) (t := t) (d := d) (m := m) htd hdV
  have hbad := starLaw_bad_mass_lt_threshold (V := V) htd hdV hk hguard
  rw [← successMargin_half] at hbad
  have hgood0 := eventMass_accept_rankGood_ge mu (accepts C T) jointlyDirect
  have hset : (Finset.univ.filter fun z : StarTuple (V := V) t d m =>
      accepts C T z ∧ jointlyDirect z) =
      Finset.univ.filter (goodStar C T) := by
    ext z
    simp [goodStar]
  rw [hset] at hgood0
  have hgood : goodStarMass (V := V) htd hdV m C T ≥
    acceptanceMass (V := V) htd hdV m C T -
      eventMass mu (Finset.univ.filter fun z => ¬ jointlyDirect z) := by
    simpa only [mu, goodStarMass, acceptanceMass] using hgood0
  rw [← starDensity_eq_acceptanceMass htd hdV hcenter hleaf C T] at hgood
  linarith

end
end PvNP.RealizableHardness.ActualOrdinaryStarSelection
