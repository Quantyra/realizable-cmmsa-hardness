import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualModifiedPcpCeiling
import PvNP.RealizableHardness.ActualSourceStarGlobalCompleteness

/-!
The uniform source-star law does not meet the modified-PCP reciprocal.

`restricted_acceptanceMass_eq_one` gives acceptance mass `1` for every
global linear functional, including zero. For every large `L`,
`modifiedPcpDenom` is at least `2`, so that mass is strictly above
`1 / modifiedPcpDenom`.

The reciprocal bound therefore cannot quantify over every labeling of
this law. It remains a statement about a 3CNF-reading, side-conditioned
family, which is not constructed here. `hSrcCmmsa` stays.
-/
namespace PvNP.RealizableHardness.ActualSourceStarMassCeiling

open ActualSourceStarGlobalCompleteness
open ActualSourceStarLaw
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualCmmsaAdmissibilitySelector

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {t d : Nat}

theorem modifiedPcpDenom_gt_one {L m : Nat} (hm : 2 ≤ m) (hh : 1 ≤ hBlock L m / m) :
    1 < modifiedPcpDenom L m := by
  have hm2 : 1 ≤ m ^ 2 - 1 := by
    have h4 : 4 ≤ m * m := Nat.mul_le_mul hm hm
    have : m ^ 2 = m * m := Nat.pow_two m
    omega
  have hexp : 1 ≤ 2 * (hBlock L m / m) * (m ^ 2 - 1) := by
    have h2 : 2 ≤ 2 * (hBlock L m / m) := Nat.mul_le_mul_left 2 hh
    have hpos : 0 < m ^ 2 - 1 := by omega
    have hmul : 2 * (hBlock L m / m) ≤ 2 * (hBlock L m / m) * (m ^ 2 - 1) :=
      Nat.le_mul_of_pos_right (2 * (hBlock L m / m)) hpos
    exact (by decide : 1 ≤ 2).trans (h2.trans hmul)

  have hpow : 2 ^ 1 ≤ 2 ^ (2 * (hBlock L m / m) * (m ^ 2 - 1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have hden : 2 ≤ modifiedPcpDenom L m := by
    simpa [modifiedPcpDenom] using hpow
  omega

/-- For every large `L`, a global functional's acceptance mass is strictly
above the modified-PCP reciprocal. -/
theorem restricted_acceptance_exceeds_modified_pcp_large
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (F : V →ₗ[ZMod 2] ZMod 2) :
    ∃ L0, ∀ L, L0 ≤ L →
      ¬ acceptanceMass (V := V) (t := t) (d := d) htd hdV (certifiedM L)
          (restrictedCenter (t := t) F) (restrictedLeaf (d := d) F) ≤
        ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, hM, _⟩ := hL0 L hL
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have hsrc : manuscriptSourceFloor m ≤ hBlock L m := hAd.2.2.2.2.2.2.2.1
  have hfloor : m + 2 ≤ hBlock L m := by
    simpa [manuscriptSourceFloor] using hsrc
  have hq : 2 ≤ hBlock L m / m := by
    by_contra hlt
    have hle : hBlock L m ≤ m := by
      calc
        hBlock L m = (hBlock L m / m) * m := (Nat.div_mul_cancel hdiv).symm
        _ ≤ 1 * m := Nat.mul_le_mul_right m (by omega)
        _ = m := by simp
    omega
  have hden : 1 < modifiedPcpDenom L (certifiedM L) := by
    rw [hM]
    exact modifiedPcpDenom_gt_one (le_trans (by decide : 2 ≤ 256) hm256)
      (le_trans (by decide : 1 ≤ 2) hq)
  have hmass :=
    restricted_acceptanceMass_eq_one (V := V) (t := t) (d := d)
      (m := certifiedM L) htd hdV F
  intro hle
  rw [hmass] at hle
  have hpos : (0 : Rat) < (modifiedPcpDenom L (certifiedM L) : Rat) := by
    exact_mod_cast (Nat.zero_lt_of_lt hden)
  have hone : (0 : Rat) < 1 := by norm_num
  have hcast : (1 : Rat) < (modifiedPcpDenom L (certifiedM L) : Rat) := by
    exact_mod_cast hden
  have hinv : ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ < (1 : Rat)⁻¹ :=
    (inv_lt_inv₀ hpos hone).mpr hcast
  have hinv1 : ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ < 1 := by
    simpa using hinv
  exact not_le_of_gt hinv1 hle

end

end PvNP.RealizableHardness.ActualSourceStarMassCeiling
