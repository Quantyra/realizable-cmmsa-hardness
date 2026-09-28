import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
The Grassmann block alphabet is larger than manuscript `σ_L`.

On an admissible block, `RBlock = 2^(2 h)` and
`manuscriptSigma = 2^(2 (h/m) (m-1) - 7)`. Because `m ∣ h` and
`h/m ≥ 2`, the exponent gap is at least `11`, so

`manuscriptSigma * 2^11 ≤ RBlock`.

A uniform one-hot budget `1 / RBlock` therefore puts the all-true
assignment, whose normalized cost is `1`, strictly outside the
`manuscriptSigma` ball. `not_no_of_uniform_one_hot_budget` does not
apply to this alphabet. This file does not build a star family, a
`SeededMap`, or a 3CNF encoding, and it does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannAlphabetRoom

open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualCmmsaAdmissibilitySelector
open ActualHeadlineParameters

set_option autoImplicit false

noncomputable section

theorem rBlock_clears_manuscriptSigma :
    ∃ L0, ∀ L, L0 ≤ L →
      manuscriptSigma L * 2 ^ 11 ≤ RBlock L (certifiedM L) ∧
      (manuscriptSigma L : Rat) / (RBlock L (certifiedM L) : Rat) < 1 := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, hM, hσ⟩ := hL0 L hL
  have hmpos : 0 < m := by omega
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
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
  obtain ⟨he7, hσpow⟩ := sigmaFinal_two_pow hmpos hdiv h8
  set qh := hBlock L m / m
  set e := 2 * qh * (m - 1)
  have hhm : hBlock L m = qh * m := by
    simpa [qh] using (Nat.div_mul_cancel hdiv).symm
  have hmstep : m = (m - 1) + 1 := by omega
  have hexp : 2 * hBlock L m = e + 2 * qh := by
    have h2 : 2 * hBlock L m = 2 * (qh * m) := by rw [hhm]
    have hassoc : 2 * (qh * m) = 2 * qh * m := (Nat.mul_assoc 2 qh m).symm
    have hstep : 2 * qh * m = 2 * qh * ((m - 1) + 1) :=
      congrArg (fun t => 2 * qh * t) hmstep
    have hadd : 2 * qh * ((m - 1) + 1) = 2 * qh * (m - 1) + 2 * qh * 1 :=
      Nat.mul_add (2 * qh) (m - 1) 1
    have hone : 2 * qh * (m - 1) + 2 * qh * 1 = 2 * qh * (m - 1) + 2 * qh := by
      rw [Nat.mul_one]
    have heq : 2 * qh * (m - 1) + 2 * qh = e + 2 * qh := by
      simp [e, Nat.mul_assoc]
    exact h2.trans (hassoc.trans (hstep.trans (hadd.trans (hone.trans heq))))
  have hfour : 4 ≤ 2 * qh := by
    have : 2 * 2 ≤ 2 * qh := by
      simpa [qh] using Nat.mul_le_mul_left 2 hq
    simpa using this
  have hleExp : (e - 7) + 11 ≤ 2 * hBlock L m := by
    rw [hexp]
    omega
  have hpowLe :
      2 ^ ((e - 7) + 11) ≤ 2 ^ (2 * hBlock L m) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hleExp
  have hsplit : 2 ^ ((e - 7) + 11) = 2 ^ (e - 7) * 2 ^ 11 :=
    Nat.pow_add 2 (e - 7) 11
  have hmul : sigmaFinal L m * 2 ^ 11 ≤ RBlock L m := by
    rw [hσpow, RBlock]
    simpa [hsplit] using hpowLe
  have hσpos : 0 < sigmaFinal L m := by
    rw [hσpow]
    exact Nat.two_pow_pos _
  refine ⟨?_, ?_⟩
  · simpa [manuscriptSigma, hσ, hM] using hmul
  · have hcast :
        (sigmaFinal L m : Rat) * ((2 : Rat) ^ 11) ≤ (RBlock L m : Rat) := by
      have hnatCast :
          (sigmaFinal L m : Rat) * (2 ^ 11 : Rat) ≤ (RBlock L m : Rat) := by
        exact_mod_cast hmul
      simpa [Nat.cast_pow] using hnatCast
    have hposR : (0 : Rat) < (RBlock L m : Rat) := by
      exact_mod_cast (Nat.two_pow_pos (2 * hBlock L m) : 0 < RBlock L m)
    have hposσ : (0 : Rat) < (sigmaFinal L m : Rat) := by
      exact_mod_cast hσpos
    have hposDen : (0 : Rat) < (sigmaFinal L m : Rat) * ((2 : Rat) ^ 11) :=
      mul_pos hposσ (by norm_num)
    have hinv :
        ((RBlock L m : Rat))⁻¹ ≤
          ((sigmaFinal L m : Rat) * ((2 : Rat) ^ 11))⁻¹ :=
      (inv_le_inv₀ hposR hposDen).mpr hcast
    have hratio :
        (sigmaFinal L m : Rat) / (RBlock L m : Rat) ≤
          ((2 : Rat) ^ 11)⁻¹ := by
      rw [div_eq_mul_inv]
      have hmulInv :
          (sigmaFinal L m : Rat) * ((RBlock L m : Rat))⁻¹ ≤
            (sigmaFinal L m : Rat) *
              ((sigmaFinal L m : Rat) * ((2 : Rat) ^ 11))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hposσ.le
      have hcancel :
          (sigmaFinal L m : Rat) *
              ((sigmaFinal L m : Rat) * ((2 : Rat) ^ 11))⁻¹ =
            ((2 : Rat) ^ 11)⁻¹ := by
        have hne : (sigmaFinal L m : Rat) ≠ 0 := hposσ.ne'
        field_simp [hne]
      exact hmulInv.trans (le_of_eq hcancel)
    have hsmall : ((2 : Rat) ^ 11)⁻¹ < 1 := by
      rw [inv_lt_one₀ (by norm_num : (0 : Rat) < (2 : Rat) ^ 11)]
      norm_num
    have hlt : (sigmaFinal L m : Rat) / (RBlock L m : Rat) < 1 :=
      lt_of_le_of_lt hratio hsmall
    simpa [manuscriptSigma, hσ, hM] using hlt

end

end PvNP.RealizableHardness.ActualGrassmannAlphabetRoom
