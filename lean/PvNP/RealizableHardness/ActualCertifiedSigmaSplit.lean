import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Headline `rofSigma` is `(ROf/4)/2`. The manuscript family is `certifiedSigma`,
the `/16`, `/4`, `/2` chain. At `L = 2^20` those values are `32768` and `0`.

`certifiedSigma` is eventually at least `2`, so a second uniform symbol still
fits in `σ` times a one-hot budget for every large leaf. This file does not
rewrite `rofSigma`, does not construct an `FP` `MapReducesVia`, and does not
prove Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualCertifiedSigmaSplit

open PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

theorem log_two_pow_twenty : Nat.log 2 (2 ^ 20) = 20 :=
  Nat.log_eq_of_pow_le_of_lt_pow (le_rfl : 2 ^ 20 ≤ 2 ^ 20)
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 20 < 21))

theorem log2nat_two_pow_twenty :
    ActualHeadlineParameters.log2nat (2 ^ 20) = 20 := by
  simp only [ActualHeadlineParameters.log2nat, if_neg (by decide : 2 ^ 20 ≠ 0)]
  exact log_two_pow_twenty

theorem sqrt_twenty : Nat.sqrt 20 = 4 :=
  ((Nat.eq_sqrt (n := 20) (a := 4)).mpr ⟨by decide, by decide⟩).symm

theorem mOf_two_pow_twenty : ActualHeadlineParameters.mOf (2 ^ 20) = 0 := by
  unfold ActualHeadlineParameters.mOf
  rw [log2nat_two_pow_twenty, sqrt_twenty]
  decide

theorem log_two_pow_twenty_sub_one : Nat.log 2 (2 ^ 20 - 1) = 19 := by
  have hle : 2 ^ 19 ≤ 2 ^ 20 - 1 := by
    have hsum : 2 ^ 19 + 2 ^ 19 = 2 ^ 20 := by
      rw [← Nat.two_mul, ← pow_succ']
    omega
  have hlt : 2 ^ 20 - 1 < 2 ^ (19 + 1) := by
    exact Nat.sub_lt (Nat.two_pow_pos 20) (by decide)
  exact Nat.log_eq_of_pow_le_of_lt_pow hle hlt

theorem hOf_two_pow_twenty : ActualHeadlineParameters.hOf (2 ^ 20) 0 = 9 := by
  unfold ActualHeadlineParameters.hOf ActualHeadlineParameters.qOf
  simp only [Nat.sqrt_zero]
  have hmax : Nat.max 0 1 = 1 := Nat.max_eq_right (by decide : 0 ≤ 1)
  rw [hmax]
  have hif :
      (if (2 ^ 20) = 0 then 0 else (2 ^ 20 - 1) / 1) = 2 ^ 20 - 1 := by
    decide
  rw [hif]
  have hlog : ActualHeadlineParameters.log2nat (2 ^ 20 - 1) = 19 := by
    simp only [ActualHeadlineParameters.log2nat,
      if_neg (by decide : 2 ^ 20 - 1 ≠ 0), log_two_pow_twenty_sub_one]
  rw [hlog]

theorem rofSigma_two_pow_twenty : ActualHeadlineParameters.rofSigma (2 ^ 20) = 32768 := by
  have hm : ActualHeadlineParameters.mOf (2 ^ 20) = 0 := mOf_two_pow_twenty
  have hh : ActualHeadlineParameters.hOf (2 ^ 20) 0 = 9 := hOf_two_pow_twenty
  unfold ActualHeadlineParameters.rofSigma ActualHeadlineParameters.ROf
  rw [hm, hh]
  decide

theorem selector_two_pow_twenty :
    selector manuscriptSourceFloor (2 ^ 20) = ⊥ := by
  rw [selector_eq_bot_iff]
  rintro ⟨m, hAd⟩
  have hm : 256 ≤ m := hAd.1
  have hsqrt : m ≤ Nat.sqrt (log2nat (2 ^ 20)) := hAd.2.1
  have hlog : log2nat (2 ^ 20) = 20 := by
    simp only [log2nat, if_neg (by decide : 2 ^ 20 ≠ 0)]
    exact log_two_pow_twenty
  rw [hlog, sqrt_twenty] at hsqrt
  omega

theorem sigmaFinal_zero : sigmaFinal (2 ^ 20) 0 = 0 := by
  simp [sigmaFinal, sigmaRepair, sigmaBase, gapRoot, hBlock, bOf]

theorem certifiedSigma_two_pow_twenty : certifiedSigma (2 ^ 20) = 0 := by
  unfold certifiedSigma certifiedM
  rw [selector_two_pow_twenty]
  have hget : (⊥ : WithBot Nat).getD 0 = 0 := rfl
  rw [hget]
  exact sigmaFinal_zero

theorem rofSigma_ne_certifiedSigma :
    ActualHeadlineParameters.rofSigma (2 ^ 20) ≠ certifiedSigma (2 ^ 20) := by
  rw [rofSigma_two_pow_twenty, certifiedSigma_two_pow_twenty]
  decide

theorem certified_family_still_large_gap :
    ∃ L0, ∀ L, L0 ≤ L → 2 ≤ certifiedSigma L ∧ certifiedGamma L < 3 / 4 := by
  obtain ⟨Lσ, hσ⟩ := certifiedSigma_ge_two_eventual
  obtain ⟨Lγ, hγ⟩ := certifiedGamma_small_eventual (3 / 4) (by norm_num)
  refine ⟨max Lσ Lγ, ?_⟩
  intro L hL
  exact ⟨hσ L (le_trans (Nat.le_max_left _ _) hL),
    hγ L (le_trans (Nat.le_max_right _ _) hL)⟩

end PvNP.RealizableHardness.ActualCertifiedSigmaSplit
