import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Manuscript `(σ_L, γ_L)` eventually passes both proved endpoints.

`γ_L` falls strictly below `3/4`, which is the list-decoding satisfaction
cap of `witness_mass_le_three_quarters`. Whenever `1 ≤ σ_L`, the headline
value is at least `2`, so a second uniform symbol fits in `σ_L` times a
one-hot budget.

This file does not construct `MapReducesVia` and does not prove Theorem 1
or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualManuscriptGapObstruction

open ActualHeadlineParameters

theorem rofSigma_ge_two_of_one {L : Nat} (h : 1 ≤ rofSigma L) : 2 ≤ rofSigma L := by
  have h8 : rofSigma L = ROf L / 8 := by
    simpa [rofSigma] using Nat.div_div_eq_div_mul (ROf L) 4 2
  rw [h8] at h ⊢
  have hR : ROf L = 2 ^ (2 * hOf L (mOf L)) := rfl
  rw [hR] at h ⊢
  set e := 2 * hOf L (mOf L) with _he
  by_cases h2 : 2 ≤ hOf L (mOf L)
  · have he4 : 4 ≤ e := by omega
    have hpow : 2 ^ 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) he4
    have hmul : 2 * 8 ≤ 2 ^ e := by
      calc
        2 * 8 = 2 ^ 4 := by decide
        _ ≤ 2 ^ e := hpow
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr hmul
  · have hlt : hOf L (mOf L) ≤ 1 := by omega
    have he2 : e ≤ 2 := by omega
    have hpow : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide : 0 < 2) he2
    have h4 : 2 ^ e ≤ 4 := by
      have h22 : 2 ^ 2 = 4 := by decide
      rwa [h22] at hpow
    have hlt8 : 2 ^ e < 8 := lt_of_le_of_lt h4 (by decide : 4 < 8)
    have hzero : 2 ^ e / 8 = 0 := Nat.div_eq_of_lt hlt8
    omega

theorem manuscript_gamma_eventually_lt_three_quarters :
    ∃ L0, ∀ L, L0 ≤ L → gammaL L < 3 / 4 :=
  gammaL_small_eventual (3 / 4) (by norm_num)

/-- Manuscript `γ_L` eventually lies strictly below the list-decoding cap `3/4`.
A proved satisfaction bound of `≤ 3/4` therefore does not discharge `No`
at `manuscriptGamma`. -/
theorem manuscriptGamma_eventually_lt_three_quarters :
    ∃ L0, ∀ L, L0 ≤ L → manuscriptGamma L < 3 / 4 := by
  simpa [manuscriptGamma] using
    ActualCertifiedManuscriptParameters.certifiedGamma_small_eventual
      (3 / 4) (by norm_num)

theorem manuscript_large_gap_parameters :
    ∃ L0, ∀ L, L0 ≤ L →
      (1 ≤ rofSigma L → 2 ≤ rofSigma L) ∧ gammaL L < 3 / 4 := by
  obtain ⟨Lγ, hγ⟩ := manuscript_gamma_eventually_lt_three_quarters
  refine ⟨Lγ, ?_⟩
  intro L hL
  exact ⟨fun hσ => rofSigma_ge_two_of_one hσ, hγ L hL⟩

end PvNP.RealizableHardness.ActualManuscriptGapObstruction
