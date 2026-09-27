import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Manuscript `(σ_L, γ_L)` eventually passes both proved endpoints.

`γ_L` falls strictly below `3/4`, which is the list-decoding satisfaction
cap of `witness_mass_le_three_quarters`. Whenever `1 ≤ σ_L`, the headline
value is at least `2`, so a second uniform symbol fits in `σ_L` times a
one-hot budget.

A fixed positive CSP-value ceiling misses the manuscript HN endpoint
`(8 σ_L)^{m+1} ζ ≤ 5/8` once `L` is large. That is the numerical room a
soundness proof has to beat. This file does not construct that soundness,
does not construct `MapReducesVia`, and does not prove Theorem 1 or
Corollary 2.
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

/-- A fixed positive CSP ceiling misses the manuscript HN endpoint.
`witness_mass_le_three_quarters` asks for `(8ρ)^{arity+1} ζ ≤ 5/8`.
At `ρ = manuscriptSigma` and arity `certifiedM`, every `ζ = c > 0` fails
that bound for all large `L`. -/
theorem constant_csp_ceiling_misses_manuscript_hn (c : Rat) (hc : 0 < c) :
    ∃ L0, ∀ L, L0 ≤ L →
      ¬ ((8 : Rat) * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1) * c
        ≤ (5 : Rat) / 8 := by
  have hsmall : (0 : Rat) < (8 * c) / 5 :=
    div_pos (mul_pos (by norm_num) hc) (by norm_num)
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one hsmall (by norm_num : ((1 : Rat) / 16) < 1)
  obtain ⟨Lσ, hσ⟩ :=
    ActualCertifiedManuscriptParameters.certifiedSigma_ge_two_eventual
  obtain ⟨Lm, hm⟩ :=
    ActualCertifiedManuscriptParameters.certified_parameters_eventually k
  refine ⟨max Lσ Lm, ?_⟩
  intro L hL
  have hσ2 : 2 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hσ L (le_trans (Nat.le_max_left _ _) hL)
  obtain ⟨_m, _hsel, hmk, _hAd, hM, _hsig⟩ :=
    hm L (le_trans (Nat.le_max_right _ _) hL)
  have hcert :
      k ≤ ActualCertifiedManuscriptParameters.certifiedM L := by
    simpa [hM] using hmk
  have hbase : (16 : Rat) ≤ 8 * (manuscriptSigma L : Rat) := by
    have h2 : (2 : Rat) ≤ (manuscriptSigma L : Rat) := by exact_mod_cast hσ2
    linarith
  have hexp :
      k + 1 ≤ ActualCertifiedManuscriptParameters.certifiedM L + 1 := by
    omega
  have hpow16 :
      (16 : Rat) ^ (k + 1) ≤
        (16 : Rat) ^ (ActualCertifiedManuscriptParameters.certifiedM L + 1) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hpow :
      (16 : Rat) ^ (ActualCertifiedManuscriptParameters.certifiedM L + 1) ≤
        (8 * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1) :=
    pow_le_pow_left₀ (by norm_num) hbase _
  have hkc : (5 : Rat) / 8 < (16 : Rat) ^ k * c := by
    have hone : (1 : Rat) / (16 : Rat) ^ k < (8 * c) / 5 := by
      simpa [div_pow] using hk
    have hden : (0 : Rat) < (16 : Rat) ^ k := pow_pos (by norm_num) k
    have h1 : (1 : Rat) < (8 * c) / 5 * (16 : Rat) ^ k :=
      (div_lt_iff₀ hden).mp hone
    have h5 : (5 : Rat) < (8 * c) * (16 : Rat) ^ k := by
      have hmul := mul_lt_mul_of_pos_left h1 (by norm_num : (0 : Rat) < 5)
      have hrew :
          (5 : Rat) * ((8 * c) / 5 * (16 : Rat) ^ k) =
            (8 * c) * (16 : Rat) ^ k := by ring
      simpa [hrew] using hmul
    rw [div_lt_iff₀ (by norm_num : (0 : Rat) < 8)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using h5
  have hstep : (5 : Rat) / 8 < (16 : Rat) ^ (k + 1) * c := by
    calc
      (5 : Rat) / 8 < 10 := by norm_num
      _ = 16 * ((5 : Rat) / 8) := by norm_num
      _ < 16 * ((16 : Rat) ^ k * c) :=
        mul_lt_mul_of_pos_left hkc (by norm_num)
      _ = (16 : Rat) ^ (k + 1) * c := by ring
  have hbig :
      (5 : Rat) / 8 <
        (8 * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1) * c := by
    calc
      (5 : Rat) / 8 < (16 : Rat) ^ (k + 1) * c := hstep
      _ ≤ (16 : Rat) ^ (ActualCertifiedManuscriptParameters.certifiedM L + 1) * c :=
        mul_le_mul_of_nonneg_right hpow16 hc.le
      _ ≤ (8 * (manuscriptSigma L : Rat)) ^
            (ActualCertifiedManuscriptParameters.certifiedM L + 1) * c :=
        mul_le_mul_of_nonneg_right hpow hc.le
  exact not_le_of_gt hbig

end PvNP.RealizableHardness.ActualManuscriptGapObstruction
