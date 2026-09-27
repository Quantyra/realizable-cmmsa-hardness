import PvNP.RealizableHardness.ActualFpMapInterface

/-!
Dinur-style repetition versus the manuscript HN exponent.

`compiledSatisfaction_le_three_quarters` needs
`(8 ρ)^{arity + 1} ζ ≤ 5/8`. At `ρ = manuscriptSigma L` and a score ceiling
`r ^ t` with `1/2 ≤ r`, matching the arity to the repetition count makes the
product larger than `5/8` for every `t`. The same ceiling does fall under
`5/8` when the arity stays `certifiedM L` and `t` is chosen in the proof,
provided `r < 1`.

Neither statement builds a star family, a `SeededMap`, or a `Preserves (1/6)`
map. `theorem1_realizable_cmmsa` still takes `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualDinurArityGap

open ActualCertifiedManuscriptParameters
open ActualFpMapInterface
open ActualHeadlineParameters

set_option autoImplicit false

theorem half_base_repetition_misses_hn
    (r : ℚ) (hr : (1 : ℚ) / 2 ≤ r) :
    ∃ L0, ∀ L, L0 ≤ L → ∀ t : ℕ,
      ¬ ((8 * (manuscriptSigma L : ℚ)) ^ (t + 1) * r ^ t ≤ (5 : ℚ) / 8) := by
  obtain ⟨L0, hL0⟩ := manuscriptSigma_ge_pow1013
  refine ⟨L0, ?_⟩
  intro L hL t hle
  have hσnat : 2 ^ 1013 ≤ manuscriptSigma L := hL0 L hL
  set s : ℚ := 8 * (manuscriptSigma L : ℚ)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    positivity
  have honeσ : (1 : ℚ) ≤ (manuscriptSigma L : ℚ) := by
    exact_mod_cast (le_trans (Nat.one_le_two_pow : (1 : ℕ) ≤ 2 ^ 1013) hσnat)
  have hs1 : (1 : ℚ) ≤ s := by
    dsimp [s]
    nlinarith
  have hsr : (1 : ℚ) ≤ s * r := by
    have hhalf : (1 : ℚ) ≤ s * ((1 : ℚ) / 2) := by
      nlinarith
    exact le_trans hhalf (mul_le_mul_of_nonneg_left hr hs0)
  have hpow : (1 : ℚ) ≤ (s * r) ^ t := one_le_pow₀ (n := t) hsr
  have hfactor : s ^ (t + 1) * r ^ t = (s * r) ^ t * s := by
    rw [pow_succ]
    have hcomm : s ^ t * s * r ^ t = s ^ t * r ^ t * s := by ring
    rw [hcomm, ← mul_pow]
  have hlower : s ≤ s ^ (t + 1) * r ^ t := by
    rw [hfactor]
    calc
      s = 1 * s := by ring
      _ ≤ (s * r) ^ t * s := mul_le_mul_of_nonneg_right hpow hs0
  have h58 : (5 : ℚ) / 8 < 1 := by norm_num
  have hgt : (5 : ℚ) / 8 < s ^ (t + 1) * r ^ t :=
    lt_of_lt_of_le (h58.trans_le hs1) hlower
  exact not_le_of_gt hgt hle

theorem fixed_arity_base_meets_hn
    (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ t : ℕ,
        (8 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) * r ^ t ≤
          (5 : ℚ) / 8 := by
  obtain ⟨L0, hL0⟩ := manuscriptSigma_ge_pow1013
  refine ⟨L0, ?_⟩
  intro L hL
  have hσnat : 2 ^ 1013 ≤ manuscriptSigma L := hL0 L hL
  have hσpos : 0 < manuscriptSigma L :=
    lt_of_lt_of_le (Nat.two_pow_pos 1013) hσnat
  set s : ℚ := 8 * (manuscriptSigma L : ℚ)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hden : 0 < s ^ (certifiedM L + 1) := pow_pos hs _
  have hc : 0 < ((5 : ℚ) / 8) / s ^ (certifiedM L + 1) := div_pos (by norm_num) hden
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hc hr1
  refine ⟨t, ?_⟩
  have hrpow : r ^ t < ((5 : ℚ) / 8) / s ^ (certifiedM L + 1) := ht
  have hmul : s ^ (certifiedM L + 1) * r ^ t < (5 : ℚ) / 8 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hden).mp hrpow
  have _hr0 : 0 ≤ r ^ t := pow_nonneg hr0 t
  exact le_of_lt hmul

end PvNP.RealizableHardness.ActualDinurArityGap
