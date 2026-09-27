import PvNP.RealizableHardness.ActualDinurShrinkingCeiling

/-!
An `L`-fold power of the fixed Dinur acceptance ceiling lies strictly below
`manuscriptGamma` for every large leaf bound.

`cmmsaPromise`'s no-side asks for satisfaction `< manuscriptGamma`, and that
gamma tends to `0`. The leaf-length power meets that numerical bound.

This file does not build a `SeededMap`, does not encode a gap-graph edge as
a formula of at most `L` leaves, and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGapPowerBelowGamma

open Complexity
open Dinur
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open ActualCmmsaParameterReconciliation

set_option autoImplicit false

theorem half_pow_le_four_mul_three_quarters (k : Nat) :
    ((1 : Rat) / 2) ^ k ≤ 4 * ((3 : Rat) / 4) ^ k := by
  have hone : (1 : Rat) ≤ ((3 : Rat) / 2) ^ k :=
    one_le_pow₀ (by norm_num : (1 : Rat) ≤ 3 / 2)
  have hcoef : (1 : Rat) ≤ 4 * ((3 : Rat) / 2) ^ k := by
    have hmul :=
      mul_le_mul (by norm_num : (1 : Rat) ≤ 4) hone
        (by norm_num : (0 : Rat) ≤ 1) (by norm_num : (0 : Rat) ≤ 4)
    simpa using hmul
  calc
    ((1 : Rat) / 2) ^ k = (1 : Rat) * ((1 : Rat) / 2) ^ k := by ring
    _ ≤ (4 * ((3 : Rat) / 2) ^ k) * ((1 : Rat) / 2) ^ k :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 4 * (((3 : Rat) / 2) ^ k * ((1 : Rat) / 2) ^ k) := by ring
    _ = 4 * ((3 : Rat) / 4) ^ k := by
      rw [← mul_pow]
      norm_num

private theorem sqrt_le_self {n : Nat} (hn : 1 ≤ n) : Nat.sqrt n ≤ n := by
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  cases hsqrt : Nat.sqrt n with
  | zero => simp
  | succ s =>
      rw [hsqrt] at hsq
      have hpos : 1 ≤ s + 1 := by omega
      have hmul : s + 1 ≤ (s + 1) * (s + 1) := Nat.le_mul_of_pos_right _ hpos
      exact hmul.trans hsq

private theorem two_pow_ge_mul_self (n : Nat) (hn : 4 ≤ n) : n * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      have htwo : 2 * n + 1 ≤ 2 ^ n := by
        have hsq : n * n ≤ 2 ^ n := ih
        have hlin : 2 * n + 1 ≤ n * n := by
          have : 4 ≤ n := hn
          nlinarith
        exact hlin.trans hsq
      calc
        (n + 1) * (n + 1) = n * n + (2 * n + 1) := by ring
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih htwo
        _ = 2 ^ (n + 1) := by rw [← two_mul, Nat.mul_comm, ← pow_succ]

private theorem mul_log_le (n : Nat) (hn : 1 ≤ n) :
    ∃ L0, ∀ L, L0 ≤ L → n * Nat.log 2 L ≤ L := by
  refine ⟨2 ^ (n + 2), ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (Nat.two_pow_pos (n + 2)) hL
  have hpow : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 hLpos.ne'
  have hk : n + 2 ≤ Nat.log 2 L :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 2) hLpos.ne').2 hL
  have hbase : n * (n + 2) ≤ 2 ^ (n + 2) := by
    by_cases h4 : 4 ≤ n
    · have hnn : n * n ≤ 2 ^ n := two_pow_ge_mul_self n h4
      have h2n : 2 * n ≤ 2 ^ n := by
        have : 2 * n ≤ n * n := by nlinarith
        exact this.trans hnn
      calc
        n * (n + 2) = n * n + 2 * n := by ring
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add hnn h2n
        _ = 2 ^ (n + 1) := by rw [← two_mul, Nat.mul_comm, ← pow_succ]
        _ ≤ 2 ^ (n + 2) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ _)
    · have hlt : n < 4 := Nat.lt_of_not_ge h4
      interval_cases n <;> decide
  have hstep : ∀ k, n + 2 ≤ k → n * k ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
        have hge : n ≤ 2 ^ k := by
          have hpowk : 2 ^ (n + 2) ≤ 2 ^ k :=
            Nat.pow_le_pow_right (by decide : 0 < 2) hk
          have hn2 : n ≤ 2 ^ (n + 2) := by
            calc
              n ≤ n * (n + 2) := Nat.le_mul_of_pos_right n (by omega)
              _ ≤ 2 ^ (n + 2) := hbase
          exact hn2.trans hpowk
        calc
          n * (k + 1) = n * k + n := by ring
          _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add ih hge
          _ = 2 ^ (k + 1) := by rw [← two_mul, Nat.mul_comm, ← pow_succ]
  exact (hstep _ hk).trans hpow

/-- For every large `L`, `(1 - amplifier.gap) ^ L < manuscriptGamma L`. -/
theorem gap_leaf_power_lt_manuscriptGamma (F : FinBase) (hd : 1 < F.deg) :
    ∃ L0, ∀ L, L0 ≤ L →
      (1 - (amplifier (F.toFamily hd)).gap) ^ L < manuscriptGamma L := by
  set r : Rat := 1 - (amplifier (F.toFamily hd)).gap
  have hr0 : 0 ≤ r := by
    have hle : (amplifier (F.toFamily hd)).gap ≤ 1 :=
      (amplifier (F.toFamily hd)).gap_le_one
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    have hg : 0 < (amplifier (F.toFamily hd)).gap :=
      (amplifier (F.toFamily hd)).gap_pos
    dsimp [r]
    linarith
  have hrle : r ≤ 1 := le_of_lt hr1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : Rat) < 1 / 2) hr1
  have hn1 : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    simp [hn0, pow_zero] at hn
    norm_num at hn
  obtain ⟨Llog, hlog⟩ := mul_log_le n hn1
  obtain ⟨Lp, hp⟩ := certified_parameters_eventually 256
  refine ⟨max Llog Lp, ?_⟩
  intro L hL
  have hLlog : Llog ≤ L := le_trans (Nat.le_max_left _ _) hL
  have hLp : Lp ≤ L := le_trans (Nat.le_max_right _ _) hL
  obtain ⟨m, _hsel, hm256, hAd, hM, _⟩ := hp L hLp
  have hLpos : 0 < L := by
    have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 256) hm256
    have hden : 0 < ActualCmmsaParameterReconciliation.q m * (m + 1) := by
      have hq : 0 < ActualCmmsaParameterReconciliation.q m :=
        Nat.sqrt_pos.2 hmpos
      exact Nat.mul_pos hq (Nat.succ_pos m)
    have hlt : ActualCmmsaParameterReconciliation.q m * (m + 1) < L := hAd.2.2.2.1
    exact hden.trans hlt
  have hL2 : 2 ≤ L := by
    have hlt : ActualCmmsaParameterReconciliation.q m * (m + 1) < L := hAd.2.2.2.1
    have hq16 : 16 ≤ ActualCmmsaParameterReconciliation.q m :=
      Nat.le_sqrt.mpr (by simpa [Nat.pow_two] using hm256)
    have hm1 : 257 ≤ m + 1 := by omega
    have hbig : 16 * 257 ≤ ActualCmmsaParameterReconciliation.q m * (m + 1) :=
      Nat.mul_le_mul hq16 hm1
    omega
  set k := Nat.sqrt (Nat.log 2 L)
  have hlogeq : ActualCmmsaParameterReconciliation.log2nat L = Nat.log 2 L := by
    simp [ActualCmmsaParameterReconciliation.log2nat, hLpos.ne']
  have hmle : m ≤ k := by
    have hm : m ≤ Nat.sqrt (ActualCmmsaParameterReconciliation.log2nat L) := hAd.2.1
    simpa [k, hlogeq] using hm
  have hsqrt : Nat.sqrt m ≤ k := (sqrt_le_self (by omega : 1 ≤ m)).trans hmle
  have hklog : k ≤ Nat.log 2 L := by
    have hlog1 : 1 ≤ Nat.log 2 L :=
      Nat.succ_le_of_lt (Nat.log_pos (by decide : 1 < 2) hL2)
    simpa [k] using sqrt_le_self hlog1
  have hnk : n * k ≤ L := (Nat.mul_le_mul_left n hklog).trans (hlog L hLlog)
  have hq : k ≤ L / n :=
    (Nat.le_div_iff_mul_le hn1).2 (by simpa [Nat.mul_comm] using hnk)
  have hqn : 0 < L / n := by
    have hk1 : 0 < k := by
      have hlog1 : 0 < Nat.log 2 L := Nat.log_pos (by decide : 1 < 2) hL2
      exact Nat.sqrt_pos.2 hlog1
    exact hk1.trans_le hq
  have hdiv : n * (L / n) ≤ L := Nat.mul_div_le L n
  have hrpow : r ^ L ≤ r ^ (n * (L / n)) :=
    pow_le_pow_of_le_one hr0 hrle hdiv
  have hsplit : r ^ (n * (L / n)) = (r ^ n) ^ (L / n) := pow_mul r n (L / n)
  have hlt : (r ^ n) ^ (L / n) < ((1 : Rat) / 2) ^ (L / n) :=
    pow_lt_pow_left₀ hn (by positivity) hqn.ne'
  have hpow : r ^ L < ((1 : Rat) / 2) ^ (L / n) := by
    apply lt_of_le_of_lt hrpow
    rw [hsplit]
    exact hlt
  have hhalf : ((1 : Rat) / 2) ^ (L / n) ≤ ((1 : Rat) / 2) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hfour : ((1 : Rat) / 2) ^ k ≤ 4 * ((3 : Rat) / 4) ^ k :=
    half_pow_le_four_mul_three_quarters k
  have hγ : 4 * ((3 : Rat) / 4) ^ k ≤ manuscriptGamma L := by
    have hγeq : manuscriptGamma L = 4 * ((3 : Rat) / 4) ^ Nat.sqrt m := by
      rw [manuscriptGamma, certifiedGamma, hM, gammaFinal_eq]
      simp [ActualCmmsaParameterReconciliation.q]
    rw [hγeq]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hsqrt) (by norm_num)
  calc
    r ^ L < ((1 : Rat) / 2) ^ (L / n) := hpow
    _ ≤ ((1 : Rat) / 2) ^ k := hhalf
    _ ≤ 4 * ((3 : Rat) / 4) ^ k := hfour
    _ ≤ manuscriptGamma L := hγ

end PvNP.RealizableHardness.ActualGapPowerBelowGamma
