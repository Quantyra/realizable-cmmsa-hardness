import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Manuscript parameter family for Theorem 1 and Corollary 2.

`certifiedSigma` is the reconciled `/16`, `/4`, `/2` chain at the selected
block, not `(ROf/4)/2`. `certifiedAdviceLeaf` subtracts twice the ceiling
logarithm. The limit lemmas below are the manuscript parameter asymptotics.
This module does not construct the CMMSA reduction and does not prove
Theorem 1 or Corollary 2.
-/

namespace PvNP.RealizableHardness.ActualCertifiedManuscriptParameters

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector

def manuscriptSourceFloor (n : Nat) : Nat := n + 2

noncomputable def certifiedM (L : Nat) : Nat :=
  (selector manuscriptSourceFloor L).getD 0

noncomputable def certifiedSigma (L : Nat) : Nat :=
  sigmaFinal L (certifiedM L)

noncomputable def certifiedGamma (L : Nat) : Rat :=
  gammaFinal (certifiedM L)

/-- `L = a - 2⌈log₂(a+1)⌉ - c_U`. `Nat.clog 2` is that ceiling. -/
def certifiedAdviceLeaf (a cU : Nat) : Nat :=
  a - 2 * Nat.clog 2 (a + 1) - cU

/-- `⌊0.49 σ_L⌋` at the advice leaf. -/
noncomputable def certifiedSigmaLearn (a cU : Nat) : Nat :=
  (49 * certifiedSigma (certifiedAdviceLeaf a cU)) / 100

/-- Learning threshold `5 γ_L`. -/
noncomputable def certifiedGammaLearn (a cU : Nat) : Rat :=
  5 * certifiedGamma (certifiedAdviceLeaf a cU)

theorem certifiedAdviceLeaf_eq (a cU : Nat) :
    certifiedAdviceLeaf a cU = a - 2 * Nat.clog 2 (a + 1) - cU := rfl

theorem certifiedSigmaLearn_eq (a cU : Nat) :
    certifiedSigmaLearn a cU =
      (49 * certifiedSigma (certifiedAdviceLeaf a cU)) / 100 := rfl

theorem certifiedGammaLearn_eq (a cU : Nat) :
    certifiedGammaLearn a cU = 5 * certifiedGamma (certifiedAdviceLeaf a cU) := rfl

theorem certifiedM_of_selector {L m : Nat}
    (h : selector manuscriptSourceFloor L = (m : WithBot Nat)) :
    certifiedM L = m := by
  unfold certifiedM
  rw [h]
  rfl

theorem certifiedSigma_of_selector {L m : Nat}
    (h : selector manuscriptSourceFloor L = (m : WithBot Nat)) :
    certifiedSigma L = sigmaFinal L m := by
  simp [certifiedSigma, certifiedM_of_selector h]

theorem certified_parameters_eventually (M : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat, selector manuscriptSourceFloor L = (m : WithBot Nat) ∧
        M ≤ m ∧ Admissible manuscriptSourceFloor L m ∧
        certifiedM L = m ∧ certifiedSigma L = sigmaFinal L m := by
  obtain ⟨L0, hL0⟩ := selector_unbounded manuscriptSourceFloor M
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hsel, hM, hAd⟩ := hL0 L hL
  exact ⟨m, hsel, hM, hAd, certifiedM_of_selector hsel, certifiedSigma_of_selector hsel⟩

private theorem sigmaFinal_eq_pow {L m : Nat} (hm : 0 < m)
    (hdiv : m ∣ hBlock L m) (h8 : 8 ≤ sigmaBase L m) :
    let e := 2 * (hBlock L m / m) * (m - 1)
    7 ≤ e ∧ sigmaFinal L m = 2 ^ (e - 7) := by
  intro e
  have hgap : gapRoot L m = 2 ^ e := rfl
  have he4 : 4 ≤ e := by
    by_contra hlt
    have he : e < 4 := Nat.lt_of_not_ge hlt
    have hpow : 2 ^ e < 16 := by
      have : 2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Nat.le_pred_of_lt he)
      exact this.trans_lt (by decide)
    have hzero : gapRoot L m / 16 = 0 := by
      rw [hgap]
      exact Nat.div_eq_of_lt hpow
    have hσ : sigmaBase L m = 0 := by simpa [sigmaBase] using hzero
    omega
  have hbase : sigmaBase L m = 2 ^ (e - 4) := by
    simp only [sigmaBase, hgap]
    have hdiv16 : 2 ^ 4 ∣ 2 ^ e := Nat.pow_dvd_pow 2 he4
    rw [show (16 : Nat) = 2 ^ 4 by decide, Nat.pow_div he4 (by decide)]
  have he7 : 7 ≤ e := by
    have hge : 2 ^ 3 ≤ 2 ^ (e - 4) := by
      simpa [hbase] using h8
    have hle : 3 ≤ e - 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hge
    omega
  have hrepair : sigmaRepair L m = 2 ^ (e - 6) := by
    simp only [sigmaRepair, hbase]
    have hshift : e - 4 = (e - 6) + 2 := by omega
    rw [hshift, pow_add]
    have hfour : (2 : Nat) ^ 2 = 4 := by decide
    rw [hfour, Nat.mul_div_cancel _ (by decide : 0 < 4)]
  refine ⟨he7, ?_⟩
  simp only [sigmaFinal, hrepair]
  have hshift : e - 6 = (e - 7) + 1 := by omega
  rw [hshift, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem certifiedSigma_pos_le_log :
    ∃ L0, ∀ L, L0 ≤ L →
      0 < certifiedSigma L ∧ log2nat (certifiedSigma L) ≤ log2nat L := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _hsel, hm256, hAd, hm, hσ⟩ := hL0 L hL
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 256) hm256
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
  obtain ⟨_he7, hpow⟩ := sigmaFinal_eq_pow (L := L) (m := m) hmpos hdiv h8
  have hpos : 0 < certifiedSigma L := by
    rw [hσ, hpow]
    exact Nat.two_pow_pos _
  refine ⟨hpos, ?_⟩
  rw [hσ, hpow]
  have hlog : log2nat (2 ^ (2 * (hBlock L m / m) * (m - 1) - 7)) =
      2 * (hBlock L m / m) * (m - 1) - 7 := by
    rw [log2nat, if_neg (Nat.two_pow_pos _).ne', Nat.log_pow (by decide : 1 < 2)]
  rw [hlog]
  have h2h : 2 * hBlock L m ≤ log2nat (blockNum L m) :=
    two_mul_hBlock_le_log2_blockNum L m
  have hbn : blockNum L m ≤ L := by
    unfold blockNum
    split_ifs with hzero
    · exact Nat.zero_le _
    · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hnum : log2nat (blockNum L m) ≤ log2nat L := by
    unfold log2nat
    by_cases hb0 : blockNum L m = 0
    · simp [hb0]
    · have hLz : L ≠ 0 := by
        intro hLz
        have : blockNum L m = 0 := by simp [blockNum, hLz]
        exact hb0 this
      simp [hb0, hLz, Nat.log_mono_right hbn]
  have hmul : 2 * (hBlock L m / m) * (m - 1) ≤ 2 * hBlock L m := by
    have hstep : (hBlock L m / m) * (m - 1) ≤ hBlock L m := by
      calc
        (hBlock L m / m) * (m - 1) ≤ (hBlock L m / m) * m :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ hBlock L m := Nat.div_mul_le_self _ _
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 hstep
  exact ((Nat.sub_le _ 7).trans hmul).trans (h2h.trans hnum)

private lemma three_four_pow_pos (n : Nat) : (0 : Rat) < (3 / 4 : Rat) ^ n :=
  pow_pos (by norm_num) n

private lemma three_four_pow_six_lt : ((3 / 4 : Rat) ^ 6) < (1 / 4 : Rat) := by
  norm_num

private lemma q_ge_six {m : Nat} (hm : 36 ≤ m) : 6 ≤ q m :=
  Nat.le_sqrt.mpr (by simpa [Nat.pow_two] using hm)

theorem certifiedGamma_pos_lt_one_eventual :
    ∃ L0, ∀ L, L0 ≤ L → 0 < certifiedGamma L ∧ certifiedGamma L < 1 := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 36
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm36, _, hm, _⟩ := hL0 L hL
  have hq : 6 ≤ q m := q_ge_six hm36
  have hpow : ((3 / 4 : Rat) ^ q m) ≤ ((3 / 4 : Rat) ^ 6) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hlt : ((3 / 4 : Rat) ^ q m) < (1 / 4 : Rat) :=
    lt_of_le_of_lt hpow three_four_pow_six_lt
  have hγ : certifiedGamma L = 4 * ((3 / 4 : Rat) ^ q m) := by
    rw [certifiedGamma, hm, gammaFinal_eq]
  refine ⟨?_, ?_⟩
  · rw [hγ]
    exact mul_pos (by norm_num) (three_four_pow_pos _)
  · rw [hγ]
    nlinarith

theorem certifiedGamma_small_eventual (ε : Rat) (hε : 0 < ε) :
    ∃ L0, ∀ L, L0 ≤ L → certifiedGamma L < ε := by
  have hε4 : (0 : Rat) < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε4 (by norm_num : (3 / 4 : Rat) < 1)
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually (k * k)
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hmk, _, hm, _⟩ := hL0 L hL
  have hq : k ≤ q m := Nat.le_sqrt.mpr hmk
  have hpow : ((3 / 4 : Rat) ^ q m) ≤ ((3 / 4 : Rat) ^ k) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have h4 : 4 * ((3 / 4 : Rat) ^ q m) < ε := by
    have hle : 4 * ((3 / 4 : Rat) ^ q m) ≤ 4 * ((3 / 4 : Rat) ^ k) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hstrict : 4 * ((3 / 4 : Rat) ^ k) < 4 * (ε / 4) :=
      mul_lt_mul_of_pos_left hk (by norm_num)
    have hcancel : (4 : Rat) * (ε / 4) = ε := by ring
    exact lt_of_le_of_lt hle (hstrict.trans_eq hcancel)
  simpa [certifiedGamma, hm, gammaFinal_eq] using h4

private lemma clog_le_log_succ (n : Nat) (_hn : 0 < n) :
    Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
  apply Nat.clog_le_of_le_pow
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

private lemma self_le_two_pow (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left (Nat.one_le_pow k 2 (by decide)) _
      _ = 2 ^ (k + 1) := by rw [← two_mul, pow_succ']

private lemma succ_le_two_pow : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ m
  | 0, h => by omega
  | 1, _ => by decide
  | m + 2, _ => by
      have ih := succ_le_two_pow (m + 1) (by omega)
      calc
        m + 2 + 1 = m + 1 + 1 + 1 := by omega
        _ ≤ 2 ^ (m + 1) + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) :=
          Nat.add_le_add_left (Nat.one_le_pow (m + 1) 2 (by decide)) _
        _ = 2 ^ (m + 2) := by rw [← two_mul, ← pow_succ']

private lemma two_mul_succ_le_sq {t : Nat} (ht : 5 ≤ t) : 2 * t + 1 ≤ t * t := by
  have h3 : 3 ≤ t := by omega
  calc
    2 * t + 1 ≤ 3 * t := by omega
    _ ≤ t * t := Nat.mul_le_mul_right t h3

private lemma sq_lt_two_pow : ∀ t, 5 ≤ t → t * t < 2 ^ t
  | 0, h => by omega
  | t + 1, ht => by
      by_cases h5 : 5 ≤ t
      · have hih : t * t < 2 ^ t := sq_lt_two_pow t h5
        have hstep : 2 * t + 1 ≤ t * t := two_mul_succ_le_sq h5
        calc
          (t + 1) * (t + 1) = t * t + (2 * t + 1) := by ring
          _ ≤ t * t + t * t := Nat.add_le_add_left hstep _
          _ < 2 ^ t + 2 ^ t := Nat.add_lt_add hih hih
          _ = 2 ^ (t + 1) := by rw [← two_mul, pow_succ']
      · have ht4 : t = 4 := by omega
        subst ht4
        decide

/-- For every fixed advice overhead, the ceiling leaf is eventually at least
`a` minus a term `o(a)`, so `L / a → 1`. -/
theorem certifiedAdviceLeaf_gap (cU k : Nat) :
    ∃ a0, ∀ a, a0 ≤ a →
      2 * Nat.clog 2 (a + 1) + cU ≤ a ∧
      k * (a - certifiedAdviceLeaf a cU) ≤ a := by
  let t0 := 4 * k + cU + 8
  refine ⟨2 ^ t0, ?_⟩
  intro a ha
  have ht0_8 : 8 ≤ t0 := by
    dsimp [t0]
    omega
  have ht : t0 ≤ Nat.log 2 (a + 1) :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) (ha.trans (Nat.le_succ a))
  set t := Nat.log 2 (a + 1)
  have ht5 : 5 ≤ t := by omega
  have hc : cU ≤ t := by
    have hc0 : cU ≤ t0 := by
      dsimp [t0]
      omega
    exact hc0.trans ht
  have h4k : 4 * k ≤ t := by
    have hk0 : 4 * k ≤ t0 := by
      dsimp [t0]
      omega
    exact hk0.trans ht
  have hclog := clog_le_log_succ (a + 1) (Nat.succ_pos a)
  have hover_lin : 2 * Nat.clog 2 (a + 1) + cU ≤ 4 * t := by
    have hmul : 2 * Nat.clog 2 (a + 1) ≤ 2 * t + 2 := by
      have := Nat.mul_le_mul_left 2 hclog
      omega
    have hrest : 2 * t + 2 + cU ≤ 4 * t := by
      have ht2 : 2 ≤ t := by omega
      omega
    exact (Nat.add_le_add_right hmul cU).trans hrest
  have h4t : 4 * t ≤ t * t := Nat.mul_le_mul_right t (by omega : 4 ≤ t)
  have hsq : t * t < 2 ^ t := sq_lt_two_pow t ht5
  have hself : 2 ^ t ≤ a + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero a)
  have hoverhead : 2 * Nat.clog 2 (a + 1) + cU ≤ a := by
    have hlt : 2 * Nat.clog 2 (a + 1) + cU < a + 1 :=
      lt_of_le_of_lt hover_lin (lt_of_lt_of_le (lt_of_le_of_lt h4t hsq) hself)
    omega
  have hleaf : certifiedAdviceLeaf a cU =
      a - (2 * Nat.clog 2 (a + 1) + cU) := by
    unfold certifiedAdviceLeaf
    rw [Nat.sub_sub]
  have hdiff : a - certifiedAdviceLeaf a cU =
      2 * Nat.clog 2 (a + 1) + cU := by
    rw [hleaf]
    exact Nat.sub_sub_self hoverhead
  refine ⟨hoverhead, ?_⟩
  rw [hdiff]
  have hkmul : k * (2 * Nat.clog 2 (a + 1) + cU) ≤ 4 * k * t := by
    have h1 : k * (2 * Nat.clog 2 (a + 1) + cU) ≤ k * (4 * t) :=
      Nat.mul_le_mul_left k hover_lin
    have h2 : k * (4 * t) = 4 * k * t := by ring
    exact h1.trans_eq h2
  have hkt : 4 * k * t ≤ t * t := Nat.mul_le_mul_right t h4k
  have hlt : k * (2 * Nat.clog 2 (a + 1) + cU) < a + 1 :=
    lt_of_le_of_lt hkmul (lt_of_lt_of_le (lt_of_le_of_lt hkt hsq) hself)
  omega

/-- The selected block satisfies `log σ_L / log L → 1`: for every `k`,
the deficit `log L - log σ_L` is eventually at most `log L / k`. -/
theorem certifiedSigma_log_gap (k : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      k * (log2nat L - log2nat (certifiedSigma L)) ≤ log2nat L := by
  by_cases hk : k = 0
  · refine ⟨0, ?_⟩
    intro L _
    simp [hk]
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually (max 256 (8 * k))
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hmM, hAd, _, hσ⟩ := hL0 L hL
  have hm256 : 256 ≤ m := (Nat.le_max_left 256 (8 * k)).trans hmM
  have h8k : 8 * k ≤ m := (Nat.le_max_right 256 (8 * k)).trans hmM
  have hmpos : 0 < m := by omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  set ℓ := log2nat L
  set h := hBlock L m
  have hm_sqrt : m ≤ Nat.sqrt ℓ := hAd.2.1
  have hb_sqrt : bOf m ≤ Nat.sqrt ℓ := hAd.2.2.1
  have hdiv : m ∣ h := hAd.2.2.2.2.2.2.1
  have h8sig : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
  have hdenL : q m * (m + 1) < L := hAd.2.2.2.1
  obtain ⟨he7, hpow⟩ := sigmaFinal_eq_pow (L := L) (m := m) hmpos hdiv h8sig
  set e := 2 * (h / m) * (m - 1)
  have hlogσ : log2nat (certifiedSigma L) = e - 7 := by
    rw [hσ, hpow]
    rw [log2nat, if_neg (Nat.two_pow_pos _).ne', Nat.log_pow (by decide : 1 < 2)]
  have hm_le_b : m ≤ bOf m := by
    have h1 : m ≤ 4000 * m := Nat.le_mul_of_pos_left m (by decide : 0 < 4000)
    have h2 : 4000 * m ≤ 4000 * m * m :=
      Nat.le_mul_of_pos_right (4000 * m) hmpos
    simpa [bOf, Nat.pow_two, Nat.mul_assoc] using h1.trans h2
  have hb2 : bOf m * bOf m ≤ ℓ := (Nat.le_sqrt).mp hb_sqrt
  have hm2 : m * m ≤ ℓ :=
    (Nat.mul_le_mul hm_le_b hm_le_b).trans hb2
  let D := q m * (m + 1)
  have hDpos : 0 < D := Nat.mul_pos (Nat.sqrt_pos.2 hmpos) (Nat.succ_pos m)
  have hDle : D ≤ 2 ^ (2 * m) := by
    calc
      D ≤ m * (m + 1) := Nat.mul_le_mul_right (m + 1) (Nat.sqrt_le_self m)
      _ ≤ 2 ^ m * 2 ^ m :=
        Nat.mul_le_mul (self_le_two_pow m) (succ_le_two_pow m (by omega))
      _ = 2 ^ (2 * m) := by rw [← Nat.pow_add, Nat.two_mul]
  let p1 := 2 * m + 1
  have hp1_le : p1 ≤ ℓ := by
    have h3 : 2 * m + 1 ≤ 3 * m := by omega
    have h33 : 3 * m ≤ m * m := Nat.mul_le_mul_right m (by omega : 3 ≤ m)
    exact (h3.trans h33).trans hm2
  have hLne : L ≠ 0 := by
    intro h0
    have hzero : ℓ = 0 := by simp [ℓ, log2nat, h0]
    have : (0 : Nat) < ℓ := by
      have : 0 < m * m := Nat.mul_pos hmpos hmpos
      exact this.trans_le hm2
    omega
  have hℓlog : ℓ = Nat.log 2 L := by simp [ℓ, log2nat, hLne]
  have hpowL : 2 ^ ℓ ≤ L := by
    rw [hℓlog]
    exact Nat.pow_log_le_self 2 hLne
  have hbn_eq : blockNum L m = (L - 1) / D := by
    have hmax : Nat.max D 1 = D := Nat.max_eq_left (Nat.succ_le_of_lt hDpos)
    simp [blockNum, hLne, hmax, D]
  have hbn_pow : 2 ^ (ℓ - p1) ≤ blockNum L m := by
    rw [hbn_eq]
    apply (Nat.le_div_iff_mul_le hDpos).2
    have hmul : D * 2 ^ (ℓ - p1) ≤ 2 ^ (2 * m) * 2 ^ (ℓ - p1) :=
      Nat.mul_le_mul_right _ hDle
    have hpowadd : 2 ^ (2 * m) * 2 ^ (ℓ - p1) = 2 ^ (ℓ - 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hhalf : 2 ^ (ℓ - 1) ≤ 2 ^ ℓ - 1 := by
      have hpos : 1 ≤ 2 ^ (ℓ - 1) := Nat.one_le_pow (ℓ - 1) 2 (by decide)
      have htwo : 2 ^ (ℓ - 1) + 2 ^ (ℓ - 1) = 2 ^ ℓ := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      exact Nat.le_sub_of_add_le <|
        calc
          2 ^ (ℓ - 1) + 1 ≤ 2 ^ (ℓ - 1) + 2 ^ (ℓ - 1) := Nat.add_le_add_left hpos _
          _ = 2 ^ ℓ := htwo
    have hsub : 2 ^ ℓ - 1 ≤ L - 1 := Nat.sub_le_sub_right hpowL 1
    have hcomm : 2 ^ (ℓ - p1) * D = D * 2 ^ (ℓ - p1) := Nat.mul_comm _ _
    rw [hcomm]
    exact (hmul.trans (le_of_eq hpowadd)).trans (hhalf.trans hsub)
  have hlogbn : ℓ - p1 ≤ log2nat (blockNum L m) := by
    have hne : blockNum L m ≠ 0 :=
      ne_of_gt <| lt_of_lt_of_le (Nat.two_pow_pos (ℓ - p1)) hbn_pow
    have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) hbn_pow
    simpa [log2nat, hne] using hlog
  have hℓ_bn : ℓ ≤ log2nat (blockNum L m) + p1 :=
    (Nat.sub_le_iff_le_add).mp hlogbn
  let b := bOf m
  have hbpos : 0 < 2 * b := by
    dsimp [b, bOf]
    positivity
  have hsplit := Nat.div_add_mod' (log2nat (blockNum L m)) (2 * b)
  have h2h_eq : 2 * h = log2nat (blockNum L m) / (2 * b) * (2 * b) := by
    dsimp [h, hBlock, b]
    calc
      2 * (bOf m * (log2nat (blockNum L m) / (2 * bOf m))) =
          (2 * bOf m) * (log2nat (blockNum L m) / (2 * bOf m)) := by ring
      _ = log2nat (blockNum L m) / (2 * bOf m) * (2 * bOf m) := by rw [Nat.mul_comm]
  have hrem : log2nat (blockNum L m) ≤ 2 * h + 2 * b := by
    have hr : log2nat (blockNum L m) % (2 * b) ≤ 2 * b :=
      Nat.le_of_lt (Nat.mod_lt _ hbpos)
    calc
      log2nat (blockNum L m) =
          2 * h + log2nat (blockNum L m) % (2 * b) := by
        rw [h2h_eq]
        exact hsplit.symm
      _ ≤ 2 * h + 2 * b := Nat.add_le_add_left hr _
  have h2h_log : 2 * h ≤ log2nat (blockNum L m) :=
    two_mul_hBlock_le_log2_blockNum L m
  have hlog_mono : log2nat (blockNum L m) ≤ ℓ := by
    have hbnL : blockNum L m ≤ L := by
      unfold blockNum
      split_ifs with hzero
      · exact Nat.zero_le _
      · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    rw [hℓlog]
    unfold log2nat
    by_cases hb0 : blockNum L m = 0
    · simp [hb0]
    · rw [if_neg hb0]
      exact Nat.log_mono_right hbnL
  have h2h_ℓ : 2 * h ≤ ℓ := h2h_log.trans hlog_mono
  have hdiv_le : 2 * (h / m) ≤ ℓ / m := by
    rw [← Nat.mul_div_assoc 2 hdiv]
    exact Nat.div_le_div_right h2h_ℓ
  have he_sub : e = 2 * h - 2 * (h / m) := by
    have hmul : (h / m) * m = h := Nat.div_mul_cancel hdiv
    have he1 : e = 2 * (h / m) * m - 2 * (h / m) := by
      dsimp [e]
      rw [Nat.mul_sub, Nat.mul_one]
    have he2 : 2 * (h / m) * m = 2 * h := by
      calc
        2 * (h / m) * m = 2 * ((h / m) * m) := by rw [Nat.mul_assoc]
        _ = 2 * h := by rw [hmul]
    rw [he1, he2]
  have he_cancel : e + 2 * (h / m) = 2 * h := by
    rw [he_sub]
    exact Nat.sub_add_cancel (Nat.mul_le_mul_left 2 (Nat.div_le_self h m))
  let p2 := 2 * b
  let p3 := ℓ / m
  let p4 : Nat := 7
  have hp1 : k * p1 ≤ ℓ / 4 := by
    have hkdiv : k ≤ m / 8 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2 (by simpa [Nat.mul_comm] using h8k)
    have h12k : 12 * k ≤ 2 * m := by
      have h1 : 12 * k ≤ 12 * (m / 8) := Nat.mul_le_mul_left 12 hkdiv
      have h2 : 12 * (m / 8) ≤ (12 * m) / 8 := by
        apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
        calc
          12 * (m / 8) * 8 = 12 * ((m / 8) * 8) := by rw [Nat.mul_assoc]
          _ ≤ 12 * m := Nat.mul_le_mul_left 12 (Nat.div_mul_le_self m 8)
      have h3 : (12 * m) / 8 ≤ 2 * m := by
        apply Nat.le_of_mul_le_mul_right _ (by decide : 0 < 8)
        calc
          (12 * m) / 8 * 8 ≤ 12 * m := Nat.div_mul_le_self _ _
          _ ≤ 16 * m := Nat.mul_le_mul_right m (by decide : 12 ≤ 16)
          _ = 2 * m * 8 := by ring
      exact h1.trans (h2.trans h3)
    have h12km : 12 * k * m ≤ m * m * (m * m) := by
      have hmul : 12 * k * m ≤ (2 * m) * m := Nat.mul_le_mul_right m h12k
      have h2mm : (2 * m) * m ≤ m * m * (m * m) := by
        have hm2ge : 2 ≤ m * m := by
          calc
            2 ≤ m := by omega
            _ ≤ m * m := Nat.le_mul_of_pos_right m hmpos
        calc
          (2 * m) * m = 2 * (m * m) := by rw [Nat.mul_assoc]
          _ ≤ (m * m) * (m * m) := Nat.mul_le_mul_right (m * m) hm2ge
      exact hmul.trans h2mm
    have hm4 : m * m * (m * m) ≤ ℓ := by
      have hbb : m * m ≤ bOf m := by
        simpa [bOf, Nat.pow_two] using
          Nat.le_mul_of_pos_left (m * m) (by decide : 0 < 4000)
      exact (Nat.mul_le_mul hbb hbb).trans hb2
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
    calc
      k * p1 * 4 ≤ k * (3 * m) * 4 := by
        have h3m : p1 ≤ 3 * m := by
          dsimp [p1]
          omega
        exact Nat.mul_le_mul_right 4 (Nat.mul_le_mul_left k h3m)
      _ = 12 * k * m := by ring
      _ ≤ ℓ := h12km.trans hm4
  have hp2 : k * p2 ≤ ℓ / 4 := by
    have h8b : 8 * k ≤ b := h8k.trans hm_le_b
    have h8prod : 8 * k * b ≤ ℓ := by
      have hmul : (8 * k) * b ≤ b * b := Nat.mul_le_mul_right b h8b
      simpa [b, Nat.mul_assoc] using hmul.trans hb2
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
    calc
      k * p2 * 4 = k * (2 * b) * 4 := by dsimp [p2]
      _ = 8 * k * b := by ring
      _ ≤ ℓ := h8prod
  have hp3 : k * p3 ≤ ℓ / 4 := by
    have hden : 0 < 8 * k := by omega
    have hquot : ℓ / m ≤ ℓ / (8 * k) := by
      apply (Nat.le_div_iff_mul_le hden).2
      calc
        (ℓ / m) * (8 * k) ≤ (ℓ / m) * m := Nat.mul_le_mul_left (ℓ / m) h8k
        _ ≤ ℓ := Nat.div_mul_le_self ℓ m
    have hmulk : k * (ℓ / m) ≤ k * (ℓ / (8 * k)) := Nat.mul_le_mul_left k hquot
    have h8 : k * (ℓ / (8 * k)) ≤ ℓ / 8 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
      calc
        k * (ℓ / (8 * k)) * 8 = (ℓ / (8 * k)) * (8 * k) := by ring
        _ ≤ ℓ := Nat.div_mul_le_self ℓ (8 * k)
    have h84 : ℓ / 8 ≤ ℓ / 4 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
      calc
        (ℓ / 8) * 4 ≤ (ℓ / 8) * 8 := Nat.mul_le_mul_left _ (by decide)
        _ ≤ ℓ := Nat.div_mul_le_self ℓ 8
    simpa [p3] using hmulk.trans (h8.trans h84)
  have hp4 : k * p4 ≤ ℓ / 4 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
    have h64 : 64 * k * k ≤ ℓ := by
      have hmul : (8 * k) * (8 * k) ≤ m * m := Nat.mul_le_mul h8k h8k
      have hsq : (8 * k) * (8 * k) = 64 * k * k := by ring
      exact (hsq ▸ hmul).trans hm2
    calc
      k * p4 * 4 = 28 * k := by dsimp [p4]; ring
      _ ≤ 64 * k * k := by
        calc
          28 * k ≤ 64 * k := Nat.mul_le_mul_right k (by decide : 28 ≤ 64)
          _ ≤ 64 * k * k := Nat.le_mul_of_pos_right (64 * k) hkpos
      _ ≤ ℓ := h64
  have hmain : ℓ ≤ (e - 7) + (p1 + p2 + p3 + p4) := by
    have hbn_p2 : log2nat (blockNum L m) + p1 ≤ 2 * h + p2 + p1 :=
      Nat.add_le_add_right hrem p1
    have h2 : 2 * h + p2 + p1 ≤ e + 2 * (h / m) + p2 + p1 := by
      rw [← he_cancel]
    have h3 : e + 2 * (h / m) + p2 + p1 ≤ e + p3 + p2 + p1 := by
      have hle : 2 * (h / m) ≤ p3 := by simpa [p3] using hdiv_le
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_left hle e) p2) p1
    have h4 : e + p3 + p2 + p1 ≤ (e - 7) + (p1 + p2 + p3 + p4) := by
      have h7 := Nat.sub_add_cancel he7
      dsimp [p4]
      omega
    calc
      ℓ ≤ log2nat (blockNum L m) + p1 := hℓ_bn
      _ ≤ 2 * h + p2 + p1 := hbn_p2
      _ ≤ e + 2 * (h / m) + p2 + p1 := h2
      _ ≤ e + p3 + p2 + p1 := h3
      _ ≤ (e - 7) + (p1 + p2 + p3 + p4) := h4
  have hδ : ℓ - (e - 7) ≤ p1 + p2 + p3 + p4 :=
    (Nat.sub_le_iff_le_add).mpr <| by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmain
  have hdist : k * (p1 + p2 + p3 + p4) =
      k * p1 + k * p2 + k * p3 + k * p4 := by ring
  have hquarters : k * p1 + k * p2 + k * p3 + k * p4 ≤ ℓ := by
    calc
      k * p1 + k * p2 + k * p3 + k * p4 ≤
          ℓ / 4 + ℓ / 4 + ℓ / 4 + ℓ / 4 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp1 hp2) hp3) hp4
      _ = 4 * (ℓ / 4) := by ring
      _ ≤ ℓ := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self ℓ 4
  calc
    k * (ℓ - log2nat (certifiedSigma L)) = k * (ℓ - (e - 7)) := by rw [hlogσ]
    _ ≤ k * (p1 + p2 + p3 + p4) := Nat.mul_le_mul_left k hδ
    _ = k * p1 + k * p2 + k * p3 + k * p4 := hdist
    _ ≤ ℓ := hquarters

theorem certified_log_pos :
    ∃ L0, ∀ L, L0 ≤ L → 0 < log2nat L := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, _, _⟩ := hL0 L hL
  have hm : m * m ≤ log2nat L := (Nat.le_sqrt).mp hAd.2.1
  have h256 : 256 * 256 ≤ m * m := Nat.mul_le_mul hm256 hm256
  exact lt_of_lt_of_le (by decide : 0 < 256 * 256) (h256.trans hm)

/-- `log σ_L / log L` is eventually at least `1 - 1/k`. -/
theorem certifiedSigma_log_ratio (k : Nat) (hk : 0 < k) :
    ∃ L0, ∀ L, L0 ≤ L →
      0 < log2nat L ∧
      (1 : Rat) - (1 / (k : Rat)) ≤
        (log2nat (certifiedSigma L) : Rat) / (log2nat L : Rat) := by
  obtain ⟨L1, h1⟩ := certifiedSigma_log_gap k
  obtain ⟨L2, h2⟩ := certifiedSigma_pos_le_log
  obtain ⟨L3, h3⟩ := certified_log_pos
  refine ⟨max L1 (max L2 L3), ?_⟩
  intro L hL
  have hL1 : L1 ≤ L := (Nat.le_max_left _ _).trans hL
  have hL2 : L2 ≤ L :=
    (Nat.le_max_left L2 L3).trans ((Nat.le_max_right L1 (max L2 L3)).trans hL)
  have hL3 : L3 ≤ L :=
    (Nat.le_max_right L2 L3).trans ((Nat.le_max_right L1 (max L2 L3)).trans hL)
  have hgap := h1 L hL1
  have hpos := h2 L hL2
  have hℓ : 0 < log2nat L := h3 L hL3
  set ℓ := log2nat L
  set s := log2nat (certifiedSigma L)
  have hs : s ≤ ℓ := by simpa [s, ℓ] using hpos.2
  have hδ : k * (ℓ - s) ≤ ℓ := by simpa [ℓ, s] using hgap
  have hsum : s + (ℓ - s) = ℓ := Nat.add_sub_of_le hs
  have hcast : (ℓ : Rat) = (s : Rat) + ((ℓ - s : Nat) : Rat) := by
    exact_mod_cast hsum.symm
  have hdiv : ((ℓ - s : Nat) : Rat) / (ℓ : Rat) ≤ 1 / (k : Rat) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hℓ) (by exact_mod_cast hk)]
    have hmul : (ℓ - s) * k ≤ 1 * ℓ := by
      simpa [Nat.one_mul, Nat.mul_comm] using hδ
    exact_mod_cast hmul
  have hratio : (s : Rat) / (ℓ : Rat) = 1 - ((ℓ - s : Nat) : Rat) / (ℓ : Rat) := by
    have hne : (ℓ : Rat) ≠ 0 := by exact_mod_cast hℓ.ne'
    field_simp [hne]
    linarith [hcast]
  refine ⟨hℓ, ?_⟩
  calc
    (1 : Rat) - (1 / (k : Rat)) ≤
        1 - ((ℓ - s : Nat) : Rat) / (ℓ : Rat) :=
      sub_le_sub_left hdiv _
    _ = (s : Rat) / (ℓ : Rat) := hratio.symm

/-- Admissible blocks have `σ ≥ 2`. A one-hot budget then admits a second
uniform symbol, the same numerical room used by the headline two-label cover. -/
theorem certifiedSigma_ge_two_eventual :
    ∃ L0, ∀ L, L0 ≤ L → 2 ≤ certifiedSigma L := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, _, hσ⟩ := hL0 L hL
  have hmpos : 0 < m := by omega
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have hsrc : manuscriptSourceFloor m ≤ hBlock L m := hAd.2.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
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
  obtain ⟨_, hpow⟩ := sigmaFinal_eq_pow (L := L) (m := m) hmpos hdiv h8
  have hm1 : 255 ≤ m - 1 := by omega
  have he8 : 8 ≤ 2 * (hBlock L m / m) * (m - 1) := by
    have hmul : 2 * 2 ≤ 2 * (hBlock L m / m) := Nat.mul_le_mul_left 2 hq
    have hprod : 2 * 2 * 255 ≤ 2 * (hBlock L m / m) * (m - 1) := by
      calc
        2 * 2 * 255 ≤ 2 * (hBlock L m / m) * 255 := Nat.mul_le_mul_right 255 hmul
        _ ≤ 2 * (hBlock L m / m) * (m - 1) := Nat.mul_le_mul_left _ hm1
    exact (by decide : 8 ≤ 2 * 2 * 255).trans hprod
  rw [hσ, hpow]
  have hshift : 1 ≤ 2 * (hBlock L m / m) * (m - 1) - 7 := by omega
  have hpow2 : 2 ^ 1 ≤ 2 ^ (2 * (hBlock L m / m) * (m - 1) - 7) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hshift
  simpa using hpow2

/-- The same admissible blocks have `σ ≥ 4`, enough room for a 4-label cover. -/
theorem certifiedSigma_ge_four_eventual :
    ∃ L0, ∀ L, L0 ≤ L → 4 ≤ certifiedSigma L := by
  obtain ⟨L0, hL0⟩ := certified_parameters_eventually 256
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, _, hσ⟩ := hL0 L hL
  have hmpos : 0 < m := by omega
  have hdiv : m ∣ hBlock L m := hAd.2.2.2.2.2.2.1
  have hsrc : manuscriptSourceFloor m ≤ hBlock L m := hAd.2.2.2.2.2.2.2.1
  have h8 : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
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
  obtain ⟨_, hpow⟩ := sigmaFinal_eq_pow (L := L) (m := m) hmpos hdiv h8
  have hm1 : 255 ≤ m - 1 := by omega
  have he9 : 9 ≤ 2 * (hBlock L m / m) * (m - 1) := by
    have hmul : 2 * 2 ≤ 2 * (hBlock L m / m) := Nat.mul_le_mul_left 2 hq
    have hprod : 2 * 2 * 255 ≤ 2 * (hBlock L m / m) * (m - 1) := by
      calc
        2 * 2 * 255 ≤ 2 * (hBlock L m / m) * 255 := Nat.mul_le_mul_right 255 hmul
        _ ≤ 2 * (hBlock L m / m) * (m - 1) := Nat.mul_le_mul_left _ hm1
    exact (by decide : 9 ≤ 2 * 2 * 255).trans hprod
  rw [hσ, hpow]
  have hshift : 2 ≤ 2 * (hBlock L m / m) * (m - 1) - 7 := by omega
  have hpow2 : 2 ^ 2 ≤ 2 ^ (2 * (hBlock L m / m) * (m - 1) - 7) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hshift
  simpa using hpow2

end PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
