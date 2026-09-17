import PvNP.RealizableHardness.ActualTheorem1
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
Manuscript `σ_L` / `γ_L` family, Corollary 2 parameter maps, and the
conditional headline specialization of `theorem1_realizable_cmmsa`.

This module does not construct SAT-to-source or source-to-CMMSA
`Preserves (1/6)` maps, does not inhabit the headline theorem with an
identity reduction, and does not prove unconditional Theorem 1,
Corollary 2 NP-hardness, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualHeadlineParameters
open Complexity RandomizedReduction ActualCMMSARandomizedReduction ActualTheorem1

def log2nat (n : Nat) : Nat := if n = 0 then 0 else Nat.log 2 n

def qOf (m : Nat) : Nat := Nat.sqrt m

/-- Largest `m` with `256 ≤ m ∧ m ≤ sqrt(log2 L)`. Zero if none. -/
def mOf (L : Nat) : Nat :=
  if Nat.sqrt (log2nat L) < 256 then 0 else Nat.sqrt (log2nat L)

theorem mOf_spec (L : Nat) :
    mOf L = 0 ∨ (256 ≤ mOf L ∧ mOf L ≤ Nat.sqrt (log2nat L)) := by
  unfold mOf
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr ⟨Nat.le_of_not_gt h, le_rfl⟩

theorem mOf_maximal (L m : Nat) (h : 256 ≤ m ∧ m ≤ Nat.sqrt (log2nat L)) :
    m ≤ mOf L := by
  have hge : ¬ Nat.sqrt (log2nat L) < 256 := not_lt.mpr (h.1.trans h.2)
  unfold mOf
  simp [hge]
  exact h.2

def hOf (L m : Nat) : Nat :=
  let q := qOf m
  let den := q * (m + 1)
  let num := if L = 0 then 0 else (L - 1) / Nat.max den 1
  let bm := Nat.max m 1
  bm * (log2nat num / (2 * bm))

def ROf (L : Nat) : Nat := 2 ^ (2 * hOf L (mOf L))

def GammaOf (L : Nat) : Rat :=
  2 * ((3 / 4 : Rat) ^ qOf (mOf L))

def sigmaL (L : Nat) : Nat := (ROf L / 4) / 2

def gammaL (L : Nat) : Rat := 2 * GammaOf L

private lemma log2nat_pow_two (k : Nat) : log2nat (2 ^ k) = k := by
  simp [log2nat]

private lemma log2nat_mono {a b : Nat} (h : a ≤ b) : log2nat a ≤ log2nat b := by
  unfold log2nat
  by_cases ha : a = 0
  · simp [ha]
  · have hb : b ≠ 0 := fun hb => ha (Nat.eq_zero_of_le_zero (h.trans hb.le))
    simp [ha, hb]
    exact Nat.log_mono_right h

private lemma log2nat_le_of_le {a b : Nat} (h : a ≤ b) : log2nat a ≤ log2nat b :=
  log2nat_mono h

private lemma hOf_eq (L m : Nat) :
    hOf L m =
      Nat.max m 1 *
        (log2nat (if L = 0 then 0 else (L - 1) / Nat.max (qOf m * (m + 1)) 1) /
          (2 * Nat.max m 1)) :=
  rfl

private lemma numOf_le (L m : Nat) :
    (if L = 0 then 0 else (L - 1) / Nat.max (qOf m * (m + 1)) 1) ≤ L := by
  split_ifs with hL
  · exact Nat.zero_le _
  · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem hOf_le_log2 (L : Nat) : 2 * hOf L (mOf L) ≤ log2nat L := by
  rw [hOf_eq]
  set bm := Nat.max (mOf L) 1
  set num := if L = 0 then 0 else (L - 1) / Nat.max (qOf (mOf L) * (mOf L + 1)) 1
  have hmul :
      2 * (bm * (log2nat num / (2 * bm))) ≤ log2nat num := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le (log2nat num) (2 * bm)
  exact hmul.trans (log2nat_mono (numOf_le L (mOf L)))

theorem sigmaL_le_ROf (L : Nat) : sigmaL L ≤ ROf L :=
  (Nat.div_le_self (ROf L / 4) 2).trans (Nat.div_le_self (ROf L) 4)

theorem mOf_unbounded : ∀ M, ∃ L0, ∀ L, L0 ≤ L → M ≤ mOf L := by
  intro M
  let t := Nat.max M 256
  refine ⟨2 ^ (t ^ 2 + 1), ?_⟩
  intro L hL
  have ht256 : 256 ≤ t := Nat.le_max_right _ _
  have htM : M ≤ t := Nat.le_max_left _ _
  have hlog0 : log2nat (2 ^ (t ^ 2 + 1)) = t ^ 2 + 1 := log2nat_pow_two _
  have hlog : t ^ 2 + 1 ≤ log2nat L :=
    (le_of_eq hlog0.symm).trans (log2nat_mono hL)
  have hsq : t * t ≤ log2nat L := by
    have : t ^ 2 ≤ t ^ 2 + 1 := Nat.le_succ _
    exact (le_of_eq (Nat.pow_two t).symm).trans (this.trans hlog)
  have hsqrt : t ≤ Nat.sqrt (log2nat L) := Nat.le_sqrt.mpr hsq
  have hge : ¬ Nat.sqrt (log2nat L) < 256 := not_lt.mpr (ht256.trans hsqrt)
  unfold mOf
  simp [hge]
  exact htM.trans hsqrt

private lemma two_pow_sq_dominates {s : Nat} (hs : 256 ≤ s) :
    s * (s + 1) * 2 ^ (4 * s) + 1 ≤ 2 ^ (s ^ 2) := by
  have h1 : s ≤ 2 ^ s := (Nat.lt_two_pow_self (n := s)).le
  have h2 : s + 1 ≤ 2 ^ (s + 1) := (Nat.lt_two_pow_self (n := s + 1)).le
  have h3 : s * (s + 1) ≤ 2 ^ s * 2 ^ (s + 1) := Nat.mul_le_mul h1 h2
  have h3' : s * (s + 1) ≤ 2 ^ (2 * s + 1) := by
    calc
      s * (s + 1) ≤ 2 ^ s * 2 ^ (s + 1) := h3
      _ = 2 ^ (s + (s + 1)) := (Nat.pow_add 2 s (s + 1)).symm
      _ = 2 ^ (2 * s + 1) := by congr 1; omega
  have h4 : s * (s + 1) * 2 ^ (4 * s) ≤ 2 ^ (6 * s + 1) := by
    calc
      s * (s + 1) * 2 ^ (4 * s) ≤ 2 ^ (2 * s + 1) * 2 ^ (4 * s) :=
        Nat.mul_le_mul_right _ h3'
      _ = 2 ^ (2 * s + 1 + 4 * s) := (Nat.pow_add 2 (2 * s + 1) (4 * s)).symm
      _ = 2 ^ (6 * s + 1) := by congr 1; omega
  have hone : 1 ≤ 2 ^ (6 * s + 1) := Nat.one_le_two_pow
  have h5 : 2 ^ (6 * s + 1) + 1 ≤ 2 ^ (6 * s + 2) := by
    have hdouble : 2 ^ (6 * s + 1) + 2 ^ (6 * s + 1) = 2 ^ (6 * s + 2) := by
      calc
        2 ^ (6 * s + 1) + 2 ^ (6 * s + 1) = 2 * 2 ^ (6 * s + 1) :=
          (Nat.two_mul _).symm
        _ = 2 ^ (6 * s + 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ ((6 * s + 1) + 1) := (Nat.pow_succ 2 (6 * s + 1)).symm
        _ = 2 ^ (6 * s + 2) := by rfl
    exact (Nat.add_le_add_left hone _).trans (le_of_eq hdouble)
  have h6 : 6 * s + 2 ≤ s ^ 2 := by
    have h8 : 6 * s + 2 ≤ 8 * s := by
      have : 2 ≤ 2 * s := Nat.mul_le_mul_left 2 (le_trans (by decide : 1 ≤ 256) hs)
      omega
    have h256 : 8 * s ≤ 256 * s := Nat.mul_le_mul_right s (by decide : 8 ≤ 256)
    have hsq : 256 * s ≤ s * s := Nat.mul_le_mul_right s hs
    exact h8.trans (h256.trans (by simpa [Nat.pow_two] using hsq))
  have h7 : 2 ^ (6 * s + 2) ≤ 2 ^ (s ^ 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h6
  exact (Nat.add_le_add_right h4 1).trans (h5.trans h7)

private lemma mOf_eq_sqrt {L : Nat} (h : 256 ≤ mOf L) :
    mOf L = Nat.sqrt (log2nat L) := by
  have hspec := mOf_spec L
  rcases hspec with h0 | hpair
  · exact (Nat.not_succ_le_zero 255 (h0 ▸ h)).elim
  · exact le_antisymm hpair.2
      (mOf_maximal L (Nat.sqrt (log2nat L)) ⟨hpair.1.trans hpair.2, le_rfl⟩)

private lemma one_le_div4_div2 {n : Nat} (h : 8 ≤ n) : 1 ≤ (n / 4) / 2 := by
  have h2 : 2 ≤ n / 4 := (Nat.div_le_div_right h : 8 / 4 ≤ n / 4)
  exact (Nat.div_le_div_right h2 : 2 / 2 ≤ (n / 4) / 2)

private lemma hOf_ge_two {L : Nat} (hL : 256 ≤ mOf L)
    (hnum : 4 * mOf L ≤
      log2nat (if L = 0 then 0 else (L - 1) / Nat.max (qOf (mOf L) * (mOf L + 1)) 1)) :
    2 ≤ hOf L (mOf L) := by
  rw [hOf_eq]
  set s := mOf L
  set num := if L = 0 then 0 else (L - 1) / Nat.max (qOf s * (s + 1)) 1
  have hs : 1 ≤ s := le_trans (by decide : 1 ≤ 256) hL
  have hbm : Nat.max s 1 = s := Nat.max_eq_left hs
  have hspos : 0 < s := lt_of_lt_of_le (by decide : 0 < 256) hL
  have h2s : 0 < 2 * s := Nat.mul_pos (by decide) hspos
  rw [hbm]
  have hquot : 2 ≤ log2nat num / (2 * s) :=
    (Nat.le_div_iff_mul_le h2s).2 (by
      have : 2 * (2 * s) = 4 * s := by ring
      simpa [this, num] using hnum)
  have hprod : s * 2 ≤ s * (log2nat num / (2 * s)) :=
    Nat.mul_le_mul_left s hquot
  exact (Nat.le_mul_of_pos_left 2 hspos).trans hprod

theorem sigmaL_ge_one_eventual : ∃ L0, ∀ L, L0 ≤ L → 1 ≤ sigmaL L := by
  obtain ⟨L0, hL0⟩ := mOf_unbounded 256
  refine ⟨L0, ?_⟩
  intro L hLL0
  have hs256 : 256 ≤ mOf L := hL0 L hLL0
  have hLpos : L ≠ 0 := by
    intro h0
    subst h0
    have : mOf 0 = 0 := by simp [mOf, log2nat]
    exact Nat.not_succ_le_zero 255 (this ▸ hs256)
  have hs : mOf L = Nat.sqrt (log2nat L) := mOf_eq_sqrt hs256
  set s := mOf L
  have hspos : 0 < s := lt_of_lt_of_le (by decide : 0 < 256) hs256
  have hsq : s ^ 2 ≤ log2nat L := by
    have := Nat.sqrt_le' (log2nat L)
    simpa [hs] using this
  have hpowL : 2 ^ log2nat L ≤ L := by
    rw [show log2nat L = Nat.log 2 L from ite_eq_right hLpos]
    exact Nat.pow_log_le_self 2 hLpos
  have h2s : 2 ^ (s ^ 2) ≤ L :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hsq).trans hpowL
  have hden_le : qOf s * (s + 1) ≤ s * (s + 1) :=
    Nat.mul_le_mul_right (s + 1) (Nat.sqrt_le_self s)
  have hdenpos : 0 < qOf s * (s + 1) := by
    have hq : 0 < qOf s := by
      have : 16 ≤ Nat.sqrt s :=
        (Nat.le_sqrt.mpr (by
          have : 16 * 16 ≤ 256 := by decide
          exact this.trans hs256))
      exact lt_of_lt_of_le (by decide : 0 < 16) this
    exact Nat.mul_pos hq (Nat.succ_pos s)
  have hbound : qOf s * (s + 1) * 2 ^ (4 * s) + 1 ≤ 2 ^ (s ^ 2) :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hden_le) 1).trans
      (two_pow_sq_dominates hs256)
  have hnum_ge : 2 ^ (4 * s) ≤
      (L - 1) / Nat.max (qOf s * (s + 1)) 1 := by
    have hden : Nat.max (qOf s * (s + 1)) 1 = qOf s * (s + 1) :=
      Nat.max_eq_left (Nat.succ_le_iff.mp hdenpos)
    have hprod : qOf s * (s + 1) * 2 ^ (4 * s) ≤ L - 1 := by
      have hadd : qOf s * (s + 1) * 2 ^ (4 * s) + 1 ≤ L := hbound.trans h2s
      have hL1 : 1 ≤ L := Nat.pos_iff_ne_zero.mpr hLpos
      exact Nat.le_sub_of_add_le hadd
    have : (qOf s * (s + 1) * 2 ^ (4 * s)) / (qOf s * (s + 1)) ≤
        (L - 1) / (qOf s * (s + 1)) :=
      Nat.div_le_div_right hprod
    have hcancel :
        (qOf s * (s + 1) * 2 ^ (4 * s)) / (qOf s * (s + 1)) = 2 ^ (4 * s) :=
      Nat.mul_div_cancel_left _ hdenpos
    simpa [hden, hcancel] using this
  have hlog : 4 * s ≤
      log2nat (if L = 0 then 0 else (L - 1) / Nat.max (qOf s * (s + 1)) 1) := by
    simp [hLpos]
    have hpow : log2nat (2 ^ (4 * s)) = 4 * s := log2nat_pow_two _
    exact (le_of_eq hpow.symm).trans (log2nat_mono hnum_ge)
  have hh : 2 ≤ hOf L s := by
    have := hOf_ge_two (L := L) hs256
    simpa [s] using this hlog
  have hR : 8 ≤ ROf L := by
    unfold ROf
    have h3 : 3 ≤ 2 * hOf L (mOf L) :=
      le_trans (by decide : 3 ≤ 4) (Nat.mul_le_mul_left 2 (by simpa [s] using hh))
    exact (show 2 ^ 3 ≤ 2 ^ (2 * hOf L (mOf L)) from
      Nat.pow_le_pow_right (by decide : 0 < 2) h3)
  exact one_le_div4_div2 (n := ROf L) hR

private lemma three_four_pow_pos (n : Nat) : (0 : Rat) < (3 / 4 : Rat) ^ n :=
  pow_pos (by norm_num) n

private lemma gammaL_eq (L : Nat) :
    gammaL L = 4 * ((3 / 4 : Rat) ^ qOf (mOf L)) := by
  simp [gammaL, GammaOf]
  ring

private lemma gammaL_pos (L : Nat) : 0 < gammaL L := by
  rw [gammaL_eq]
  exact mul_pos (by norm_num) (three_four_pow_pos _)

private lemma three_four_pow_six_lt : ((3 / 4 : Rat) ^ 6) < (1 / 4 : Rat) := by
  norm_num

private lemma qOf_ge_six {m : Nat} (hm : 36 ≤ m) : 6 ≤ qOf m :=
  Nat.le_sqrt.mpr (by simpa [Nat.pow_two] using hm)

theorem gammaL_pos_lt_one_eventual :
    ∃ L0, ∀ L, L0 ≤ L → 0 < gammaL L ∧ gammaL L < 1 := by
  obtain ⟨L0, hL0⟩ := mOf_unbounded 36
  refine ⟨L0, ?_⟩
  intro L hLL0
  refine ⟨gammaL_pos L, ?_⟩
  have hm : 36 ≤ mOf L := hL0 L hLL0
  have hq : 6 ≤ qOf (mOf L) := qOf_ge_six hm
  have hpow : ((3 / 4 : Rat) ^ qOf (mOf L)) ≤ ((3 / 4 : Rat) ^ 6) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hlt : ((3 / 4 : Rat) ^ qOf (mOf L)) < (1 / 4 : Rat) :=
    lt_of_le_of_lt hpow three_four_pow_six_lt
  rw [gammaL_eq]
  nlinarith

theorem gammaL_small_eventual (ε : Rat) (hε : 0 < ε) :
    ∃ L0, ∀ L, L0 ≤ L → gammaL L < ε := by
  have hε4 : (0 : Rat) < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε4 (by norm_num : (3 / 4 : Rat) < 1)
  obtain ⟨L0, hL0⟩ := mOf_unbounded (k * k)
  refine ⟨L0, ?_⟩
  intro L hLL0
  have hm : k * k ≤ mOf L := hL0 L hLL0
  have hq : k ≤ qOf (mOf L) := Nat.le_sqrt.mpr hm
  have hpow : ((3 / 4 : Rat) ^ qOf (mOf L)) ≤ ((3 / 4 : Rat) ^ k) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hlt : 4 * ((3 / 4 : Rat) ^ qOf (mOf L)) < ε := by
    have hle : 4 * ((3 / 4 : Rat) ^ qOf (mOf L)) ≤ 4 * ((3 / 4 : Rat) ^ k) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hstrict : 4 * ((3 / 4 : Rat) ^ k) < 4 * (ε / 4) :=
      mul_lt_mul_of_pos_left hk (by norm_num)
    have h4 : (4 : Rat) * (ε / 4) = ε := by ring
    exact lt_of_le_of_lt hle (hstrict.trans_eq h4)
  simpa [gammaL_eq] using hlt

def adviceLeaf (a cU : Nat) : Nat :=
  a - 2 * log2nat (a + 1) - cU

def sigmaLearn (a cU : Nat) : Nat := (49 * sigmaL (adviceLeaf a cU)) / 100

def gammaLearn (a cU : Nat) : Rat := 5 * gammaL (adviceLeaf a cU)

/-- Conditional headline specialization of `theorem1_realizable_cmmsa` at
`sigmaL` / `gammaL`. The two `Preserves (1/6)` maps remain hypotheses. -/
theorem theorem1_headline
    {L : Nat}
    (hσ : 1 ≤ sigmaL L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (source : PromiseProblem)
    (hSatSrc : ∃ R : SeededMap,
      Preserves R (PromiseProblem.ofLanguage SAT.language) source (1 / 6) (1 / 6))
    (hSrcCmmsa : ∃ S : SeededMap,
      Preserves S source (cmmsaPromise L (sigmaL L) (gammaL L) hσ hγ0 hγ1) (1 / 6) (1 / 6)) :
    RandomizedPromiseNPHard (cmmsaPromise L (sigmaL L) (gammaL L) hσ hγ0 hγ1) :=
  theorem1_realizable_cmmsa hσ hγ0 hγ1 source hSatSrc hSrcCmmsa

end PvNP.RealizableHardness.ActualHeadlineParameters
