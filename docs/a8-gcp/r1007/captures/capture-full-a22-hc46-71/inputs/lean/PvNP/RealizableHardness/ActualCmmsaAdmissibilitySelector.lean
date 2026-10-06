import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
An honest, proof-carrying selector for the reconciled CMMSA parameter family.

The source threshold is deliberately an explicit parameter.  This file proves
that the parameter-selection mechanism is eventually populated for every
fixed natural threshold; it does not manufacture the missing source theorem.
In particular, the selector is `WithBot Nat`, so an empty admissible set is
represented by `⊥` rather than by a default natural number.
-/
namespace PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation

set_option maxRecDepth 1000000
set_option exponentiation.threshold 100000

def Admissible (sourceHMin : Nat → Nat) (L m : Nat) : Prop :=
  256 ≤ m ∧
  m ≤ Nat.sqrt (log2nat L) ∧
  bOf m ≤ Nat.sqrt (log2nat L) ∧
  q m * (m + 1) < L ∧
  q m * (m + 1) * RBlock L m + 1 ≤ L ∧
  bOf m ∣ hBlock L m ∧
  m ∣ hBlock L m ∧
  sourceHMin m ≤ hBlock L m ∧
  8 ≤ sigmaBase L m

noncomputable def admissibleMs (sourceHMin : Nat → Nat) (L : Nat) : Finset Nat := by
  classical
  exact (Finset.range (Nat.sqrt (log2nat L) + 1)).filter
    (Admissible sourceHMin L)

noncomputable def selector (sourceHMin : Nat → Nat) (L : Nat) : WithBot Nat :=
  (admissibleMs sourceHMin L).max

theorem mem_admissibleMs_iff (sourceHMin : Nat → Nat) (L m : Nat) :
    m ∈ admissibleMs sourceHMin L ↔
      m ≤ Nat.sqrt (log2nat L) ∧ Admissible sourceHMin L m := by
  simp only [admissibleMs, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨Nat.lt_succ_iff.mp h.1, h.2⟩
  · rintro ⟨hm, hAd⟩
    exact ⟨Nat.lt_succ_iff.mpr hm, hAd⟩

theorem mem_admissibleMs_range {sourceHMin : Nat → Nat} {L m : Nat}
    (hm : m ∈ admissibleMs sourceHMin L) :
    m ≤ Nat.sqrt (log2nat L) :=
  (mem_admissibleMs_iff sourceHMin L m).mp hm |>.1

theorem selector_eq_bot_iff (sourceHMin : Nat → Nat) (L : Nat) :
    selector sourceHMin L = ⊥ ↔
      ¬ ∃ m, Admissible sourceHMin L m := by
  constructor
  · intro hbot hex
    obtain ⟨m, hm⟩ := hex
    have hmem : m ∈ admissibleMs sourceHMin L := by
      exact (mem_admissibleMs_iff sourceHMin L m).2 ⟨hm.2.1, hm⟩
    have hempty : admissibleMs sourceHMin L = ∅ := by
      apply Finset.max_eq_bot.mp
      simpa [selector] using hbot
    rw [hempty] at hmem
    simpa using hmem
  · intro hno
    apply Finset.max_eq_bot.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    apply hno
    exact ⟨m, (mem_admissibleMs_iff sourceHMin L m).mp hm |>.2⟩

theorem selector_spec {sourceHMin : Nat → Nat} {L m : Nat}
    (hsel : selector sourceHMin L = (m : WithBot Nat)) :
    Admissible sourceHMin L m ∧
      ∀ n, Admissible sourceHMin L n → n ≤ m := by
  have hmax : (admissibleMs sourceHMin L).max = (m : WithBot Nat) := by
    simpa [selector] using hsel
  have hmem : m ∈ admissibleMs sourceHMin L := Finset.mem_of_max hmax
  have hAd : Admissible sourceHMin L m :=
    (mem_admissibleMs_iff sourceHMin L m).mp hmem |>.2
  refine ⟨hAd, ?_⟩
  intro n hn
  have hnm : (n : WithBot Nat) ≤ (m : WithBot Nat) := by
    have hnmax : (n : WithBot Nat) ≤ (admissibleMs sourceHMin L).max :=
      Finset.le_max ((mem_admissibleMs_iff sourceHMin L n).2 ⟨hn.2.1, hn⟩)
    exact hnmax.trans_eq hmax
  exact WithBot.coe_le_coe.mp hnm

private lemma log2nat_pow_two (k : Nat) : log2nat (2 ^ k) = k := by
  simp [log2nat]

private lemma log2nat_mono {a b : Nat} (h : a ≤ b) :
    log2nat a ≤ log2nat b := by
  unfold log2nat
  by_cases ha : a = 0
  · simp [ha]
  · have hb : b ≠ 0 := by
      intro hb
      apply ha
      exact Nat.eq_zero_of_le_zero (h.trans (by simp [hb]))
    simp [ha, hb]
    exact Nat.log_mono_right h

private lemma add_one_mul_pow_le_pow_add {d T : Nat} (hd : 0 < d) :
    d * 2 ^ T + 1 ≤ 2 ^ (d + T) := by
  have hdt : d + 1 ≤ 2 ^ d := by
    exact (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := d)))
  have hfirst : d * 2 ^ T + 1 ≤ (d + 1) * 2 ^ T := by
    calc
      d * 2 ^ T + 1 ≤ d * 2 ^ T + 2 ^ T :=
        Nat.add_le_add_left Nat.one_le_two_pow _
      _ = (d + 1) * 2 ^ T := by
        rw [Nat.add_mul]
        simp
  calc
    d * 2 ^ T + 1 ≤ (d + 1) * 2 ^ T := hfirst
    _ ≤ 2 ^ d * 2 ^ T := Nat.mul_le_mul_right _ hdt
    _ = 2 ^ (d + T) := (Nat.pow_add 2 d T).symm

private lemma sigmaBase_ge_eight_of_hBlock {L m : Nat}
    (hm : 256 ≤ m) (hh : 4 * m ≤ hBlock L m) :
    8 ≤ sigmaBase L m := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 256) hm
  have hquot : 4 ≤ hBlock L m / m := by
    apply (Nat.le_div_iff_mul_le hmpos).2
    simpa [Nat.mul_comm] using hh
  have hm1 : 1 ≤ m - 1 := by omega
  have hprod : 4 ≤ (hBlock L m / m) * (m - 1) := by
    have h := Nat.mul_le_mul hquot hm1
    simpa using h
  have hexp : 7 ≤ 2 * (hBlock L m / m) * (m - 1) := by
    have h := Nat.mul_le_mul_left 2 hprod
    have h8 : 8 ≤ 2 * (hBlock L m / m) * (m - 1) := by
      simpa [Nat.mul_assoc] using h
    exact (by decide : 7 ≤ 8).trans h8
  have hpow : 2 ^ 7 ≤ 2 ^ (2 * (hBlock L m / m) * (m - 1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have hgap : 128 ≤ gapRoot L m := by
    simpa [gapRoot] using hpow
  have hdiv : 128 / 16 ≤ gapRoot L m / 16 := Nat.div_le_div_right hgap
  simpa [sigmaBase] using hdiv

/-- Every fixed admissible value is eventually admissible, for every supplied
source threshold.  The witness is a power of two, and the proof applies to
all later `L`, not just to that witness. -/
theorem admissible_eventually (sourceHMin : Nat → Nat) {m : Nat}
    (hm : 256 ≤ m) :
    ∃ L0, ∀ L, L0 ≤ L → Admissible sourceHMin L m := by
  let d := q m * (m + 1)
  let b := bOf m
  let H := Nat.max (sourceHMin m) (4 * m)
  let T := 2 * b * H
  let K := Nat.max (Nat.max (m ^ 2) (b ^ 2)) (d + T)
  refine ⟨2 ^ K, ?_⟩
  intro L hL
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 256) hm
  have hbpos : 0 < b := by
    dsimp [b, bOf]
    positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos (Nat.sqrt_pos.2 hmpos) (Nat.succ_pos m)
  have hKlog : K ≤ log2nat L := by
    have hpow : 2 ^ K ≤ L := hL
    exact (le_of_eq (log2nat_pow_two K).symm).trans (log2nat_mono hpow)
  have hmsq : m ^ 2 ≤ log2nat L := by
    exact (le_max_left _ _).trans (le_max_left _ _ |>.trans hKlog)
  have hbsq : b ^ 2 ≤ log2nat L := by
    exact (le_max_right _ _).trans (le_max_left _ _ |>.trans hKlog)
  have hmroot : m ≤ Nat.sqrt (log2nat L) := by
    apply Nat.le_sqrt.mpr
    simpa [Nat.pow_two] using hmsq
  have hbroot : b ≤ Nat.sqrt (log2nat L) := by
    apply Nat.le_sqrt.mpr
    simpa [Nat.pow_two] using hbsq
  have hKdt : d + T ≤ K := le_max_right _ _
  have hdtK : d + T ≤ K := hKdt
  have hpowK : 2 ^ (d + T) ≤ 2 ^ K :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hdtK
  have hpowL : 2 ^ (d + T) ≤ L := hpowK.trans hL
  have hlarge : d * 2 ^ T + 1 ≤ L :=
    (add_one_mul_pow_le_pow_add hdpos).trans hpowL
  have hLpos : 0 < L := by
    exact lt_of_lt_of_le (by positivity : 0 < 2 ^ (d + T)) hpowL
  have hprod : d * 2 ^ T ≤ L - 1 := Nat.le_sub_of_add_le hlarge
  have hden : Nat.max d 1 = d := Nat.max_eq_left (Nat.succ_le_iff.mp hdpos)
  have hquot :
      (d * 2 ^ T) / d ≤ (L - 1) / d := Nat.div_le_div_right hprod
  have hnum : 2 ^ T ≤ blockNum L m := by
    have hcancel : (d * 2 ^ T) / d = 2 ^ T := Nat.mul_div_cancel_left _ hdpos
    have hquot' : 2 ^ T ≤ (L - 1) / Nat.max d 1 := by
      rw [hden]
      simpa [hcancel] using hquot
    simpa [blockNum, d, hLpos.ne'] using hquot'
  have hlognum : T ≤ log2nat (blockNum L m) := by
    exact (le_of_eq (log2nat_pow_two T).symm).trans (log2nat_mono hnum)
  have hquotH : H ≤ log2nat (blockNum L m) / (2 * b) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) hbpos)).2
    simpa [T, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlognum
  have hH : H ≤ hBlock L m := by
    have hmul : H ≤ b * (log2nat (blockNum L m) / (2 * b)) :=
      (Nat.le_mul_of_pos_left H hbpos).trans (Nat.mul_le_mul_left b hquotH)
    simpa [hBlock, b] using hmul
  have hsource : sourceHMin m ≤ hBlock L m :=
    (Nat.le_max_left _ _).trans hH
  have h4m : 4 * m ≤ hBlock L m :=
    (Nat.le_max_right _ _).trans hH
  have hdenL : d < L := by
    have hdpow : 2 ^ d ≤ 2 ^ K :=
      Nat.pow_le_pow_right (by decide : 0 < 2)
        ((le_trans (Nat.le_add_right d T) hdtK))
    exact (Nat.lt_two_pow_self (n := d)).trans_le (hdpow.trans hL)
  have hleaf : d * RBlock L m + 1 ≤ L := by
    simpa [d] using amplified_leaf_fit_of_hBlock hmpos hdenL
  have hsigma : 8 ≤ sigmaBase L m :=
    sigmaBase_ge_eight_of_hBlock hm h4m
  exact ⟨hm, hmroot, hbroot, by simpa [d] using hdenL, hleaf,
    bOf_dvd_hBlock L m, m_dvd_hBlock L m, hsource, hsigma⟩

theorem selector_eventually_exists (sourceHMin : Nat → Nat) :
    ∃ L0, ∀ L, L0 ≤ L → selector sourceHMin L ≠ ⊥ := by
  obtain ⟨L0, hL0⟩ := admissible_eventually sourceHMin (m := 256) (by decide)
  refine ⟨L0, ?_⟩
  intro L hL hbot
  apply (selector_eq_bot_iff sourceHMin L).mp hbot
  exact ⟨256, hL0 L hL⟩

theorem selector_unbounded (sourceHMin : Nat → Nat) (M : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat, selector sourceHMin L = (m : WithBot Nat) ∧
        M ≤ m ∧ Admissible sourceHMin L m := by
  let w := Nat.max 256 M
  have hw : 256 ≤ w := Nat.le_max_left _ _
  have hM : M ≤ w := Nat.le_max_right _ _
  obtain ⟨L0, hL0⟩ := admissible_eventually sourceHMin (m := w) hw
  refine ⟨L0, ?_⟩
  intro L hL
  have hwAd : Admissible sourceHMin L w := hL0 L hL
  have hwmem : w ∈ admissibleMs sourceHMin L :=
    (mem_admissibleMs_iff sourceHMin L w).2 ⟨hwAd.2.1, hwAd⟩
  obtain ⟨m : Nat, hmax⟩ := Finset.max_of_nonempty ⟨w, hwmem⟩
  have hsel : selector sourceHMin L = (m : WithBot Nat) := by
    change (admissibleMs sourceHMin L).max = (m : WithBot Nat)
    exact hmax
  have hspec := selector_spec hsel
  have hwm : w ≤ m := hspec.2 w hwAd
  exact ⟨m, hsel, hM.trans hwm, hspec.1⟩

end PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
