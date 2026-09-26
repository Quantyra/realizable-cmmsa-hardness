import PvNP.RealizableHardness.ActualVecLabel
import PvNP.RealizableHardness.ActualThreeSatXorStars
import PvNP.RealizableHardness.StarListDecoding
import Mathlib.Tactic.Linarith

/-!
Grassmann dual-restriction `Star`s at alphabet `alph h = ROf L`.

Labels are dual vectors `Fin (2^(2h))` via `vecOfFin`.  Leaf projection is
`restrictLow` onto a coordinate flag (`k < 2h`, not the identity).  3SAT
dependence is the clause-polarity vertex map `clausePol`.

Folding a 3LIN right-hand side is dual evaluation of the center label on
the first three basis vectors (`legal3Lin`).  The contradictory 3LIN pair
then has folded CSP value at most `1/2`.  That is the actual unsat value
of this folded dual family, not `zeta = 0` as a number, and it does **not**
meet `hn_zeta_beats_sigma` at integer `rho = rofSigma`.

This module does not pack CMMSA `Data` (restriction-only stars remain Yes
on unsat) and does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannDualStar

open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualVecLabel
open ActualThreeSatStarFamily
open ActualThreeSatCmmsaReduce
open ActualThreeSatXorStars
open ActualFinite3LinStarPCP
open StarListDecoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
attribute [local instance] Classical.propDecidable

theorem one_le_two_mul {h : Nat} (hh : 0 < h) : 1 ≤ 2 * h :=
  le_trans (Nat.succ_le_of_lt hh)
    (Nat.le_mul_of_pos_left h (by decide : 0 < 2))

theorem two_lt_two_mul {h : Nat} (hh : 1 < h) : 2 < 2 * h := by
  have : 2 * 2 ≤ 2 * h := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hh)
  exact Nat.lt_of_lt_of_le (by decide : 2 < 4) this

theorem three_lt_two_mul {h : Nat} (hh : 1 < h) : 3 < 2 * h :=
  Nat.lt_of_lt_of_le (by decide : 3 < 4)
    (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hh))

def dualStar {n h k m : Nat} (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n)
    (hsep : ∀ i, c ≠ leaf i) :
    Star (Fin n) (fun _ => Fin (alph h)) m where
  center := c
  leaf := leaf
  projection := fun _ a => restrictLow hk a
  separated := hsep

theorem dualStar_accepts_iff {n h k m : Nat} (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n)
    (hsep : ∀ i, c ≠ leaf i)
    (l : Labeling (fun _ : Fin n => Fin (alph h))) :
    (dualStar hk c leaf hsep).accepts l ↔
      ∀ i, restrictLow hk (l (leaf i)) = l c :=
  Iff.rfl

theorem one_lt_two_mul {h : Nat} (hh : 0 < h) : 1 < 2 * h :=
  Nat.lt_of_lt_of_le (by decide : 1 < 2)
    (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hh))

/-- `k = 1` dual restriction is not the identity map on labels. -/
theorem dualStar_proj_ne_id {h : Nat} (hh : 0 < h) {n m : Nat}
    (c : Fin n) (leaf : Fin m → Fin n) (hsep : ∀ i, c ≠ leaf i)
    (i : Fin m) :
    (dualStar (one_le_two_mul hh) c leaf hsep).projection i
        ⟨2, two_pow_lt_two_pow (one_lt_two_mul hh)⟩ ≠
      ⟨2, two_pow_lt_two_pow (one_lt_two_mul hh)⟩ :=
  restrictLow_ne_id (one_lt_two_mul hh)

def zeroLabel {n h : Nat} : Labeling (fun _ : Fin n => Fin (alph h)) :=
  fun _ => ⟨0, alph_pos h⟩

/-- Dual evaluation of a label on a basis vector. -/
def evalBit {h : Nat} (a : Fin (alph h)) (i : Fin (2 * h)) : ZMod 2 :=
  vecOfFin a i

theorem restrictLow_zero {h k : Nat} (hk : k ≤ 2 * h) :
    restrictLow hk (⟨0, alph_pos h⟩ : Fin (alph h)) = ⟨0, alph_pos h⟩ :=
  Fin.ext (Nat.zero_mod _)

theorem evalBit_restrictLow {h k : Nat} (hk : k ≤ 2 * h)
    (a : Fin (alph h)) (i : Fin (2 * h)) (hi : i.val < k) :
    evalBit (restrictLow hk a) i = evalBit a i := by
  unfold evalBit vecOfFin bit restrictLow
  have hbit : (a.val % 2 ^ k).testBit i.val = a.val.testBit i.val := by
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  simp [hbit]

/-- Dual restriction uniquely recovers the low `k` coordinates of a label. -/
theorem restrictLow_evalBit_eq {h k : Nat} (hk : k ≤ 2 * h)
    (a b : Fin (alph h)) (hEq : restrictLow hk a = restrictLow hk b)
    (i : Fin (2 * h)) (hi : i.val < k) :
    evalBit a i = evalBit b i := by
  have ha := evalBit_restrictLow hk a i hi
  have hb := evalBit_restrictLow hk b i hi
  exact ha.symm.trans ((congrArg (fun z => evalBit z i) hEq).trans hb)

theorem zeroLabel_accepts_dualStar {n h k m : Nat} (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (hsep : ∀ i, c ≠ leaf i) :
    (dualStar hk c leaf hsep).accepts (zeroLabel (n := n) (h := h)) := by
  intro i
  simp [dualStar, zeroLabel, restrictLow_zero hk]

def basis3 {h : Nat} (hh : 1 < h) (i : Fin 3) : Fin (2 * h) :=
  ⟨i.val, Nat.lt_trans i.isLt (three_lt_two_mul hh)⟩

/-- Center label folds a 3LIN right-hand side by dual pairing on `e0+e1+e2`. -/
def legal3Lin {h : Nat} (hh : 1 < h) (a : Fin (alph h)) (rhs : ZMod 2) : Prop :=
  evalBit a (basis3 hh 0) + evalBit a (basis3 hh 1) + evalBit a (basis3 hh 2) = rhs

theorem legal3Lin_not_both {h : Nat} (hh : 1 < h) (a : Fin (alph h)) :
    ¬ (legal3Lin hh a 0 ∧ legal3Lin hh a 1) := by
  intro ⟨h0, h1⟩
  exact zero_ne_one (h0.symm.trans h1)

def pairLeaf : Fin 2 → Fin 3 := fun i => i.succ

theorem pair_separated (i : Fin 2) : (0 : Fin 3) ≠ pairLeaf i := by
  intro h
  exact Nat.succ_ne_zero i.val (congrArg Fin.val h).symm

def pairDualStar {h : Nat} (hh : 0 < h) :
    Star (Fin 3) (fun _ => Fin (alph h)) 2 :=
  dualStar (one_le_two_mul hh) 0 pairLeaf pair_separated

/-- Restriction agreement plus dual 3LIN folding at the shared center. -/
def foldedAccepts {h : Nat} (hh : 1 < h)
    (rhs : ZMod 2)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) : Prop :=
  (pairDualStar (lt_trans Nat.zero_lt_one hh)).accepts l ∧
    legal3Lin hh (l 0) rhs

theorem pair_folded_not_both {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    ¬ (foldedAccepts hh 0 l ∧ foldedAccepts hh 1 l) := by
  intro ⟨h0, h1⟩
  exact legal3Lin_not_both hh (l 0) ⟨h0.2, h1.2⟩

def pairP : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

theorem pairP_nonneg (q : Fin 2) : 0 ≤ pairP q :=
  div_nonneg (by norm_num) (by norm_num)

/-- Actual folded dual CSP value of the contradictory 3LIN pair. -/
noncomputable def foldedScore {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) : ℝ :=
  (if foldedAccepts hh 0 l then (1 : ℝ) / 2 else 0) +
    (if foldedAccepts hh 1 l then (1 : ℝ) / 2 else 0)

theorem foldedScore_le_half {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    foldedScore hh l ≤ (1 : ℝ) / 2 := by
  unfold foldedScore
  have hnot := pair_folded_not_both hh l
  by_cases h0 : foldedAccepts hh 0 l
  · have h1 : ¬ foldedAccepts hh 1 l := fun h1 => hnot ⟨h0, h1⟩
    simp [h0, h1]
  · simp [h0]
    split_ifs <;> norm_num

/-- Integer-rho HN still needs `zeta ≤ 5/(8 R^{m+1})`; `1/2` is not that bound. -/
theorem half_not_hn_zeta {L : Nat} (hR : 2 ≤ ROf L) :
    ¬ ((1 : Rat) / 2 ≤ (5 : Rat) /
      ((8 : Rat) * (ROf L : Rat) ^ (mOf L + 1))) := by
  intro hle
  have hdenpos : (0 : Rat) <
      (8 : Rat) * (ROf L : Rat) ^ (mOf L + 1) :=
    mul_pos (by norm_num)
      (pow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hR)) _)
  have hmul := (le_div_iff₀ hdenpos).mp hle
  have hsimp :
      ((1 : Rat) / 2) * ((8 : Rat) * (ROf L : Rat) ^ (mOf L + 1)) =
        4 * (ROf L : Rat) ^ (mOf L + 1) := by
    have : ((1 : Rat) / 2) * 8 = 4 := by norm_num
    rw [← mul_assoc, this]
  rw [hsimp] at hmul
  have hone : (1 : Rat) ≤ (ROf L : Rat) :=
    le_trans (by norm_num : (1 : Rat) ≤ 2) (Nat.cast_le.mpr hR)
  have hpow : (ROf L : Rat) ^ 1 ≤ (ROf L : Rat) ^ (mOf L + 1) :=
    pow_le_pow_right₀ hone (Nat.le_add_left 1 (mOf L))
  have hR1 : (ROf L : Rat) ^ 1 = (ROf L : Rat) := pow_one _
  have hRpow : (2 : Rat) ≤ (ROf L : Rat) ^ (mOf L + 1) :=
    (Nat.cast_le.mpr hR).trans (hR1.symm.trans_le hpow)
  have h8 : (8 : Rat) ≤ 4 * (ROf L : Rat) ^ (mOf L + 1) := by
    have hx : (8 : Rat) = 4 * 2 := by norm_num
    rw [hx]
    nlinarith
  exact (not_le_of_gt (lt_of_lt_of_le (by norm_num : (5 : Rat) < 8) h8)) hmul

def clauseDualStar {h : Nat} (hh : 0 < h) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length)
    (hsep : ∀ j : Fin 2, clausePol φ h3 i 0 ≠ clausePol φ h3 i j.succ) :
    Star (Fin (nPol φ)) (fun _ => Fin (alph h)) 2 :=
  dualStar (one_le_two_mul hh) (clausePol φ h3 i 0)
    (fun j => clausePol φ h3 i j.succ) hsep

theorem zeroLabel_accepts_clauseDualStar {h : Nat} (hh : 0 < h)
    (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (hsep : ∀ j : Fin 2, clausePol φ h3 i 0 ≠ clausePol φ h3 i j.succ) :
    (clauseDualStar hh φ h3 i hsep).accepts
      (zeroLabel (n := nPol φ) (h := h)) :=
  zeroLabel_accepts_dualStar (one_le_two_mul hh) _ _ hsep

end
end PvNP.RealizableHardness.ActualGrassmannDualStar
