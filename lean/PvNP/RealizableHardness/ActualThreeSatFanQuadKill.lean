import PvNP.RealizableHardness.ActualThreeSatGrassmannFan
import Mathlib.Algebra.BigOperators.Fin

/-!
Global 4-label witness that `fanData` is not manuscript `No`.

Every vertex lights `{0, 1+2^h, 2+2^{h+1}, 4+2^{h+2}}`.  Color `0` meets
RHS 0, and `1+2^h` meets RHS 1 after the fan's three shifts, so every
clause formula is true.  The cost is `4/R`.  Once `4 ≤ manuscriptSigma`
that cost lies under `manuscriptSigma / R`.

This is not a `Complexity.FP` `MapReducesVia`.  `fanEncFn` is a different
clause-0 encoder.  Theorem 1 is not assembled.
-/
namespace PvNP.RealizableHardness.ActualThreeSatFanQuadKill

open Complexity
open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualThreeSatLegalRes
open ActualThreeSatGrassmannRes
open ActualThreeSatDualWindow
open ActualThreeSatGrassmannFan
open ActualCertifiedManuscriptParameters
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def quadHot {n h : Nat} (_hh : 3 < h) : Fin (n * alph h) → Bool :=
  fun i =>
    decide (i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h ∨
      i.val % alph h = 2 + 2 ^ (h + 1) ∨ i.val % alph h = 4 + 2 ^ (h + 2))

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

private theorem quad1_lt {h : Nat} (hh : 3 < h) : 1 + 2 ^ h < alph h :=
  dualBit_lt (three_lt_h_to_pos hh)

private theorem quad2_lt {h : Nat} (hh : 3 < h) : 2 + 2 ^ (h + 1) < alph h := by
  simpa using shift_dual_lt_alph hh (j := 1) (by decide : (1 : Nat) ≤ 2)

private theorem quad3_lt {h : Nat} (hh : 3 < h) : 4 + 2 ^ (h + 2) < alph h := by
  simpa using shift_dual_lt_alph hh (j := 2) (by decide : (2 : Nat) ≤ 2)

private theorem quadHot_coord {n h : Nat} (hh : 3 < h) (v : Fin n)
    (a : Fin (alph h)) :
    quadHot (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 + 2 ^ h ∨ a.val = 2 + 2 ^ (h + 1) ∨
        a.val = 4 + 2 ^ (h + 2)) := by
  simp [quadHot, coord_mod (alph_pos h) v a]

private theorem quadHot_of_val {n h : Nat} (hh : 3 < h) (v : Fin n)
    (a : Fin (alph h))
    (ha : a.val = 0 ∨ a.val = 1 + 2 ^ h ∨ a.val = 2 + 2 ^ (h + 1) ∨
      a.val = 4 + 2 ^ (h + 2)) :
    quadHot (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      true := by
  rw [quadHot_coord hh v a]
  exact decide_eq_true ha

private theorem quadHot_eval_fan {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.eval (quadHot (n := resN L φ) hh) (fanFormula hh hm φ h3 i) =
      true := by
  rcases zmod2_eq_zero_or_one (clauseRhs φ h3 i) with h0 | h1
  · refine (eval_compileFan hh hm (quadHot (n := resN L φ) hh)
        (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
      ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [h0] using legalBoth_zero (three_lt_h_to_two_lt hh)
    · exact quadHot_of_val hh (resCenter φ h3 i) ⟨0, alph_pos _⟩ (by simp)
    · have hsh := restrictShift_zero (three_lt_h_to_pos hh) 0
      rw [hsh]
      exact quadHot_of_val hh
        (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩)
        ⟨0, alph_pos _⟩ (by simp)
    · have hsh := restrictShift_zero (three_lt_h_to_pos hh) 1
      rw [hsh]
      exact quadHot_of_val hh
        (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩)
        ⟨0, alph_pos _⟩ (by simp)
    · have hsh := restrictShift_zero (three_lt_h_to_pos hh) 2
      rw [hsh]
      exact quadHot_of_val hh
        (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩)
        ⟨0, alph_pos _⟩ (by simp)
  · refine (eval_compileFan hh hm (quadHot (n := resN L φ) hh)
        (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
      ⟨dualBit (three_lt_h_to_pos hh), ?_, ?_, ?_, ?_, ?_⟩
    · simpa [h1] using legalBoth_dualBit (three_lt_h_to_two_lt hh)
    · exact quadHot_of_val hh (resCenter φ h3 i)
        (dualBit (three_lt_h_to_pos hh)) (by simp [dualBit])
    · rw [restrictShift_id (three_lt_h_to_pos hh)]
      exact quadHot_of_val hh
        (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩)
        (dualBit (three_lt_h_to_pos hh)) (by simp [dualBit])
    · refine quadHot_of_val hh
        (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩)
        (restrictShift (three_lt_h_to_pos hh) 1
          (dualBit (three_lt_h_to_pos hh))) ?_
      rw [restrictShift_dualBit hh (by decide : (1 : Nat) ≤ 2)]
      simp
    · refine quadHot_of_val hh
        (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩)
        (restrictShift (three_lt_h_to_pos hh) 2
          (dualBit (three_lt_h_to_pos hh))) ?_
      rw [restrictShift_dualBit hh (by decide : (2 : Nat) ≤ 2)]
      simp

private theorem quad_vals_ne {h : Nat} (_hh : 3 < h) :
    (0 : Nat) ≠ 1 + 2 ^ h ∧ 0 ≠ 2 + 2 ^ (h + 1) ∧ 0 ≠ 4 + 2 ^ (h + 2) ∧
      1 + 2 ^ h ≠ 2 + 2 ^ (h + 1) ∧ 1 + 2 ^ h ≠ 4 + 2 ^ (h + 2) ∧
      2 + 2 ^ (h + 1) ≠ 4 + 2 ^ (h + 2) := by
  have hpow1 : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ, Nat.mul_comm]
  have hpow2 : 2 ^ (h + 2) = 2 * 2 ^ (h + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  omega

private theorem quad_weight {n h : Nat} (hn : 0 < n) (hh : 3 < h) :
    weight (compactWeights n (alph h) hn (alph_pos h))
      (quadHot (n := n) hh) = (4 : Rat) / (alph h : Rat) := by
  unfold weight compactWeights quadHot
  have hA := alph_pos h
  have hcard : ((n * alph h : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn hA).ne'
  have hre :
      (∑ i : Fin (n * alph h),
          if i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h ∨
              i.val % alph h = 2 + 2 ^ (h + 1) ∨
              i.val % alph h = 4 + 2 ^ (h + 2) then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        ∑ v : Fin n, ∑ a : Fin (alph h),
          if a.val = 0 ∨ a.val = 1 + 2 ^ h ∨ a.val = 2 + 2 ^ (h + 1) ∨
              a.val = 4 + 2 ^ (h + 2) then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval : (finProdFinEquiv (v, a)).val = a.val + alph h * v.val := rfl
    have hmod : (a.val + alph h * v.val) % alph h = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    simp [hval, hmod]
  have hdecide :
      (∑ i : Fin (n * alph h),
          if decide (i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h ∨
              i.val % alph h = 2 + 2 ^ (h + 1) ∨
              i.val % alph h = 4 + 2 ^ (h + 2)) = true then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        ∑ i : Fin (n * alph h),
          if i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h ∨
              i.val % alph h = 2 + 2 ^ (h + 1) ∨
              i.val % alph h = 4 + 2 ^ (h + 2) then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hdecide, hre]
  let a0 : Fin (alph h) := ⟨0, hA⟩
  let a1 : Fin (alph h) := ⟨1 + 2 ^ h, quad1_lt hh⟩
  let a2 : Fin (alph h) := ⟨2 + 2 ^ (h + 1), quad2_lt hh⟩
  let a3 : Fin (alph h) := ⟨4 + 2 ^ (h + 2), quad3_lt hh⟩
  have hne := quad_vals_ne hh
  have hinner : ∀ v : Fin n,
      (∑ a : Fin (alph h),
          if a.val = 0 ∨ a.val = 1 + 2 ^ h ∨ a.val = 2 + 2 ^ (h + 1) ∨
              a.val = 4 + 2 ^ (h + 2) then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        (4 : Rat) / ((n * alph h : Nat) : Rat) := by
    intro v
    have hfilter :
        (Finset.univ.filter fun a : Fin (alph h) =>
            a.val = 0 ∨ a.val = 1 + 2 ^ h ∨ a.val = 2 + 2 ^ (h + 1) ∨
              a.val = 4 + 2 ^ (h + 2)) =
          {a0, a1, a2, a3} := by
      ext a
      constructor
      · intro ha
        have hv := by simpa using ha
        simp [Finset.mem_insert, Finset.mem_singleton]
        rcases hv with hval | hval | hval | hval
        · exact Or.inl (Fin.ext hval)
        · exact Or.inr (Or.inl (Fin.ext hval))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext hval)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext hval)))
      · intro ha
        simp [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simp [a0, a1, a2, a3]
    have hcard : ({a0, a1, a2, a3} : Finset (Fin (alph h))).card = 4 := by
      have h10 : a1 ≠ a0 := Fin.ne_of_val_ne hne.1.symm
      have h20 : a2 ≠ a0 := Fin.ne_of_val_ne hne.2.1.symm
      have h30 : a3 ≠ a0 := Fin.ne_of_val_ne hne.2.2.1.symm
      have h21 : a2 ≠ a1 := Fin.ne_of_val_ne hne.2.2.2.1.symm
      have h31 : a3 ≠ a1 := Fin.ne_of_val_ne hne.2.2.2.2.1.symm
      have h32 : a3 ≠ a2 := Fin.ne_of_val_ne hne.2.2.2.2.2.symm
      have n01 : a0 ∉ ({a1, a2, a3} : Finset (Fin (alph h))) := by
        simp [Finset.mem_insert, Finset.mem_singleton, h10.symm, h20.symm, h30.symm]
      have n12 : a1 ∉ ({a2, a3} : Finset (Fin (alph h))) := by
        simp [Finset.mem_insert, Finset.mem_singleton, h21.symm, h31.symm]
      have n23 : a2 ∉ ({a3} : Finset (Fin (alph h))) := by
        simpa [Finset.mem_singleton] using h32.symm
      rw [Finset.card_insert_of_notMem n01, Finset.card_insert_of_notMem n12,
        Finset.card_insert_of_notMem n23, Finset.card_singleton]
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    norm_num
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  have hnR : (n : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hAR : (alph h : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  field_simp [hcard, hnR, hAR]

private theorem fan_len {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (fanData hh hm φ h3 hM).weights.length = resN L φ * alph (legalH L) := by
  simp [fanData, indexedData]

private theorem fan_quad_cost {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (fanData hh hm φ h3 hM).cost
      (fun i => quadHot (n := resN L φ) hh ⟨i.val,
        (fan_len hh hm φ h3 hM) ▸ i.isLt⟩) =
      (4 : Rat) / (alph (legalH L) : Rat) := by
  unfold Data.cost Data.coordinateWeights
  simp only [fanData, indexedData, List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (resN L φ) (alph (legalH L))
        (resN_pos L φ) (alph_pos (legalH L)))).length ≃
      Fin (resN L φ * alph (legalH L)) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := quad_weight (resN_pos L φ) hh
  unfold weight compactWeights quadHot at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights, quadHot]

private theorem fan_quad_sat {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (fanData hh hm φ h3 hM).satisfaction
      (fun i => quadHot (n := resN L φ) hh ⟨i.val,
        (fan_len hh hm φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (fanData hh hm φ h3 hM).formulas.length) := by
    simp [fanData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (fanData hh hm φ h3 hM).formulas.length,
      Formula.eval
        (fun i => quadHot (n := resN L φ) hh ⟨i.val,
          (fan_len hh hm φ h3 hM) ▸ i.isLt⟩)
        ((fanData hh hm φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [fanData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
      (fanFormulas hh hm φ h3) (compactBudget (alph (legalH L)))
      (fun i => quadHot (n := resN L φ) hh ⟨i.val, by
        simpa [fanData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [fanData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [fanData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (fanFormulas hh hm φ h3 ⟨j.val, hj⟩)) ?_).trans
      (quadHot_eval_fan hh hm φ h3 ⟨j.val, hj⟩)
    funext v
    exact congrArg (quadHot (n := resN L φ) hh) (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => quadHot (n := resN L φ) hh ⟨i.val,
          (fan_len hh hm φ h3 hM) ▸ i.isLt⟩)
        ((fanData hh hm φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

private theorem four_div_le_manuscript_budget {L : Nat}
    (h4 : 4 ≤ manuscriptSigma L) :
    (4 : Rat) / (ROf L : Rat) ≤
      (manuscriptSigma L : Rat) * compactBudget (ROf L) := by
  have hRpos : (0 : Rat) < (ROf L : Rat) := Nat.cast_pos.mpr (ROf_pos L)
  have hσ : (4 : Rat) ≤ (manuscriptSigma L : Rat) := Nat.cast_le.mpr h4
  unfold compactBudget
  have : (4 : Rat) / (ROf L : Rat) ≤ (manuscriptSigma L : Rat) / (ROf L : Rat) :=
    div_le_div_of_nonneg_right hσ hRpos.le
  simpa [div_eq_mul_inv] using this

/-- `fanData` is not manuscript `No`: four labels per vertex satisfy every
clause and cost `4/R`. -/
theorem fanData_not_no_manuscript {L : Nat} (h : 256 ≤ mOf L)
    (hh : 3 < legalH L) (h4 : 4 ≤ manuscriptSigma L)
    (hγ1 : manuscriptGamma L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    ¬ No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (fanData hh (paramM_ge_3 h) φ h3 hM)
        (fanData_valid h hh φ h3 hM)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  have hx := hall
    (fun i => quadHot (n := resN L φ) hh ⟨i.val,
      (fan_len hh (paramM_ge_3 h) φ h3 hM) ▸ i.isLt⟩)
  have hcost := fan_quad_cost hh (paramM_ge_3 h) φ h3 hM
  have hsat := fan_quad_sat hh (paramM_ge_3 h) φ h3 hM
  have hb : (fanData hh (paramM_ge_3 h) φ h3 hM).budget =
      compactBudget (alph (legalH L)) := rfl
  have hle : (fanData hh (paramM_ge_3 h) φ h3 hM).cost
      (fun i => quadHot (n := resN L φ) hh ⟨i.val,
        (fan_len hh (paramM_ge_3 h) φ h3 hM) ▸ i.isLt⟩) ≤
      (manuscriptSigma L : Rat) *
        (fanData hh (paramM_ge_3 h) φ h3 hM).budget := by
    rw [hcost, hb, legalH, resH, alph_eq_ROf]
    exact four_div_le_manuscript_budget h4
  have h1lt : (1 : Rat) < manuscriptGamma L := by simpa [hsat] using hx hle
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- For every large `L`, manuscript `σ` is at least 4 and `fanData` misses
manuscript `No` on every nonempty 3CNF.  `3 < legalH` stays a hypothesis. -/
theorem fanData_fails_manuscript_eventually :
    ∃ L0, ∀ L, L0 ≤ L →
      256 ≤ mOf L ∧ 4 ≤ manuscriptSigma L ∧
        0 < manuscriptGamma L ∧ manuscriptGamma L < 1 ∧
        ∀ (h : 256 ≤ mOf L) (hh : 3 < legalH L)
          (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length),
          ¬ No (manuscriptSigma L) (manuscriptGamma L)
            (ofData (fanData hh (paramM_ge_3 h) φ h3 hM)
              (fanData_valid h hh φ h3 hM)) := by
  obtain ⟨Lm, hm⟩ := mOf_unbounded 256
  obtain ⟨Ls, hS⟩ := certifiedSigma_ge_four_eventual
  obtain ⟨Lg, hG⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max Lm (max Ls Lg), ?_⟩
  intro L hL
  have hLm : Lm ≤ L := (le_max_left _ _).trans hL
  have hLs : Ls ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLg : Lg ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have h256 : 256 ≤ mOf L := hm L hLm
  have h4 : 4 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨h256, h4, hγp.1, hγp.2, ?_⟩
  intro h hh φ h3 hM
  exact fanData_not_no_manuscript h hh h4 hγp.2 φ h3 hM

end
end PvNP.RealizableHardness.ActualThreeSatFanQuadKill
