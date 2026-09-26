import PvNP.RealizableHardness.ActualThreeSatPcpPack
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
HN compilation pack: 1-hot completeness of 3SAT-dependent XOR-star `Data`,
and the list-decoding transfer from a small CSP value to CMMSA satisfaction
`≤ 3/4`.

A labeling that accepts every clause XOR star yields `Yes 0` via the
coordinate 1-hot of that labeling (cost `1/ROf`, satisfaction `1`).
`witness_mass_le_three_quarters` then sends a family of CSP value `≤ zeta`
meeting `(8 ρ)^{m+1} zeta ≤ 5/8` to satisfaction `≤ 3/4` on lists of
budget `≤ ρ`.  Instantiating `ρ = σ_L` needs a Grassmann-scale `zeta`,
which this 2-leaf XOR family does not have (`twoLabel` remains cheap).

Not `if-sat`.  Not `Complexity.FP`.  Does not inhabit `hSrcCmmsa`.
Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatHnPack

open Complexity
open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFamily
open ActualThreeSatXorStars
open ActualThreeSatGraphYes
open ActualRestrictXorCompile
open ActualXorLabel
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open StarListDecoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

private theorem coord_div {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) / A = v.val := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm, Nat.mul_add_div hA,
    Nat.div_eq_of_lt a.isLt, Nat.add_zero]

private theorem finProd_val {n A : Nat} (v : Fin n) (a : Fin A) :
    (finProdFinEquiv (v, a)).val = a.val + A * v.val :=
  rfl

/-- Coordinate 1-hot of a global labeling. -/
def labelOneHot {n h : Nat} (_hh : 0 < h) (l : Fin n → Fin (alph h)) :
    Fin (n * alph h) → Bool :=
  fun i =>
    decide (i.val % alph h =
      (l ⟨i.val / alph h,
        (Nat.div_lt_iff_lt_mul (alph_pos h)).mpr i.isLt⟩).val)

theorem labelOneHot_coord {n h : Nat} (hh : 0 < h)
    (l : Fin n → Fin (alph h)) (v : Fin n) (a : Fin (alph h)) :
    labelOneHot hh l ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = (l v).val) := by
  unfold labelOneHot
  have hmod := coord_mod (alph_pos h) v a
  have hdiv := coord_div (alph_pos h) v a
  simp [hmod, hdiv]

theorem labelOneHot_cost {n h : Nat} (hn : 0 < n) (hh : 0 < h)
    (l : Fin n → Fin (alph h)) :
    weight (compactWeights n (alph h) hn (alph_pos h))
      (labelOneHot hh l) = compactBudget (alph h) := by
  unfold weight compactWeights compactBudget labelOneHot
  have hA := alph_pos h
  have hcard : ((n * alph h : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn hA).ne'
  have hre :
      (∑ i : Fin (n * alph h),
          if i.val % alph h =
              (l ⟨i.val / alph h,
                (Nat.div_lt_iff_lt_mul hA).mpr i.isLt⟩).val then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        ∑ v : Fin n, ∑ a : Fin (alph h),
          if a.val = (l v).val then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval := finProd_val (A := alph h) v a
    have hmod : (a.val + alph h * v.val) % alph h = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    have hdiv : (a.val + alph h * v.val) / alph h = v.val := by
      rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt a.isLt, Nat.zero_add]
    simp [hval, hmod, hdiv]
  have hdecide :
      (∑ i : Fin (n * alph h),
          if decide (i.val % alph h =
              (l ⟨i.val / alph h,
                (Nat.div_lt_iff_lt_mul hA).mpr i.isLt⟩).val) = true then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        ∑ i : Fin (n * alph h),
          if i.val % alph h =
              (l ⟨i.val / alph h,
                (Nat.div_lt_iff_lt_mul hA).mpr i.isLt⟩).val then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hdecide, hre]
  have hinner : ∀ v : Fin n,
      (∑ a : Fin (alph h),
          if a.val = (l v).val then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        (1 : Rat) / ((n * alph h : Nat) : Rat) := by
    intro v
    have hA0 :
        (Finset.univ.filter fun a : Fin (alph h) => a.val = (l v).val) =
          {l v} := by
      ext a
      constructor
      · intro ha
        exact Finset.mem_singleton.2 (Fin.ext (by simpa using ha))
      · intro ha
        have : a = l v := Finset.mem_singleton.1 ha
        simpa [this]
    simp [Finset.sum_ite, hA0]
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  field_simp [hcard]

private theorem xorStar_len {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (xorStarData hh φ h3 hM).weights.length = nPol φ * alph h := by
  simp [xorStarData, indexedData]

private theorem xorStar_cost_oneHot {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (l : Fin (nPol φ) → Fin (alph h)) :
    (xorStarData hh φ h3 hM).cost
      (fun i => labelOneHot hh l ⟨i.val,
        (xorStar_len hh φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph h) := by
  unfold Data.cost Data.coordinateWeights weight xorStarData indexedData
  simp only [List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (nPol φ) (alph h) (nPol_pos φ) (alph_pos h))).length ≃
      Fin (nPol φ * alph h) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := labelOneHot_cost (nPol_pos φ) hh l
  unfold weight compactWeights labelOneHot at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights, labelOneHot]

private theorem restrictLow_id {h : Nat} (a : Fin (alph h)) :
    restrictLow (le_rfl : 2 * h ≤ 2 * h) a = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem xorFin_cancel {h : Nat} (a b : Fin (alph h)) :
    xorFin (xorFin a b) b = a :=
  Fin.ext (by
    simp [xorFin, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])

private theorem decide_val_eq {h : Nat} {a b : Fin (alph h)}
    (hdec : decide (a.val = b.val) = true) : a = b :=
  Fin.ext (of_decide_eq_true hdec)

/-- 1-hot of `l` satisfies a clause XOR formula iff the three slot labels
of `l` form an accepting XOR triple. -/
theorem eval_clauseXor_labelOneHot {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) (l : Fin (nPol φ) → Fin (alph h)) :
    Formula.eval (labelOneHot (n := nPol φ) hh l)
      (clauseXorFormula hh φ h3 i) = true ↔
      (∀ j : Fin 2,
        xorFin (l (clausePol φ h3 i j.succ)) (clauseMask hh φ h3 i j) =
          l (clausePol φ h3 i 0)) := by
  refine (eval_compileResXor (le_rfl : 2 * h ≤ 2 * h)
      (labelOneHot (n := nPol φ) hh l)
      (clausePol φ h3 i 0)
      (fun j : Fin 2 => clausePol φ h3 i j.succ)
      (clauseMask hh φ h3 i)).trans ?_
  constructor
  · rintro ⟨b, hc, hleaf⟩
    have hb : b = l (clausePol φ h3 i 0) := by
      have hcoord := labelOneHot_coord hh l (clausePol φ h3 i 0) b
      have : decide (b.val = (l (clausePol φ h3 i 0)).val) = true := by
        simpa [hcoord] using hc
      exact decide_val_eq this
    subst hb
    intro j
    have hj := hleaf j
    rw [restrictLow_id] at hj
    have hcoord := labelOneHot_coord hh l (clausePol φ h3 i j.succ)
      (xorFin (l (clausePol φ h3 i 0)) (clauseMask hh φ h3 i j))
    have : decide
        ((xorFin (l (clausePol φ h3 i 0)) (clauseMask hh φ h3 i j)).val =
          (l (clausePol φ h3 i j.succ)).val) = true := by
      simpa [hcoord] using hj
    have hEq : xorFin (l (clausePol φ h3 i 0)) (clauseMask hh φ h3 i j) =
        l (clausePol φ h3 i j.succ) :=
      decide_val_eq this
    rw [← hEq]
    exact xorFin_cancel (l (clausePol φ h3 i 0)) (clauseMask hh φ h3 i j)
  · intro hall
    refine ⟨l (clausePol φ h3 i 0), ?_, ?_⟩
    · rw [labelOneHot_coord hh l (clausePol φ h3 i 0)
        (l (clausePol φ h3 i 0))]
      simp
    · intro j
      rw [restrictLow_id]
      have hleaf :
          xorFin (l (clausePol φ h3 i 0)) (clauseMask hh φ h3 i j) =
            l (clausePol φ h3 i j.succ) := by
        have hacc := hall j
        simpa [xorFin_cancel] using
          congrArg (fun a => xorFin a (clauseMask hh φ h3 i j)) hacc.symm
      rw [labelOneHot_coord hh l (clausePol φ h3 i j.succ)
        (xorFin (l (clausePol φ h3 i 0)) (clauseMask hh φ h3 i j))]
      simp [hleaf]

/-- Zero labeling accepts every all-positive unit clause XOR star. -/
def zeroLab {n h : Nat} (_hh : 0 < h) : Fin n → Fin (alph h) :=
  fun _ => ⟨0, alph_pos h⟩

theorem satUnit_clauseMask_zero {h : Nat} (hh : 0 < h) (j : Fin 2) :
    clauseMask hh satUnit satUnit_is3 ⟨0, satUnit_len⟩ j =
      ⟨0, alph_pos h⟩ := by
  fin_cases j <;> rfl

theorem satUnit_zeroLab_accepts {h : Nat} (hh : 0 < h) :
    ∀ j : Fin 2,
      xorFin (zeroLab (n := nPol satUnit) hh
          (clausePol satUnit satUnit_is3 ⟨0, satUnit_len⟩ j.succ))
        (clauseMask hh satUnit satUnit_is3 ⟨0, satUnit_len⟩ j) =
        zeroLab (n := nPol satUnit) hh
          (clausePol satUnit satUnit_is3 ⟨0, satUnit_len⟩ 0) := by
  intro j
  simp [zeroLab, satUnit_clauseMask_zero hh j, xorFin_zero]

private theorem xorStar_sat_oneHot {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (l : Fin (nPol φ) → Fin (alph h))
    (hacc : ∀ i : Fin φ.length, ∀ j : Fin 2,
      xorFin (l (clausePol φ h3 i j.succ)) (clauseMask hh φ h3 i j) =
        l (clausePol φ h3 i 0)) :
    (xorStarData hh φ h3 hM).satisfaction
      (fun i => labelOneHot hh l ⟨i.val,
        (xorStar_len hh φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (xorStarData hh φ h3 hM).formulas.length) := by
    simp [xorStarData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (xorStarData hh φ h3 hM).formulas.length,
      Formula.eval
        (fun i => labelOneHot hh l ⟨i.val,
          (xorStar_len hh φ h3 hM) ▸ i.isLt⟩)
        ((xorStarData hh φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [xorStarData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (nPol φ) (alph h) (nPol_pos φ) (alph_pos h))
      (xorFormulas hh φ h3) (compactBudget (alph h))
      (fun i => labelOneHot hh l ⟨i.val, by
        simpa [xorStarData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [xorStarData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [xorStarData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (xorFormulas hh φ h3 ⟨j.val, hj⟩)) ?_).trans
      ((eval_clauseXor_labelOneHot hh φ h3 ⟨j.val, hj⟩ l).mpr
        (hacc ⟨j.val, hj⟩))
    funext v
    exact congrArg (labelOneHot hh l) (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => labelOneHot hh l ⟨i.val,
          (xorStar_len hh φ h3 hM) ▸ i.isLt⟩)
        ((xorStarData hh φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem xorStarData_yes_of_labeling {L h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) (hleaves : alph h * 3 ≤ L)
    (l : Fin (nPol φ) → Fin (alph h))
    (hacc : ∀ i : Fin φ.length, ∀ j : Fin 2,
      xorFin (l (clausePol φ h3 i j.succ)) (clauseMask hh φ h3 i j) =
        l (clausePol φ h3 i 0)) :
    Yes 0 (ofData (xorStarData hh φ h3 hM)
      (xorStarData_valid hh φ h3 hM hleaves)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => labelOneHot hh l ⟨i.val,
      (xorStar_len hh φ h3 hM) ▸ i.isLt⟩, ?_, ?_⟩
  · have hcost := xorStar_cost_oneHot hh φ h3 hM l
    have hle : compactBudget (alph h) ≤ (xorStarData hh φ h3 hM).budget := by
      simp [xorStarData, indexedData]
    exact hcost.trans_le hle
  · have hsat := xorStar_sat_oneHot hh φ h3 hM l hacc
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

/-- Sat unit 3CNF XOR-star packing is `Yes 0` via the zero labeling. -/
theorem xorStarData_yes_satUnit {L h : Nat} (hh : 0 < h)
    (hleaves : alph h * 3 ≤ L) :
    Yes 0 (ofData (xorStarData hh satUnit satUnit_is3 satUnit_len)
      (xorStarData_valid hh satUnit satUnit_is3 satUnit_len hleaves)) :=
  xorStarData_yes_of_labeling hh satUnit satUnit_is3 satUnit_len hleaves
    (zeroLab hh) (fun i => by
      have hi : i = ⟨0, satUnit_len⟩ := by
        apply Fin.ext
        have : i.val < 1 := by
          simpa [satUnit] using i.isLt
        exact Nat.lt_one_iff.mp this
      subst hi
      exact satUnit_zeroLab_accepts hh)

theorem xorStarData_yes_satUnit_mem {L h : Nat} (hh : 0 < h)
    (hleaves : alph h * 3 ≤ L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    encodeData (xorStarData hh satUnit satUnit_is3 satUnit_len)
        (xorStarData_valid hh satUnit satUnit_is3 satUnit_len hleaves) ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).yesInstances :=
  cmmsaPromise_yes_of_encode hσ hγ0 hγ1
    (ofData (xorStarData hh satUnit satUnit_is3 satUnit_len)
      (xorStarData_valid hh satUnit satUnit_is3 satUnit_len hleaves))
    (xorStarData_yes_satUnit hh hleaves)

/-- List-decoding endpoint at integer `ρ = σ_L` for arity-2 stars.
A Grassmann-scale `zeta` is required; `1/2` does not meet it. -/
theorem hn_rofSigma_arity2 {L : Nat} (hσ : 0 < rofSigma L) (zeta : Rat)
    (hz : zeta ≤ (5 : Rat) /
      ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (2 + 1))) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (2 + 1) * zeta ≤ (5 : Rat) / 8 := by
  have hden : (0 : Rat) <
      (8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (2 + 1) :=
    mul_pos (by norm_num)
      (pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (by decide : 0 < 8) hσ)) _)
  have hmul : zeta * ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (2 + 1)) ≤ 5 :=
    (le_div_iff₀ hden).mp hz
  have hpow : ((8 : Rat) * (rofSigma L : Rat)) ^ (2 + 1) =
      ((8 * rofSigma L : Nat) : Rat) ^ (2 + 1) := by
    simp [Nat.cast_mul]
  rw [hpow]
  have hrew : ((8 * rofSigma L : Nat) : Rat) ^ (2 + 1) * zeta =
      (zeta * ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (2 + 1))) / 8 := by
    field_simp [hden.ne']
  rw [hrew]
  exact div_le_div_of_nonneg_right hmul (by norm_num)

/-- `zeta = 0` meets the arity-2 integer-`σ_L` HN bound.  2-leaf XOR
families on unsat 3SAT do not achieve this `zeta`. -/
theorem zero_zeta_arity2_hn {L : Nat} (_hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (2 + 1) * (0 : Rat) ≤ (5 : Rat) / 8 := by
  simp
  norm_num

/-- Transfer: CMMSA satisfaction `≤ 3/4` is strictly below `4/5`.
This is the compilation `γ` of HN Lemma 4.6, not manuscript `γ_L`. -/
theorem three_quarters_lt_four_fifths : (3 / 4 : Rat) < (4 / 5 : Rat) := by
  norm_num

end
end PvNP.RealizableHardness.ActualThreeSatHnPack
