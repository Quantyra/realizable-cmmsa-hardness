import PvNP.RealizableHardness.ActualThreeSatXorStars
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import Mathlib.Algebra.BigOperators.Fin

/-!
3SAT-dependent Grassmann-alphabet packing with `Yes 0` completeness, and
explicit cheap witnesses that polarity-OR / XOR-star families are not `No`.

* `threeSatToStarBits` is `encodeData` of `paramStarData` (clause polarity
  ORs at alphabet `ROf L`).  Sat 3CNF encodings are `cmmsaPromise` yes-
  instances.  3SAT data lives in the tree, not a trailing remainder.
* `allResidue0` lights label `0` at every polarity.  Cost equals the
  honest budget `1/ROf L ≤ σ_L · budget`, and every clause OR is true, so
  `paramStarData` is not `No σ_L γ_L`.  The same witness misses manuscript
  `No` once `1 ≤ manuscriptSigma` and `manuscriptGamma < 1`.
* `twoLabel` lights labels `0` and `1` at every polarity.  Cost `2/ROf L`
  is cheap once `16 ≤ ROf L`, and every `compileResXor` clause is true, so
  `xorStarData` is not `No σ_L γ_L`.  Once `2 ≤ manuscriptSigma`, the same
  cost is at most `manuscriptSigma · (1/ROf)` without `8 * rofSigma = ROf`.

Neither family inhabits `hSrcCmmsa` or a many-valued `Complexity.FP`
`MapReducesVia`.  Live polarity-OR coordinates are label `0` only; XOR
stars have a two-label cover of every clause, sat or unsat.  Not `if-sat`,
not identity, not LeafFold/`unsatCnf`.  Checking-transducer `mem_FP` is
not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatPcpPack

open Complexity
open Complexity.SAT
open RandomizedReduction
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFamily
open ActualThreeSatXorStars
open ActualThreeSatGraphYes
open ActualRestrictXorCompile
open ActualXorLabel
open ActualFinite3LinStarPCP
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
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

private theorem residue0_weight {n A : Nat} (hn : 0 < n) (hA : 0 < A) :
    weight (compactWeights n A hn hA) (honest (n := n) hA) =
      compactBudget A := by
  unfold weight compactWeights compactBudget honest
  have hcard : ((n * A : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn hA).ne'
  have hre :
      (∑ i : Fin (n * A),
          if i.val % A = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        ∑ v : Fin n, ∑ a : Fin A,
          if a.val = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval := finProd_val (A := A) v a
    have hmod : (a.val + A * v.val) % A = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    simp [hval, hmod]
  have hdecide :
      (∑ i : Fin (n * A),
          if decide (i.val % A = 0) = true then
            (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        ∑ i : Fin (n * A),
          if i.val % A = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hdecide, hre]
  have hinner : ∀ v : Fin n,
      (∑ a : Fin A,
          if a.val = 0 then (1 : Rat) / ((n * A : Nat) : Rat) else 0) =
        (1 : Rat) / ((n * A : Nat) : Rat) := by
    intro v
    have hA0 : (Finset.univ.filter fun a : Fin A => a.val = 0) = {⟨0, hA⟩} := by
      ext a
      constructor
      · intro ha
        exact Finset.mem_singleton.2 (Fin.ext (by simpa using ha))
      · intro ha
        have : a = ⟨0, hA⟩ := Finset.mem_singleton.1 ha
        simpa [this]
    simp [Finset.sum_ite, hA0]
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  field_simp [hcard]

private theorem starData_len {φ : CNF} (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    {A : Nat} (hA : 0 < A) :
    (starData φ h3 hM hA).weights.length = nPol φ * A := by
  simp [starData, indexedData]

private theorem starData_cost_residue0 {φ : CNF} (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) {A : Nat} (hA : 0 < A) :
    (starData φ h3 hM hA).cost
      (fun i => honest (n := nPol φ) hA ⟨i.val,
        (starData_len h3 hM hA) ▸ i.isLt⟩) =
      compactBudget A := by
  have hlen := starData_len h3 hM hA
  unfold Data.cost Data.coordinateWeights weight honest starData indexedData
  simp only [List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (nPol φ) A (nPol_pos φ) hA)).length ≃
      Fin (nPol φ * A) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := residue0_weight (nPol_pos φ) hA
  unfold weight compactWeights honest at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights]

private theorem eval_varAt_residue0 {n A : Nat} (hA : 0 < A)
    (v : Fin n) (a : Fin A) :
    Formula.eval (honest (n := n) hA) (varAt hA v a) = decide (a.val = 0) := by
  simp only [varAt, Formula.eval, honest]
  rw [coord_mod hA v a]

private theorem eval_paddedLit_residue0 {φ : CNF} {A : Nat} (hA : 0 < A)
    (ℓ : Lit) (hℓ : ℓ.var < nVars φ) :
    Formula.eval (honest (n := nPol φ) hA) (paddedLit hA ℓ hℓ) = true := by
  simpa [paddedLit] using eval_varAt_residue0 hA (litIndex φ ℓ hℓ) ⟨0, hA⟩

private theorem eval_paddedClause_residue0 {φ : CNF} {A : Nat} (hA : 0 < A)
    (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula.eval (honest (n := nPol φ) hA) (paddedClause hA c hc hv) = true := by
  have h0 := eval_paddedLit_residue0 (φ := φ) hA (clauseNth c hc 0)
    (hv _ (List.get_mem c _))
  have h1 := eval_paddedLit_residue0 (φ := φ) hA (clauseNth c hc 1)
    (hv _ (List.get_mem c _))
  have h2 := eval_paddedLit_residue0 (φ := φ) hA (clauseNth c hc 2)
    (hv _ (List.get_mem c _))
  simp [paddedClause, or3, Formula.eval, h0, h1, h2]

private theorem starFormulas_eval_residue0 {φ : CNF} (h3 : φ.Is3CNF)
    {A : Nat} (hA : 0 < A) (j : Fin φ.length) :
    Formula.eval (honest (n := nPol φ) hA) (starFormulas φ h3 hA j) = true := by
  simpa [starFormulas] using
    eval_paddedClause_residue0 (φ := φ) hA φ[j.val] (h3 _ (List.get_mem φ j))
      (fun ℓ hℓ => lit_var_lt_nVars φ φ[j.val] ℓ (List.get_mem φ j) hℓ)

private theorem starData_sat_residue0 {φ : CNF} (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) {A : Nat} (hA : 0 < A) :
    (starData φ h3 hM hA).satisfaction
      (fun i => honest (n := nPol φ) hA ⟨i.val,
        (starData_len h3 hM hA) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (starData φ h3 hM hA).formulas.length) := by
    simp [starData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (starData φ h3 hM hA).formulas.length,
      Formula.eval
        (fun i => honest (n := nPol φ) hA ⟨i.val,
          (starData_len h3 hM hA) ▸ i.isLt⟩)
        ((starData φ h3 hM hA).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [starData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (nPol φ) A (nPol_pos φ) hA)
      (starFormulas φ h3 hA) (compactBudget A)
      (fun i => honest (n := nPol φ) hA ⟨i.val, by
        simpa [starData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [starData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [starData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (starFormulas φ h3 hA ⟨j.val, hj⟩)) ?_).trans
      (starFormulas_eval_residue0 h3 hA ⟨j.val, hj⟩)
    funext v
    exact congrArg (honest (n := nPol φ) hA) (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := nPol φ) hA ⟨i.val,
          (starData_len h3 hM hA) ▸ i.isLt⟩)
        ((starData φ h3 hM hA).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

/-- Polarity-OR packing is not `No`: both polarities at label `0` are cheap
and satisfy every clause OR. -/
theorem paramStarData_not_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (paramStarData L φ h3 hM) (paramStarData_valid h φ h3 hM)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  let x : Fin (paramStarData L φ h3 hM).weights.length → Bool :=
    fun i => honest (n := nPol φ) (paramA_pos L) ⟨i.val, by
      simpa [paramStarData, starData, indexedData] using i.isLt⟩
  have hx := hall x
  have hcost : (paramStarData L φ h3 hM).cost x = compactBudget (paramA L) := by
    simpa [paramStarData, x] using starData_cost_residue0 h3 hM (paramA_pos L)
  have hsat : (paramStarData L φ h3 hM).satisfaction x = 1 := by
    simpa [paramStarData, x] using starData_sat_residue0 h3 hM (paramA_pos L)
  have hb : (paramStarData L φ h3 hM).budget = compactBudget (paramA L) := rfl
  have hle : (paramStarData L φ h3 hM).cost x ≤
      (rofSigma L : Rat) * (paramStarData L φ h3 hM).budget := by
    rw [hcost, hb]
    have hσQ : (1 : Rat) ≤ (rofSigma L : Rat) := Nat.one_le_cast.mpr hσ
    exact le_mul_of_one_le_left (le_of_lt (compactBudget_pos (paramA_pos L))) hσQ
  have h1lt : (1 : Rat) < gammaL L := by simpa [hsat] using hx hle
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- `encodeData` of the polarity-OR packing.  3SAT lives in the tree. -/
def threeSatToStarBits {L : Nat} (h : 256 ≤ mOf L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) : List Bool :=
  encodeData (paramStarData L φ h3 hM) (paramStarData_valid h φ h3 hM)

theorem threeSatToStarBits_yes_of_sat {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    threeSatToStarBits h φ h3 hM ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).yesInstances :=
  cmmsaPromise_yes_of_encode hσ hγ0 hγ1
    (ofData (paramStarData L φ h3 hM) (paramStarData_valid h φ h3 hM))
    (paramStarData_yes_of_sat h φ h3 hM α hsat)

theorem threeSatToStarBits_ne_id {L : Nat} (h : 256 ≤ mOf L) :
    threeSatToStarBits h satUnit satUnit_is3 satUnit_len ≠ [] := by
  intro hz
  have henc := congrArg List.length hz
  simp [threeSatToStarBits, encodeData, encode, ofData, dataTree,
    CMMSACodec.Tree.encode] at henc

/-! ### XOR-star two-label cheap witness -/

def twoLabel {n h : Nat} (_hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i => decide (i.val % alph h < 2)

private theorem two_lt_alph {h : Nat} (hh : 0 < h) : 2 < alph h := by
  have h2 : 2 ≤ 2 * h := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hh)
  have h4 : 4 ≤ alph h := by
    simpa [alph] using Nat.pow_le_pow_right (by decide : 0 < 2) h2
  exact lt_of_lt_of_le (by decide : 2 < 4) h4

private theorem restrictLow_id {h : Nat} (a : Fin (alph h)) :
    restrictLow (le_rfl : 2 * h ≤ 2 * h) a = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

private theorem clauseMask_val_lt_two {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) (j : Fin 2) :
    (clauseMask hh φ h3 i j).val < 2 := by
  simp only [clauseMask]
  split_ifs
  · exact Nat.zero_lt_two
  · simp [rhsMask]

private theorem twoLabel_coord {n h : Nat} (hh : 0 < h)
    (v : Fin n) (a : Fin (alph h)) :
    twoLabel (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val < 2) := by
  simp [twoLabel, coord_mod (alph_pos h) v a]

private theorem eval_clauseXor_twoLabel {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.eval (twoLabel (n := nPol φ) hh)
      (clauseXorFormula hh φ h3 i) = true := by
  refine (eval_compileResXor (le_rfl : 2 * h ≤ 2 * h)
      (twoLabel (n := nPol φ) hh)
      (clausePol φ h3 i 0)
      (fun j : Fin 2 => clausePol φ h3 i j.succ)
      (clauseMask hh φ h3 i)).mpr ⟨⟨0, alph_pos h⟩, ?_, ?_⟩
  · rw [twoLabel_coord hh (clausePol φ h3 i 0) ⟨0, alph_pos h⟩]
    simp
  · intro j
    have hmask := clauseMask_val_lt_two hh φ h3 i j
    have hid : restrictLow (le_rfl : 2 * h ≤ 2 * h) (⟨0, alph_pos h⟩ : Fin (alph h)) =
        ⟨0, alph_pos h⟩ := restrictLow_id _
    rw [hid, xorFin_comm, xorFin_zero, twoLabel_coord hh
      (clausePol φ h3 i j.succ) (clauseMask hh φ h3 i j)]
    exact decide_eq_true hmask

private theorem xorStar_len {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (xorStarData hh φ h3 hM).weights.length = nPol φ * alph h := by
  simp [xorStarData, indexedData]

private theorem two_label_weight {n h : Nat} (hn : 0 < n) (hh : 0 < h) :
    weight (compactWeights n (alph h) hn (alph_pos h))
      (twoLabel (n := n) hh) = (2 : Rat) / (alph h : Rat) := by
  unfold weight compactWeights twoLabel
  have hA := alph_pos h
  have hcard : ((n * alph h : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos hn hA).ne'
  have hre :
      (∑ i : Fin (n * alph h),
          if i.val % alph h < 2 then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        ∑ v : Fin n, ∑ a : Fin (alph h),
          if a.val < 2 then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval := finProd_val (A := alph h) v a
    have hmod : (a.val + alph h * v.val) % alph h = a.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    simp [hval, hmod]
  have hdecide :
      (∑ i : Fin (n * alph h),
          if decide (i.val % alph h < 2) = true then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        ∑ i : Fin (n * alph h),
          if i.val % alph h < 2 then
            (1 : Rat) / ((n * alph h : Nat) : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hdecide, hre]
  have hlt : 2 < alph h := two_lt_alph hh
  have h0 : (0 : Nat) < alph h := hA
  have h1 : (1 : Nat) < alph h := lt_trans Nat.one_lt_two hlt
  have hinner : ∀ v : Fin n,
      (∑ a : Fin (alph h),
          if a.val < 2 then (1 : Rat) / ((n * alph h : Nat) : Rat) else 0) =
        (2 : Rat) / ((n * alph h : Nat) : Rat) := by
    intro v
    have hfilter :
        (Finset.univ.filter fun a : Fin (alph h) => a.val < 2) =
          {⟨0, h0⟩, ⟨1, h1⟩} := by
      ext a
      constructor
      · intro ha
        have hv : a.val < 2 := by simpa using ha
        have h01 : a.val = 0 ∨ a.val = 1 := by omega
        simp [Finset.mem_insert, Finset.mem_singleton]
        rcases h01 with hval | hval
        · left
          apply Fin.ext
          simpa using hval
        · right
          apply Fin.ext
          simpa using hval
      · intro ha
        simp at ha
        rcases ha with rfl | rfl <;> simp
    have hne : (⟨0, h0⟩ : Fin (alph h)) ≠ ⟨1, h1⟩ := by
      intro h01
      exact Nat.zero_ne_one (congrArg Fin.val h01)
    have hcard :
        ({⟨0, h0⟩, ⟨1, h1⟩} : Finset (Fin (alph h))).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    norm_num
  rw [Finset.sum_congr rfl fun v _ => hinner v]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  have hnR : (n : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hAR : (alph h : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  field_simp [hcard, hnR, hAR]

private theorem xorStar_cost_twoLabel {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (xorStarData hh φ h3 hM).cost
      (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
        (xorStar_len hh φ h3 hM) ▸ i.isLt⟩) =
      (2 : Rat) / (alph h : Rat) := by
  have hlen := xorStar_len hh φ h3 hM
  unfold Data.cost Data.coordinateWeights weight twoLabel xorStarData indexedData
  simp only [List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (nPol φ) (alph h) (nPol_pos φ) (alph_pos h))).length ≃
      Fin (nPol φ * alph h) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := two_label_weight (nPol_pos φ) hh
  unfold weight compactWeights twoLabel at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights]

private theorem xorStar_sat_twoLabel {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (xorStarData hh φ h3 hM).satisfaction
      (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
        (xorStar_len hh φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (xorStarData hh φ h3 hM).formulas.length) := by
    simp [xorStarData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (xorStarData hh φ h3 hM).formulas.length,
      Formula.eval
        (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
          (xorStar_len hh φ h3 hM) ▸ i.isLt⟩)
        ((xorStarData hh φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [xorStarData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (nPol φ) (alph h) (nPol_pos φ) (alph_pos h))
      (xorFormulas hh φ h3) (compactBudget (alph h))
      (fun i => twoLabel (n := nPol φ) hh ⟨i.val, by
        simpa [xorStarData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [xorStarData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [xorStarData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (xorFormulas hh φ h3 ⟨j.val, hj⟩)) ?_).trans
      (eval_clauseXor_twoLabel hh φ h3 ⟨j.val, hj⟩)
    funext v
    exact congrArg (twoLabel (n := nPol φ) hh) (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
          (xorStar_len hh φ h3 hM) ▸ i.isLt⟩)
        ((xorStarData hh φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

private theorem two_div_le_sigma_budget {L : Nat} (h16 : 16 ≤ ROf L) :
    (2 : Rat) / (ROf L : Rat) ≤
      (rofSigma L : Rat) * compactBudget (ROf L) := by
  have hRpos : (0 : Rat) < (ROf L : Rat) := Nat.cast_pos.mpr (ROf_pos L)
  have hσ : (2 : Rat) ≤ (rofSigma L : Rat) := by
    have h8 : 8 ≤ ROf L := le_trans (by decide : 8 ≤ 16) h16
    have hEq := eight_mul_rofSigma_eq_ROf h8
    have : 16 ≤ 8 * rofSigma L := by simpa [hEq] using h16
    have h2 : 2 ≤ rofSigma L := by omega
    exact Nat.cast_le.mpr h2
  unfold compactBudget
  have : (2 : Rat) / (ROf L : Rat) ≤ (rofSigma L : Rat) / (ROf L : Rat) :=
    div_le_div_of_nonneg_right hσ hRpos.le
  simpa [div_eq_mul_inv] using this

/-- XOR-star packing is not `No`: labels `{0,1}` at every polarity are cheap
once `16 ≤ ROf L` and satisfy every `compileResXor` clause. -/
theorem xorStarData_not_no {L : Nat} (h : 256 ≤ mOf L)
    (hh : 0 < hOf L (mOf L)) (h16 : 16 ≤ ROf L)
    (_hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (xorStarData (h := hOf L (mOf L)) hh φ h3 hM)
        (xorStarData_valid_of_mOf h hh φ h3 hM)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  have hx := hall
    (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
      (xorStar_len hh φ h3 hM) ▸ i.isLt⟩)
  have hcost := xorStar_cost_twoLabel hh φ h3 hM
  have hsat := xorStar_sat_twoLabel hh φ h3 hM
  have hb : (xorStarData (h := hOf L (mOf L)) hh φ h3 hM).budget =
      compactBudget (alph (hOf L (mOf L))) := rfl
  have hle : (xorStarData (h := hOf L (mOf L)) hh φ h3 hM).cost
      (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
        (xorStar_len hh φ h3 hM) ▸ i.isLt⟩) ≤
      (rofSigma L : Rat) *
        (xorStarData (h := hOf L (mOf L)) hh φ h3 hM).budget := by
    rw [hcost, hb, alph_eq_ROf]
    exact two_div_le_sigma_budget h16
  have h1lt : (1 : Rat) < gammaL L := by simpa [hsat] using hx hle
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- Polarity-OR packing is not manuscript `No`: label `0` costs the budget,
so it lies in the `σ`-ball once `1 ≤ manuscriptSigma`, and every clause OR
stays at satisfaction `1`. -/
theorem paramStarData_not_no_manuscript {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ1 : manuscriptGamma L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    ¬ No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (paramStarData L φ h3 hM) (paramStarData_valid h φ h3 hM)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  let x : Fin (paramStarData L φ h3 hM).weights.length → Bool :=
    fun i => honest (n := nPol φ) (paramA_pos L) ⟨i.val, by
      simpa [paramStarData, starData, indexedData] using i.isLt⟩
  have hx := hall x
  have hcost : (paramStarData L φ h3 hM).cost x = compactBudget (paramA L) := by
    simpa [paramStarData, x] using starData_cost_residue0 h3 hM (paramA_pos L)
  have hsat : (paramStarData L φ h3 hM).satisfaction x = 1 := by
    simpa [paramStarData, x] using starData_sat_residue0 h3 hM (paramA_pos L)
  have hb : (paramStarData L φ h3 hM).budget = compactBudget (paramA L) := rfl
  have hle : (paramStarData L φ h3 hM).cost x ≤
      (manuscriptSigma L : Rat) * (paramStarData L φ h3 hM).budget := by
    rw [hcost, hb]
    have hσQ : (1 : Rat) ≤ (manuscriptSigma L : Rat) := Nat.one_le_cast.mpr hσ
    exact le_mul_of_one_le_left (le_of_lt (compactBudget_pos (paramA_pos L))) hσQ
  have h1lt : (1 : Rat) < manuscriptGamma L := by simpa [hsat] using hx hle
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- Two labels cost `2/R`.  That is at most `manuscriptSigma / R` once
`2 ≤ manuscriptSigma`, with no use of `8 * rofSigma = ROf`. -/
private theorem two_div_le_manuscript_budget {L : Nat}
    (h2 : 2 ≤ manuscriptSigma L) :
    (2 : Rat) / (ROf L : Rat) ≤
      (manuscriptSigma L : Rat) * compactBudget (ROf L) := by
  have hRpos : (0 : Rat) < (ROf L : Rat) := Nat.cast_pos.mpr (ROf_pos L)
  have hσ : (2 : Rat) ≤ (manuscriptSigma L : Rat) := Nat.cast_le.mpr h2
  unfold compactBudget
  have : (2 : Rat) / (ROf L : Rat) ≤ (manuscriptSigma L : Rat) / (ROf L : Rat) :=
    div_le_div_of_nonneg_right hσ hRpos.le
  simpa [div_eq_mul_inv] using this

/-- XOR-star packing is not manuscript `No` for any 3CNF with a clause.
Labels `{0,1}` satisfy every `compileResXor` and cost `2/ROf`. -/
theorem xorStarData_not_no_manuscript {L : Nat} (h : 256 ≤ mOf L)
    (hh : 0 < hOf L (mOf L)) (h2 : 2 ≤ manuscriptSigma L)
    (hγ1 : manuscriptGamma L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    ¬ No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (xorStarData (h := hOf L (mOf L)) hh φ h3 hM)
        (xorStarData_valid_of_mOf h hh φ h3 hM)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  have hx := hall
    (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
      (xorStar_len hh φ h3 hM) ▸ i.isLt⟩)
  have hcost := xorStar_cost_twoLabel hh φ h3 hM
  have hsat := xorStar_sat_twoLabel hh φ h3 hM
  have hb : (xorStarData (h := hOf L (mOf L)) hh φ h3 hM).budget =
      compactBudget (alph (hOf L (mOf L))) := rfl
  have hle : (xorStarData (h := hOf L (mOf L)) hh φ h3 hM).cost
      (fun i => twoLabel (n := nPol φ) hh ⟨i.val,
        (xorStar_len hh φ h3 hM) ▸ i.isLt⟩) ≤
      (manuscriptSigma L : Rat) *
        (xorStarData (h := hOf L (mOf L)) hh φ h3 hM).budget := by
    rw [hcost, hb, alph_eq_ROf]
    exact two_div_le_manuscript_budget h2
  have h1lt : (1 : Rat) < manuscriptGamma L := by simpa [hsat] using hx hle
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- For every large `L`, manuscript parameters form a promise and both
shipped many-valued packings fail manuscript `No` on every nonempty 3CNF.
The XOR witness still takes `0 < hOf`.  This is not an FP reduction. -/
theorem manyValuedPackings_fail_manuscript_eventually :
    ∃ L0, ∀ L, L0 ≤ L →
      256 ≤ mOf L ∧ 2 ≤ manuscriptSigma L ∧
        0 < manuscriptGamma L ∧ manuscriptGamma L < 1 ∧
        ∀ (h : 256 ≤ mOf L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length),
          ¬ No (manuscriptSigma L) (manuscriptGamma L)
            (ofData (paramStarData L φ h3 hM) (paramStarData_valid h φ h3 hM)) ∧
          ∀ (hh : 0 < hOf L (mOf L)),
            ¬ No (manuscriptSigma L) (manuscriptGamma L)
              (ofData (xorStarData (h := hOf L (mOf L)) hh φ h3 hM)
                (xorStarData_valid_of_mOf h hh φ h3 hM)) := by
  obtain ⟨Lm, hm⟩ := mOf_unbounded 256
  obtain ⟨Ls, hS⟩ :=
    ActualCertifiedManuscriptParameters.certifiedSigma_ge_two_eventual
  obtain ⟨Lg, hG⟩ :=
    ActualCertifiedManuscriptParameters.certifiedGamma_pos_lt_one_eventual
  refine ⟨max Lm (max Ls Lg), ?_⟩
  intro L hL
  have hLm : Lm ≤ L := (le_max_left _ _).trans hL
  have hLs : Ls ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLg : Lg ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have h256 : 256 ≤ mOf L := hm L hLm
  have h2 : 2 ≤ manuscriptSigma L := by
    simpa [manuscriptSigma] using hS L hLs
  have hγp : 0 < manuscriptGamma L ∧ manuscriptGamma L < 1 := by
    simpa [manuscriptGamma] using hG L hLg
  refine ⟨h256, h2, hγp.1, hγp.2, ?_⟩
  intro h φ h3 hM
  refine ⟨paramStarData_not_no_manuscript h (by omega) hγp.2 φ h3 hM, ?_⟩
  intro hh
  exact xorStarData_not_no_manuscript h hh h2 hγp.2 φ h3 hM

end
end PvNP.RealizableHardness.ActualThreeSatPcpPack
