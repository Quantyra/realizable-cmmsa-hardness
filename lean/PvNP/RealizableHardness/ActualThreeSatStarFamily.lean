import PvNP.RealizableHardness.ActualCompactStarCompile
import PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
import Complexitylib.SAT.Semantics
import Complexitylib.SAT.ThreeSAT

/-!
3SAT-dependent large-alphabet CMMSA family at manuscript `ROf L`.

Each 3-clause becomes a 3-leaf polarity OR on label `0` of alphabet
`ROf L`.  Formulas depend on the source literals (not identity, not a
tautology-row).  `Valid L` holds once `256 ≤ mOf L`.

This does **not** prove `No σ_L γ_L`: both polarities at label `0` still
cost `1/ROf L ≪ σ_L · budget`.  `hn_zeta_beats_sigma` is the CSP-value
threshold HN list-decoding needs; polarity-ORs do not meet it.
`hSrcCmmsa` is not inhabited here.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarFamily

open Complexity
open Complexity.SAT
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatCmmsaReduce
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem three_mul_ROf_le {L : Nat} (h : 256 ≤ mOf L) :
    3 * ROf L ≤ L := by
  have hfit := compactLeaves_le h
  have h3 : 3 ≤ mOf L + 1 :=
    Nat.succ_le_succ (le_trans (by decide : 2 ≤ 256) h)
  exact (Nat.mul_le_mul_right (ROf L) h3).trans hfit

def paddedLit {φ : CNF} {A : Nat} (hA : 0 < A) (ℓ : Lit)
    (hℓ : ℓ.var < nVars φ) : Formula (Fin (nPol φ * A)) :=
  varAt hA (litIndex φ ℓ hℓ) ⟨0, hA⟩

def paddedClause {φ : CNF} {A : Nat} (hA : 0 < A) (c : Clause)
    (hc : c.length = 3) (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula (Fin (nPol φ * A)) :=
  or3 (paddedLit hA (clauseNth c hc 0) (hv _ (List.get_mem c _)))
    (paddedLit hA (clauseNth c hc 1) (hv _ (List.get_mem c _)))
    (paddedLit hA (clauseNth c hc 2) (hv _ (List.get_mem c _)))

theorem paddedClause_leaves {φ : CNF} {A : Nat} (hA : 0 < A) (c : Clause)
    (hc : c.length = 3) (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula.leaves (paddedClause hA c hc hv) = 3 := by
  simp [paddedClause, or3_leaves, paddedLit, varAt, Formula.leaves]

def starFormulas (φ : CNF) (h3 : φ.Is3CNF) {A : Nat} (hA : 0 < A) :
    Fin φ.length → Formula (Fin (nPol φ * A)) := fun i =>
  paddedClause hA φ[i] (h3 φ[i] (List.get_mem _ _))
    (fun ℓ hℓ => lit_var_lt_nVars φ φ[i] ℓ (List.get_mem _ _) hℓ)

def starData (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    {A : Nat} (hA : 0 < A) : Data :=
  indexedData (compactWeights (nPol φ) A (nPol_pos φ) hA)
    (starFormulas φ h3 hA) (compactBudget A)

theorem starData_valid {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) {A : Nat} (hA : 0 < A) (hleaves : 3 ≤ L) :
    Valid L (starData φ h3 hM hA) := by
  refine indexedData_valid (compactWeights (nPol φ) A (nPol_pos φ) hA)
    (starFormulas φ h3 hA) (compactBudget A)
    (compactWeights_pos (nPol_pos φ) hA)
    (compactWeights_sum (nPol_pos φ) hA) hM ?_
    (compactBudget_pos hA) (compactBudget_le_one hA)
  intro i
  simpa [starFormulas, paddedClause_leaves] using hleaves

def paramStarData (L : Nat) (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) : Data :=
  starData φ h3 hM (paramA_pos L)

theorem three_le_L_of_mOf {L : Nat} (h : 256 ≤ mOf L) : 3 ≤ L := by
  have hspec := mOf_spec L
  rcases hspec with h0 | hpair
  · exact (Nat.not_succ_le_zero 255 (h0 ▸ h)).elim
  · have hlog : log2nat L ≤ L := by
      unfold log2nat
      split_ifs
      · simp
      · exact Nat.log_le_self 2 _
    have hsq : Nat.sqrt (log2nat L) ≤ log2nat L := Nat.sqrt_le_self _
    exact le_trans (by decide : 3 ≤ 256)
      (h.trans (hpair.2.trans (hsq.trans hlog)))

theorem paramStarData_valid {L : Nat} (h : 256 ≤ mOf L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (paramStarData L φ h3 hM) :=
  starData_valid φ h3 hM (paramA_pos L) (three_le_L_of_mOf h)

private theorem coord_div_lt {φ : CNF} {A : Nat} (hA : 0 < A)
    (i : Fin (nPol φ * A)) : i.val / A < nPol φ :=
  (Nat.div_lt_iff_lt_mul hA).mpr i.isLt

def satHonest {φ : CNF} {A : Nat} (hA : 0 < A) (α : Assignment) :
    Fin (nPol φ * A) → Bool :=
  fun i => decide (i.val % A = 0 ∧
    polAssign φ α ⟨i.val / A, coord_div_lt hA i⟩)

private theorem coord_mod {φ : CNF} {A : Nat} (hA : 0 < A)
    (v : Fin (nPol φ)) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

private theorem coord_div {φ : CNF} {A : Nat} (hA : 0 < A)
    (v : Fin (nPol φ)) (a : Fin A) :
    (v.val * A + a.val) / A = v.val := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm, Nat.mul_add_div hA,
    Nat.div_eq_of_lt a.isLt, Nat.add_zero]

private theorem satHonest_coord {φ : CNF} {A : Nat} (hA : 0 < A)
    (α : Assignment) (v : Fin (nPol φ)) (a : Fin A) :
    satHonest hA α ⟨v.val * A + a.val, coord_lt v a hA⟩ =
      decide (a.val = 0 ∧ polAssign φ α v) := by
  unfold satHonest
  have hcast :
      (⟨(v.val * A + a.val) / A, coord_div_lt hA ⟨_, coord_lt v a hA⟩⟩ :
        Fin (nPol φ)) = v := Fin.ext (coord_div hA v a)
  simp [coord_mod hA v a, hcast]

private theorem polAssign_litIndex {φ : CNF} (α : Assignment) (ℓ : Lit)
    (hℓ : ℓ.var < nVars φ) :
    polAssign φ α (litIndex φ ℓ hℓ) =
      if ℓ.sign then α.get ℓ.var else !(α.get ℓ.var) := by
  unfold polAssign litIndex
  by_cases hs : ℓ.sign
  · simp only [hs, ite_true]
    have hlt : ℓ.var < nVars φ := hℓ
    simp [hlt]
  · simp only [hs, ite_false]
    have hn : ¬ nVars φ + ℓ.var < nVars φ := by omega
    simp [hn]

private theorem eval_paddedLit {φ : CNF} {A : Nat} (hA : 0 < A)
    (α : Assignment) (ℓ : Lit) (hℓ : ℓ.var < nVars φ) :
    Formula.eval (satHonest (φ := φ) hA α) (paddedLit hA ℓ hℓ) =
      Lit.eval α ℓ := by
  simp only [paddedLit, varAt, Formula.eval]
  rw [satHonest_coord (φ := φ) hA α (litIndex φ ℓ hℓ) ⟨0, hA⟩,
    polAssign_litIndex]
  unfold Lit.eval
  cases ℓ.sign <;> cases hα : α.get ℓ.var <;> simp [hα]

private theorem clause_eq_three (c : Clause) (hc : c.length = 3) :
    c = [clauseNth c hc 0, clauseNth c hc 1, clauseNth c hc 2] := by
  match c with
  | [] => cases hc
  | [_] => cases hc
  | [_, _] => cases hc
  | a :: b :: d :: [] => simp [clauseNth]
  | _ :: _ :: _ :: _ :: _ => cases hc

private theorem clause_eval_three (α : Assignment) (c : Clause)
    (hc : c.length = 3) :
    Clause.eval α c =
      (Lit.eval α (clauseNth c hc 0) || Lit.eval α (clauseNth c hc 1) ||
        Lit.eval α (clauseNth c hc 2)) := by
  match c with
  | [] => cases hc
  | [_] => cases hc
  | [_, _] => cases hc
  | a :: b :: d :: [] =>
      simp [clauseNth, Clause.eval]
      exact (Bool.or_assoc _ _ _).symm
  | _ :: _ :: _ :: _ :: _ => cases hc

private theorem eval_paddedClause {φ : CNF} {A : Nat} (hA : 0 < A)
    (α : Assignment) (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula.eval (satHonest (φ := φ) hA α) (paddedClause hA c hc hv) =
      Clause.eval α c := by
  have h0 := eval_paddedLit (φ := φ) hA α (clauseNth c hc 0)
    (hv _ (List.get_mem c _))
  have h1 := eval_paddedLit (φ := φ) hA α (clauseNth c hc 1)
    (hv _ (List.get_mem c _))
  have h2 := eval_paddedLit (φ := φ) hA α (clauseNth c hc 2)
    (hv _ (List.get_mem c _))
  simp only [paddedClause, or3, Formula.eval]
  rw [h0, h1, h2, clause_eval_three α c hc]

private theorem residue0_mass {φ : CNF} {A : Nat} (hA : 0 < A) :
    (∑ i : Fin (nPol φ * A),
        if i.val % A = 0 then (1 : Rat) / ((nPol φ * A : Nat) : Rat) else 0) =
      compactBudget A := by
  have hnA : ((nPol φ * A : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (nPol_pos φ) hA).ne'
  have hprod :
      (∑ i : Fin (nPol φ * A),
          if i.val % A = 0 then (1 : Rat) / ((nPol φ * A : Nat) : Rat) else 0) =
        ∑ v : Fin (nPol φ), ∑ a : Fin A,
          if a.val = 0 then (1 : Rat) / ((nPol φ * A : Nat) : Rat) else 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    have hval : (finProdFinEquiv (v, a)).val = v.val * A + a.val := by
      change a.val + A * v.val = v.val * A + a.val
      ring
    simp [hval, coord_mod hA v a]
  rw [hprod]
  have hA0 : (Finset.univ.filter fun a : Fin A => a.val = 0) = {⟨0, hA⟩} := by
    ext a
    constructor
    · intro ha
      exact Finset.mem_singleton.2 (Fin.ext (by simpa using ha))
    · intro ha
      have : a = ⟨0, hA⟩ := Finset.mem_singleton.1 ha
      simpa [this]
  simp [Finset.sum_ite, hA0, Fintype.card_fin, compactBudget]
  have hn : (nPol φ : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (nPol_pos φ).ne'
  field_simp [hnA, hn]

private theorem starData_len {φ : CNF} (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    {A : Nat} (hA : 0 < A) :
    (starData φ h3 hM hA).weights.length = nPol φ * A := by
  simp [starData, indexedData]

private theorem satHonest_val_eq {φ : CNF} {A : Nat} (hA : 0 < A)
    (α : Assignment) (i j : Fin (nPol φ * A)) (h : i.val = j.val) :
    satHonest (φ := φ) hA α i = satHonest (φ := φ) hA α j :=
  congrArg (satHonest (φ := φ) hA α) (Fin.ext h)

private theorem starData_cost_eq {φ : CNF} (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    {A : Nat} (hA : 0 < A) (α : Assignment) :
    (starData φ h3 hM hA).cost
      (fun i => satHonest (φ := φ) hA α ⟨i.val,
        (starData_len h3 hM hA) ▸ i.isLt⟩) =
      ∑ y : Fin (nPol φ * A),
        if satHonest (φ := φ) hA α y = true then
          compactWeights (nPol φ) A (nPol_pos φ) hA y else 0 := by
  unfold Data.cost Data.coordinateWeights weight
  simp only [starData, indexedData, List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (nPol φ) A (nPol_pos φ) hA)).length ≃ Fin (nPol φ * A) :=
    (Fin.castOrderIso (by simp)).toEquiv
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  have hsat :
      satHonest (φ := φ) hA α ⟨i.val, by
        have := i.isLt
        simpa [starData, indexedData] using this⟩ =
      satHonest (φ := φ) hA α (e i) :=
    satHonest_val_eq (φ := φ) hA α _ (e i) hval.symm
  have hcast :
      Fin.cast (by simp : (List.ofFn
        (compactWeights (nPol φ) A (nPol_pos φ) hA)).length = nPol φ * A) i =
      e i := Fin.ext (by simp [e, Fin.castOrderIso])
  refine if_congr (iff_of_eq (congrArg (fun b : Bool => b = true) hsat))
    (congrArg (compactWeights (nPol φ) A (nPol_pos φ) hA) hcast) rfl

private theorem satHonest_le_residue0 {φ : CNF} {A : Nat} (hA : 0 < A)
    (α : Assignment) (y : Fin (nPol φ * A)) :
    (if satHonest (φ := φ) hA α y = true then
      compactWeights (nPol φ) A (nPol_pos φ) hA y else 0) ≤
    (if y.val % A = 0 then
      compactWeights (nPol φ) A (nPol_pos φ) hA y else 0) := by
  unfold satHonest compactWeights
  by_cases h0 : y.val % A = 0
  · by_cases hp : polAssign φ α ⟨y.val / A, coord_div_lt hA y⟩ = true
    · simp [h0, hp]
    · simp [h0, hp]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
  · simp [h0]

private theorem starData_cost_le {φ : CNF} (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    {A : Nat} (hA : 0 < A) (α : Assignment) :
    (starData φ h3 hM hA).cost
      (fun i => satHonest (φ := φ) hA α ⟨i.val,
        (starData_len h3 hM hA) ▸ i.isLt⟩) ≤
      compactBudget A :=
  (starData_cost_eq h3 hM hA α).trans_le
    ((Finset.sum_le_sum fun y _ => satHonest_le_residue0 hA α y).trans
      (le_of_eq (by simpa [compactWeights] using residue0_mass (φ := φ) hA)))

private theorem starFormulas_eval_sat {φ : CNF} (h3 : φ.Is3CNF)
    {A : Nat} (hA : 0 < A) (α : Assignment) (hsat : CNF.eval α φ = true)
    (j : Fin φ.length) :
    Formula.eval (satHonest (φ := φ) hA α) (starFormulas φ h3 hA j) = true := by
  have hcmem : φ[j.val] ∈ φ := List.get_mem φ j
  have hallc : ∀ c ∈ φ, Clause.eval α c = true := by
    simpa [CNF.eval, List.all_eq_true] using hsat
  simpa [starFormulas] using
    (eval_paddedClause (φ := φ) hA α φ[j.val] (h3 _ hcmem)
      (fun ℓ hℓ => lit_var_lt_nVars φ φ[j.val] ℓ hcmem hℓ)).trans
      (hallc _ hcmem)

theorem starData_yes_of_sat {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) {A : Nat} (hA : 0 < A) (hleaves : 3 ≤ L)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    Yes 0 (ofData (starData φ h3 hM hA)
      (starData_valid φ h3 hM hA hleaves)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => satHonest (φ := φ) hA α ⟨i.val,
      (starData_len h3 hM hA) ▸ i.isLt⟩, ?_, ?_⟩
  · exact starData_cost_le h3 hM hA α
  · haveI : Nonempty (Fin (starData φ h3 hM hA).formulas.length) := by
      simp [starData, indexedData]
      exact ⟨⟨0, hM⟩⟩
    unfold Data.satisfaction
    have hall : ∀ j : Fin (starData φ h3 hM hA).formulas.length,
        Formula.eval
          (fun i => satHonest (φ := φ) hA α ⟨i.val,
            (starData_len h3 hM hA) ▸ i.isLt⟩)
          ((starData φ h3 hM hA).indexedFormulas j) = true := by
      intro j
      have hj : j.val < φ.length := by
        simpa [starData, indexedData] using j.isLt
      have heval := indexedData_eval
        (compactWeights (nPol φ) A (nPol_pos φ) hA)
        (starFormulas φ h3 hA) (compactBudget A)
        (fun i => satHonest (φ := φ) hA α ⟨i.val, by
          simpa [starData, indexedData] using i.isLt⟩)
        ⟨j.val, hj⟩
      have hjFin : j = ⟨j.val, by simpa [starData, indexedData] using j.isLt⟩ :=
        Fin.ext rfl
      rw [hjFin, Data.indexedFormulas]
      simp only [starData, indexedData] at heval ⊢
      rw [heval]
      refine (congrArg (fun x => Formula.eval x
          (starFormulas φ h3 hA ⟨j.val, hj⟩)) ?_).trans
        (starFormulas_eval_sat h3 hA α hsat ⟨j.val, hj⟩)
      funext v
      exact satHonest_val_eq (φ := φ) hA α _ v (by simp)
    rw [show (fun j => Formula.eval
          (fun i => satHonest (φ := φ) hA α ⟨i.val,
            (starData_len h3 hM hA) ▸ i.isLt⟩)
          ((starData φ h3 hM hA).indexedFormulas j)) = fun _ => true from
      funext hall]
    have hsat1 := average_true
      (I := Fin (starData φ h3 hM hA).formulas.length)
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat1.symm)

theorem paramStarData_yes_of_sat {L : Nat} (h : 256 ≤ mOf L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    Yes 0 (ofData (paramStarData L φ h3 hM) (paramStarData_valid h φ h3 hM)) := by
  simpa [paramStarData] using
    starData_yes_of_sat φ h3 hM (paramA_pos L) (three_le_L_of_mOf h) α hsat

/-- If the star CSP value is at most `5 / (8 · (8 σ_L)^{m+1})`, then
`(8 σ_L)^{m+1} * zeta ≤ 5/8`. Polarity-OR families do not achieve this
zeta on unsat 3SAT. -/
theorem hn_zeta_beats_sigma (L : Nat) (zeta : Rat)
    (hz : zeta ≤ (5 : Rat) /
      ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1)))
    (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * zeta ≤ (5 : Rat) / 8 := by
  have hden : (0 : Rat) <
      (8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1) :=
    mul_pos (by norm_num)
      (pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (by decide : 0 < 8) hσ)) _)
  have hmul : zeta * ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1)) ≤ 5 :=
    (le_div_iff₀ hden).mp hz
  have hpow : ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) =
      ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1) := by
    simp [Nat.cast_mul]
  rw [hpow]
  have hrew : ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1) * zeta =
      (zeta * ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1))) / 8 := by
    field_simp [hden.ne']
  rw [hrew]
  exact div_le_div_of_nonneg_right hmul (by norm_num)

end PvNP.RealizableHardness.ActualThreeSatStarFamily
