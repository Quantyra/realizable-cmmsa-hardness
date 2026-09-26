import PvNP.RealizableHardness.ActualThreeSatToCmmsa
import Complexitylib.SAT.ThreeSAT
import Complexitylib.SAT.Semantics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Semantic 3SAT → CMMSA compiler: each 3-clause becomes a 3-leaf polarity OR.

Sat instances map to `Yes 0` (a consistent polarity assignment has cost `1/2`
and satisfaction `1`).  This is not an identity map and not a tautology-row
wire.  It does **not** prove `No σ γ` for unsatisfiable 3SAT at manuscript
`σ_L ≥ 2`.  Lowering the budget cannot repair that: any budget at least `1/2`
still leaves all-true inside the `σ`-ball.  `hSrcCmmsa` is not inhabited here.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCmmsaReduce

open Complexity
open Complexity.SAT
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualTheorem1
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatToCmmsa
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

def nVars (φ : CNF) : Nat := φ.maxVar + 1

def nPol (φ : CNF) : Nat := 2 * nVars φ

theorem nVars_pos (φ : CNF) : 0 < nVars φ := Nat.succ_pos _

theorem nPol_pos (φ : CNF) : 0 < nPol φ :=
  Nat.mul_pos Nat.two_pos (nVars_pos φ)

def litIndex (φ : CNF) (ℓ : Lit) (h : ℓ.var < nVars φ) : Fin (nPol φ) :=
  if ℓ.sign then
    ⟨ℓ.var, by
      simp [nPol]
      exact Nat.lt_of_lt_of_le h (Nat.le_mul_of_pos_left (nVars φ) Nat.two_pos)⟩
  else
    ⟨nVars φ + ℓ.var, by
      simp [nPol]
      have := nVars_pos φ
      omega⟩

def or3 {V : Type*} (a b c : Formula V) : Formula V :=
  Formula.or (Formula.or a b) c

theorem or3_leaves {V : Type*} (a b c : Formula V) :
    Formula.leaves (or3 a b c) =
      Formula.leaves a + Formula.leaves b + Formula.leaves c := by
  simp [or3, Formula.leaves, Nat.add_assoc]

def clauseNth (c : Clause) (hc : c.length = 3) (k : Fin 3) : Lit :=
  c.get ⟨k.val, by omega⟩

def clauseFormula (φ : CNF) (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) : Formula (Fin (nPol φ)) :=
  or3
    (.var (litIndex φ (clauseNth c hc 0) (hv _ (List.get_mem c _))))
    (.var (litIndex φ (clauseNth c hc 1) (hv _ (List.get_mem c _))))
    (.var (litIndex φ (clauseNth c hc 2) (hv _ (List.get_mem c _))))

theorem clauseFormula_leaves (φ : CNF) (c : Clause) (hc : c.length = 3)
    (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula.leaves (clauseFormula φ c hc hv) = 3 := by
  simp [clauseFormula, or3_leaves, Formula.leaves]

private theorem lit_var_le_clauseMax (ℓ : Lit) (c : Clause) (h : ℓ ∈ c) :
    ℓ.var ≤ c.maxVar := by
  induction c with
  | nil => cases h
  | cons ℓ' rest ih =>
      simp only [Clause.maxVar]
      cases h with
      | head => exact Nat.le_max_left _ _
      | tail _ hmem => exact le_trans (ih hmem) (Nat.le_max_right _ _)

private theorem clauseMax_le_cnfMax (c : Clause) (φ : CNF) (h : c ∈ φ) :
    c.maxVar ≤ φ.maxVar := by
  induction φ with
  | nil => cases h
  | cons c' cs ih =>
      simp only [CNF.maxVar]
      cases h with
      | head => exact Nat.le_max_left _ _
      | tail _ hmem => exact le_trans (ih hmem) (Nat.le_max_right _ _)

theorem lit_var_lt_nVars (φ : CNF) (c : Clause) (ℓ : Lit)
    (hc : c ∈ φ) (hℓ : ℓ ∈ c) : ℓ.var < nVars φ :=
  Nat.lt_succ_of_le (le_trans (lit_var_le_clauseMax ℓ c hℓ)
    (clauseMax_le_cnfMax c φ hc))

def compileFormulas (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (nPol φ)) := fun i =>
  clauseFormula φ φ[i] (h3 φ[i] (List.get_mem _ _))
    (fun ℓ hℓ => lit_var_lt_nVars φ φ[i] ℓ (List.get_mem _ _) hℓ)

def compileWeights (φ : CNF) : Fin (nPol φ) → Rat :=
  fun _ => (1 : Rat) / (nPol φ : Rat)

theorem compileWeights_pos (φ : CNF) (v : Fin (nPol φ)) :
    0 < compileWeights φ v :=
  div_pos (by norm_num) (Nat.cast_pos.mpr (nPol_pos φ))

theorem compileWeights_sum (φ : CNF) :
    (∑ v : Fin (nPol φ), compileWeights φ v) = 1 := by
  simp [compileWeights]
  have h : (nPol φ : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (nPol_pos φ).ne'
  field_simp [h, Fintype.card_fin]

def compileData (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) : Data :=
  indexedData (compileWeights φ) (compileFormulas φ h3) 1

theorem compileData_valid {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (hL : 3 ≤ L) :
    Valid L (compileData φ h3 hM) := by
  refine indexedData_valid (compileWeights φ) (compileFormulas φ h3) 1
    (compileWeights_pos φ) (compileWeights_sum φ) hM ?_ (by norm_num) (by norm_num)
  intro i
  simp [compileFormulas, clauseFormula_leaves]
  exact hL

theorem weight_le_sum {V : Type*} [Fintype V] (w : V → Rat) (x : V → Bool)
    (hw : ∀ v, 0 ≤ w v) :
    weight w x ≤ ∑ v, w v := by
  unfold weight
  apply Finset.sum_le_sum
  intro v _
  split <;> simp [hw v]

def polAssign (φ : CNF) (α : Assignment) : Fin (nPol φ) → Bool := fun i =>
  if h : i.val < nVars φ then α.get i.val
  else !(α.get (i.val - nVars φ))

private theorem eval_all_true {V : Type*} (f : Formula V) :
    f.eval (fun _ => true) = true := by
  induction f <;> simp [Formula.eval, *]

theorem nPol_eq (φ : CNF) : nPol φ = nVars φ + nVars φ := by
  simp [nPol, two_mul]

private theorem polAssign_inl (φ : CNF) (α : Assignment) (v : Fin (nVars φ)) :
    polAssign φ α ⟨v.val, Nat.lt_of_lt_of_le v.isLt
      (Nat.le_mul_of_pos_left (nVars φ) Nat.two_pos)⟩ = α.get v.val := by
  unfold polAssign
  simp [v.isLt]

private theorem polAssign_inr (φ : CNF) (α : Assignment) (v : Fin (nVars φ)) :
    polAssign φ α ⟨nVars φ + v.val, by
      simp [nPol]; omega⟩ = !(α.get v.val) := by
  unfold polAssign
  have hn : ¬ nVars φ + v.val < nVars φ := by omega
  simp [hn]

private theorem polAssign_pair_one (φ : CNF) (α : Assignment) (v : Fin (nVars φ)) :
    (if polAssign φ α ⟨v.val, Nat.lt_of_lt_of_le v.isLt
          (Nat.le_mul_of_pos_left (nVars φ) Nat.two_pos)⟩ then (1 : Rat) else 0) +
      (if polAssign φ α ⟨nVars φ + v.val, by simp [nPol]; omega⟩ then 1 else 0) =
        1 := by
  rw [polAssign_inl, polAssign_inr]
  cases α.get v.val <;> simp

private theorem polAssign_count (φ : CNF) (α : Assignment) :
    (∑ i : Fin (nPol φ), if polAssign φ α i then (1 : Rat) else 0) =
      nVars φ := by
  let e : Fin (nVars φ) ⊕ Fin (nVars φ) ≃ Fin (nPol φ) :=
    finSumFinEquiv.trans (Fin.castOrderIso (nPol_eq φ).symm).toEquiv
  have hinl : ∀ v : Fin (nVars φ), e (Sum.inl v) =
      ⟨v.val, Nat.lt_of_lt_of_le v.isLt
        (Nat.le_mul_of_pos_left (nVars φ) Nat.two_pos)⟩ := by
    intro v
    apply Fin.ext
    simp [e, Fin.castOrderIso]
  have hinr : ∀ v : Fin (nVars φ), e (Sum.inr v) =
      ⟨nVars φ + v.val, by simp [nPol]; omega⟩ := by
    intro v
    apply Fin.ext
    simp [e, Fin.castOrderIso]
    exact Nat.add_comm _ _
  have hpair : ∀ v : Fin (nVars φ),
      (if polAssign φ α (e (Sum.inl v)) then (1 : Rat) else 0) +
        (if polAssign φ α (e (Sum.inr v)) then 1 else 0) = 1 := by
    intro v
    rw [hinl v, hinr v, polAssign_pair_one]
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  change (∑ v : Fin (nVars φ),
        if polAssign φ α (e (Sum.inl v)) then (1 : Rat) else 0) +
      (∑ v : Fin (nVars φ),
        if polAssign φ α (e (Sum.inr v)) then 1 else 0) = _
  rw [← Finset.sum_add_distrib]
  simp only [hpair, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  simp

theorem compileData_len {φ : CNF} (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (compileData φ h3 hM).weights.length = nPol φ := by
  simp [compileData, indexedData]

private theorem compileData_cost_polAssign (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (α : Assignment) :
    (compileData φ h3 hM).cost
      (fun i => polAssign φ α ⟨i.val, (compileData_len h3 hM) ▸ i.isLt⟩) =
      (1 : Rat) / 2 := by
  unfold Data.cost Data.coordinateWeights weight compileData indexedData
  simp only [List.get_ofFn, compileWeights]
  have hmul :
      (∑ i : Fin (List.ofFn (compileWeights φ)).length,
          if polAssign φ α ⟨i.val, by simpa using i.isLt⟩ then
            (1 : Rat) / (nPol φ : Rat) else 0) =
        ((1 : Rat) / (nPol φ : Rat)) *
          ∑ i : Fin (List.ofFn (compileWeights φ)).length,
            if polAssign φ α ⟨i.val, by simpa using i.isLt⟩ then (1 : Rat) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp
  rw [hmul]
  let e : Fin (List.ofFn (compileWeights φ)).length ≃ Fin (nPol φ) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hcount' :
      (∑ i : Fin (List.ofFn (compileWeights φ)).length,
          if polAssign φ α ⟨i.val, by simpa using i.isLt⟩ then (1 : Rat) else 0) =
        (nVars φ : Rat) := by
    have heq : ∀ i : Fin (List.ofFn (compileWeights φ)).length,
        ⟨i.val, by simpa using i.isLt⟩ = e i := by
      intro i
      exact Fin.ext (by simp [e, Fin.castOrderIso])
    simp only [heq]
    rw [Equiv.sum_comp e (fun j => if polAssign φ α j then (1 : Rat) else 0)]
    exact polAssign_count φ α
  rw [hcount']
  have hn : (nPol φ : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (nPol_pos φ).ne'
  have hv : (nVars φ : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (nVars_pos φ).ne'
  simp [nPol, two_mul]
  field_simp [hn, hv]
  norm_num

private theorem polAssign_litIndex (φ : CNF) (α : Assignment) (ℓ : Lit)
    (hℓ : ℓ.var < nVars φ) :
    polAssign φ α (litIndex φ ℓ hℓ) = Lit.eval α ℓ := by
  unfold polAssign litIndex Lit.eval
  by_cases hs : ℓ.sign
  · simp [hs, hℓ]
  · have hn : ¬ nVars φ + ℓ.var < nVars φ := by omega
    simp [hs, hn]

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

private theorem eval_clauseFormula (φ : CNF) (α : Assignment) (c : Clause)
    (hc : c.length = 3) (hv : ∀ ℓ ∈ c, ℓ.var < nVars φ) :
    Formula.eval (polAssign φ α) (clauseFormula φ c hc hv) = Clause.eval α c := by
  have h0 := polAssign_litIndex φ α (clauseNth c hc 0)
    (hv _ (List.get_mem c _))
  have h1 := polAssign_litIndex φ α (clauseNth c hc 1)
    (hv _ (List.get_mem c _))
  have h2 := polAssign_litIndex φ α (clauseNth c hc 2)
    (hv _ (List.get_mem c _))
  simp [clauseFormula, or3, Formula.eval, h0, h1, h2, clause_eval_three α c hc]

private theorem compileFormulas_eval_sat (φ : CNF) (h3 : φ.Is3CNF)
    (α : Assignment) (hsat : CNF.eval α φ = true) (j : Fin φ.length) :
    Formula.eval (polAssign φ α) (compileFormulas φ h3 j) = true := by
  have hcmem : φ[j.val] ∈ φ := List.get_mem φ j
  have hallc : ∀ c ∈ φ, Clause.eval α c = true := by
    simpa [CNF.eval, List.all_eq_true] using hsat
  simpa [compileFormulas] using
    (eval_clauseFormula φ α φ[j.val] (h3 _ hcmem)
      (fun ℓ hℓ => lit_var_lt_nVars φ φ[j.val] ℓ hcmem hℓ)).trans
      (hallc _ hcmem)

/-- Sat 3CNF maps to `Yes 0` under the polarity-OR compiler.  Honest
one-polarity-per-variable cost is `1/2 ≤ budget 1`. -/
theorem compileData_yes_of_sat {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (hL : 3 ≤ L)
    (α : Assignment) (hsat : CNF.eval α φ = true) :
    Yes 0 (ofData (compileData φ h3 hM) (compileData_valid φ h3 hM hL)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => polAssign φ α ⟨i.val, (compileData_len h3 hM) ▸ i.isLt⟩,
    ?_, ?_⟩
  · have hcost := compileData_cost_polAssign φ h3 hM α
    simp only [compileData, indexedData] at hcost ⊢
    exact hcost.le.trans (by norm_num)
  · haveI : Nonempty (Fin (compileData φ h3 hM).formulas.length) := by
      simp [compileData, indexedData]
      exact ⟨⟨0, hM⟩⟩
    unfold Data.satisfaction
    have hall : ∀ j : Fin (compileData φ h3 hM).formulas.length,
        Formula.eval
          (fun i => polAssign φ α ⟨i.val, (compileData_len h3 hM) ▸ i.isLt⟩)
          ((compileData φ h3 hM).indexedFormulas j) = true := by
      intro j
      have hj : j.val < φ.length := by
        simpa [compileData, indexedData] using j.isLt
      have heval := indexedData_eval (compileWeights φ) (compileFormulas φ h3) 1
        (fun i => polAssign φ α ⟨i.val, by
          simpa [compileData, indexedData] using i.isLt⟩)
        ⟨j.val, hj⟩
      have hjFin : j = ⟨j.val, by simpa [compileData, indexedData] using j.isLt⟩ :=
        Fin.ext rfl
      rw [hjFin, Data.indexedFormulas]
      simp only [compileData, indexedData] at heval ⊢
      rw [heval]
      refine (congrArg (fun x => Formula.eval x
          (compileFormulas φ h3 ⟨j.val, hj⟩)) ?_).trans
        (compileFormulas_eval_sat φ h3 α hsat ⟨j.val, hj⟩)
      funext v
      exact congrArg (polAssign φ α) (Fin.ext (by simp))
    rw [show (fun j => Formula.eval
          (fun i => polAssign φ α ⟨i.val, (compileData_len h3 hM) ▸ i.isLt⟩)
          ((compileData φ h3 hM).indexedFormulas j)) = fun _ => true from
      funext hall]
    have hsat1 := average_true
      (I := Fin (compileData φ h3 hM).formulas.length)
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat1.symm)

private theorem compileData_cost_all_true (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) :
    (compileData φ h3 hM).cost (fun _ => true) = 1 := by
  unfold Data.cost Data.coordinateWeights weight compileData indexedData
  simp only [List.get_ofFn, ite_true, compileWeights]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  have hn : (nPol φ : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (nPol_pos φ).ne'
  field_simp [hn]

private theorem compileData_sat_all_true (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) :
    (compileData φ h3 hM).satisfaction (fun _ => true) = 1 := by
  haveI : Nonempty (Fin (compileData φ h3 hM).formulas.length) := by
    simp [compileData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (compileData φ h3 hM).formulas.length,
      Formula.eval (fun _ => true)
        ((compileData φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [compileData, indexedData] using j.isLt
    have heval := indexedData_eval (compileWeights φ) (compileFormulas φ h3) 1
      (fun _ => true) ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [compileData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [compileData, indexedData] at heval ⊢
    rw [heval]
    exact eval_all_true _
  rw [show (fun j => Formula.eval (fun _ => true)
        ((compileData φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

/-- Polarity-OR `compileData` is never `No` at manuscript `σ_L ≥ 1`:
lighting both polarities costs the honest budget `1` and satisfies every
monotone clause OR. -/
theorem compileData_not_no {L : Nat} (hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) (hL : 3 ≤ L) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (compileData φ h3 hM) (compileData_valid φ h3 hM hL)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  let x : Fin (compileData φ h3 hM).weights.length → Bool := fun _ => true
  have hx := hall x
  have hcost : (compileData φ h3 hM).cost x = 1 :=
    compileData_cost_all_true φ h3 hM
  have hsat : (compileData φ h3 hM).satisfaction x = 1 :=
    compileData_sat_all_true φ h3 hM
  have hb : (compileData φ h3 hM).budget = 1 := rfl
  have hle : (compileData φ h3 hM).cost x ≤
      (rofSigma L : Rat) * (compileData φ h3 hM).budget := by
    rw [hcost, hb]
    have hσQ : (1 : Rat) ≤ (rofSigma L : Rat) := Nat.one_le_cast.mpr hσ
    exact le_mul_of_one_le_left (by norm_num) hσQ
  have h1lt : (1 : Rat) < gammaL L := by simpa [hsat] using hx hle
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- Polarity-OR data at an arbitrary budget. `polAssign` still costs `1/2`. -/
def compileDataBudget (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) (b : Rat) : Data :=
  indexedData (compileWeights φ) (compileFormulas φ h3) b

theorem compileDataBudget_valid {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (hL : 3 ≤ L) (b : Rat) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    Valid L (compileDataBudget φ h3 hM b) := by
  refine indexedData_valid (compileWeights φ) (compileFormulas φ h3) b
    (compileWeights_pos φ) (compileWeights_sum φ) hM ?_ hb0 hb1
  intro i
  simp [compileFormulas, clauseFormula_leaves]
  exact hL

private theorem compileDataBudget_cost_all_true (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (b : Rat) :
    (compileDataBudget φ h3 hM b).cost (fun _ => true) = 1 := by
  unfold Data.cost Data.coordinateWeights weight compileDataBudget indexedData
  simp only [List.get_ofFn, ite_true, compileWeights]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  have hn : (nPol φ : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (nPol_pos φ).ne'
  field_simp [hn]

private theorem compileDataBudget_sat_all_true (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (b : Rat) :
    (compileDataBudget φ h3 hM b).satisfaction (fun _ => true) = 1 := by
  haveI : Nonempty (Fin (compileDataBudget φ h3 hM b).formulas.length) := by
    simp [compileDataBudget, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (compileDataBudget φ h3 hM b).formulas.length,
      Formula.eval (fun _ => true)
        ((compileDataBudget φ h3 hM b).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [compileDataBudget, indexedData] using j.isLt
    have heval := indexedData_eval (compileWeights φ) (compileFormulas φ h3) b
      (fun _ => true) ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [compileDataBudget, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [compileDataBudget, indexedData] at heval ⊢
    rw [heval]
    exact eval_all_true _
  rw [show (fun j => Formula.eval (fun _ => true)
        ((compileDataBudget φ h3 hM b).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

/-- No budget saves equal-weight polarity ORs once `σ ≥ 2`. A satisfying
assignment costs `1/2`, so any yes-budget is at least `1/2`, and all-true
then costs `1`, which is at most `σ` times that budget. -/
theorem compileDataBudget_not_no_of_half {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) (hL : 3 ≤ L) (b : Rat) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hhalf : (1 : Rat) / 2 ≤ b) (σ : Nat) (hσ : 2 ≤ σ) (γ : Rat)
    (_hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ¬ No (σ : Rat) γ
      (ofData (compileDataBudget φ h3 hM b)
        (compileDataBudget_valid φ h3 hM hL b hb0 hb1)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  let x : Fin (compileDataBudget φ h3 hM b).weights.length → Bool := fun _ => true
  have hx := hall x
  have hcost : (compileDataBudget φ h3 hM b).cost x = 1 :=
    compileDataBudget_cost_all_true φ h3 hM b
  have hsat : (compileDataBudget φ h3 hM b).satisfaction x = 1 :=
    compileDataBudget_sat_all_true φ h3 hM b
  have hb : (compileDataBudget φ h3 hM b).budget = b := by
    simp [compileDataBudget, indexedData]
  have hle : (compileDataBudget φ h3 hM b).cost x ≤ (σ : Rat) * b := by
    rw [hcost]
    have htwo : (2 : Rat) ≤ (σ : Rat) := by exact_mod_cast hσ
    have hnn : (0 : Rat) ≤ (1 : Rat) / 2 := by norm_num
    have hσnn : (0 : Rat) ≤ (σ : Rat) := by exact_mod_cast (Nat.zero_le σ)
    have hmul : (2 : Rat) * ((1 : Rat) / 2) ≤ (σ : Rat) * b :=
      mul_le_mul htwo hhalf hnn hσnn
    have hone : (2 : Rat) * ((1 : Rat) / 2) = 1 := by norm_num
    simpa [hone] using hmul
  have hball : (compileDataBudget φ h3 hM b).cost x ≤
      (σ : Rat) * (compileDataBudget φ h3 hM b).budget := by
    simpa [hb] using hle
  have h1lt : (1 : Rat) < γ := by simpa [hsat] using hx hball
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

/-- Width-3 tautology-free sat unit `(x₀ ∨ x₀ ∨ x₀)`. -/
def unit3 : CNF :=
  [[{ sign := true, var := 0 }, { sign := true, var := 0 },
      { sign := true, var := 0 }]]

theorem unit3_is3 : unit3.Is3CNF := by
  intro c hc
  simp [unit3] at hc
  subst hc
  simp

theorem unit3_len : 0 < unit3.length := by decide

theorem unit3_sat : CNF.eval [true] unit3 = true := by
  simp [unit3, CNF.eval, Clause.eval, Lit.eval, Assignment.get]

theorem unit3_yes {L : Nat} (hL : 3 ≤ L) :
    Yes 0 (ofData (compileData unit3 unit3_is3 unit3_len)
      (compileData_valid unit3 unit3_is3 unit3_len hL)) :=
  compileData_yes_of_sat unit3 unit3_is3 unit3_len hL [true] unit3_sat

end
end PvNP.RealizableHardness.ActualThreeSatCmmsaReduce


