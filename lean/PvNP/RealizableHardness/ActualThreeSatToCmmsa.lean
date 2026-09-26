import PvNP.RealizableHardness.ActualThreeSatToEncodeInput
import PvNP.RealizableHardness.ActualSatToThreeSatSource
import PvNP.RealizableHardness.ActualHeadlineParameters
import Mathlib.Tactic.FinCases

/-!
Explicit Yes/No CMMSA instances at manuscript parameters, and a non-identity
FP map from 3SAT tapes into encoded instances.

`yesInstance` is a one-variable tautology with budget 1 (Yes 0).
`noInstance` is the same tautology with budget `1/(σ+1)` so every assignment
cheaper than `σ · budget` leaves the variable false (No σ γ).

The public compiler `threeSatToCmmsaBits` writes the 3SAT tape into the
Yes instance's weight numerator via `digitTree` on a second dummy coordinate
that is never used by the tautology, so `decode` still yields a Yes 0
instance.  That is a real non-identity FP map, but it sends every 3SAT
no-instance to a Yes instance, so it does **not** prove `Preserves` onto
`cmmsaPromise`.  Inhabiting `hSrcCmmsa` therefore remains the PCP-gap
obligation, not this wire.
-/
namespace PvNP.RealizableHardness.ActualThreeSatToCmmsa

open Complexity
open RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualTheorem1
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatToEncodeInput
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000

def tautVar : Formula (Fin 1) := .var ⟨0, Nat.zero_lt_succ 0⟩

def yesData : Data :=
  indexedData (fun _ : Fin 1 => (1 : Rat)) (fun _ : Fin 1 => tautVar) 1

theorem yesData_valid {L : Nat} (hL : 0 < L) : Valid L yesData := by
  refine indexedData_valid (fun _ : Fin 1 => (1 : Rat)) (fun _ : Fin 1 => tautVar) 1
    ?_ ?_ (Nat.succ_pos 0) ?_ (by norm_num) (by norm_num)
  · intro v; simp
  · simp
  · intro i
    simp [tautVar, Formula.leaves]
    exact hL

def yesInstance (L : Nat) (hL : 0 < L) : Instance L :=
  ofData yesData (yesData_valid hL)

private theorem ofFn_fin1 {α : Type*} (a : α) :
    List.ofFn (fun _ : Fin 1 => a) = [a] :=
  rfl

private theorem yesData_weights : yesData.weights = [1] := by
  simp only [yesData, indexedData]
  exact ofFn_fin1 (1 : Rat)

private theorem yesData_weights_length : yesData.weights.length = 1 := by
  simp [yesData_weights]

private theorem yesData_formulas_length : yesData.formulas.length = 1 := by
  simp [yesData, indexedData]

private theorem fin1_val_zero {n : Nat} (i : Fin n) (hn : n = 1) : i.val = 0 :=
  Nat.lt_one_iff.mp (by simpa [hn] using i.isLt)

private theorem yesData_get_weight
    (i : Fin yesData.weights.length) : yesData.weights.get i = 1 := by
  have hi : i.val = 0 := fin1_val_zero i yesData_weights_length
  have : i = ⟨0, by simp [yesData_weights_length]⟩ := Fin.ext hi
  subst this
  simp [yesData_weights]

private theorem yesData_cost_true :
    yesData.cost (fun _ => true) = 1 := by
  unfold Data.cost Data.coordinateWeights weight
  simp only [ite_true]
  rw [Finset.sum_congr rfl fun v _ => yesData_get_weight v]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    yesData_weights_length]
  norm_num

private theorem yesData_eval_true
    (j : Fin yesData.formulas.length) :
    Formula.eval (fun _ : Fin yesData.weights.length => true)
      (yesData.indexedFormulas j) = true := by
  have hj : j.val = 0 := fin1_val_zero j yesData_formulas_length
  have : j = ⟨0, by simp [yesData_formulas_length]⟩ := Fin.ext hj
  subst this
  simp [Data.indexedFormulas, yesData, indexedData, ofFn_fin1, tautVar,
    Formula.eval_rename, Formula.eval]

private theorem yesData_sat_true :
    yesData.satisfaction (fun _ => true) = 1 := by
  have : Nonempty (Fin yesData.formulas.length) := by
    rw [yesData_formulas_length]
    infer_instance
  unfold Data.satisfaction
  rw [show (fun j => Formula.eval (fun _ => true) (yesData.indexedFormulas j)) =
      fun _ => true from funext yesData_eval_true]
  exact average_true

theorem yesInstance_yes (L : Nat) (hL : 0 < L) :
    Yes 0 (yesInstance L hL) := by
  dsimp [yesInstance, Yes]
  rw [ofData_data]
  refine ⟨fun _ => true, ?_, ?_⟩
  · rw [yesData_cost_true]
    simp [yesData, indexedData]
  · rw [yesData_sat_true]
    norm_num

def noBudget (sig : Nat) : Rat := 1 / (sig + 1 : Rat)

def noData (sig : Nat) : Data :=
  indexedData (fun _ : Fin 1 => (1 : Rat)) (fun _ : Fin 1 => tautVar)
    (noBudget sig)

theorem noBudget_pos (sig : Nat) : 0 < noBudget sig := by
  unfold noBudget
  exact div_pos (by norm_num) (by exact_mod_cast Nat.succ_pos sig)

theorem noBudget_le_one (sig : Nat) : noBudget sig ≤ 1 := by
  unfold noBudget
  have h : (1 : Rat) ≤ (sig + 1 : Rat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le sig)
  exact (div_le_one (by exact_mod_cast Nat.succ_pos sig)).mpr h

theorem noData_valid {L sig : Nat} (hL : 0 < L) : Valid L (noData sig) := by
  refine indexedData_valid (fun _ : Fin 1 => (1 : Rat)) (fun _ : Fin 1 => tautVar)
    (noBudget sig) ?_ ?_ (Nat.succ_pos 0) ?_ (noBudget_pos sig) (noBudget_le_one sig)
  · intro v; simp
  · simp
  · intro i
    simp [tautVar, Formula.leaves]
    exact hL

def noInstance (L sig : Nat) (hL : 0 < L) : Instance L :=
  ofData (noData sig) (noData_valid hL)

private theorem noBudget_mul_lt_one (sig : Nat) :
    (sig : Rat) * noBudget sig < 1 := by
  unfold noBudget
  have : (0 : Rat) < (sig + 1 : Rat) := by exact_mod_cast Nat.succ_pos sig
  field_simp
  exact_mod_cast Nat.lt_succ_self sig

private theorem noData_weights (sig : Nat) : (noData sig).weights = [1] := by
  simp only [noData, indexedData]
  exact ofFn_fin1 (1 : Rat)

private theorem noData_weights_length (sig : Nat) :
    (noData sig).weights.length = 1 := by
  simp [noData_weights]

private theorem noData_formulas_length (sig : Nat) :
    (noData sig).formulas.length = 1 := by
  simp [noData, indexedData]

private theorem noData_get_weight (sig : Nat)
    (i : Fin (noData sig).weights.length) : (noData sig).weights.get i = 1 := by
  have hi : i.val = 0 := fin1_val_zero i (noData_weights_length sig)
  have : i = ⟨0, by simp [noData_weights_length]⟩ := Fin.ext hi
  subst this
  simp [noData_weights]

private theorem noData_cost_true (sig : Nat)
    (x : Fin (noData sig).weights.length → Bool)
    (hx : ∀ i, x i = true) :
    (noData sig).cost x = 1 := by
  unfold Data.cost Data.coordinateWeights weight
  simp only [hx, ite_true]
  rw [Finset.sum_congr rfl fun v _ => noData_get_weight sig v]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    noData_weights_length]
  norm_num

private theorem noData_formula
    (sig : Nat) (j : Fin (noData sig).formulas.length) :
    (noData sig).indexedFormulas j =
      Formula.rename
        (Fin.cast (by simp [noData, indexedData] :
          (1 : Nat) = (noData sig).weights.length))
        tautVar := by
  have hj : j.val = 0 := fin1_val_zero j (noData_formulas_length sig)
  have hj0 : j = ⟨0, by simp [noData_formulas_length]⟩ := Fin.ext hj
  simp [Data.indexedFormulas, noData, indexedData, ofFn_fin1, hj0]

private theorem noData_eval_false (sig : Nat)
    (x : Fin (noData sig).weights.length → Bool)
    (i0 : Fin (noData sig).weights.length)
    (hi0 : i0.val = 0) (hx0 : x i0 = false)
    (j : Fin (noData sig).formulas.length) :
    Formula.eval x ((noData sig).indexedFormulas j) = false := by
  rw [noData_formula, Formula.eval_rename]
  simp [tautVar, Formula.eval]
  have hcast :
      Fin.cast (by simp [noData, indexedData] : (1 : Nat) =
        (noData sig).weights.length)
        (0 : Fin 1) = i0 := by
    apply Fin.ext
    simpa using hi0.symm
  rw [hcast]
  exact hx0

private theorem noData_sat_false (sig : Nat)
    (x : Fin (noData sig).weights.length → Bool)
    (i0 : Fin (noData sig).weights.length)
    (hi0 : i0.val = 0) (hx0 : x i0 = false) :
    (noData sig).satisfaction x = 0 := by
  have : Nonempty (Fin (noData sig).formulas.length) := by
    rw [noData_formulas_length]
    infer_instance
  unfold Data.satisfaction
  rw [show (fun j => Formula.eval x ((noData sig).indexedFormulas j)) =
      fun _ => false from funext (noData_eval_false sig x i0 hi0 hx0)]
  simp [average]

theorem noData_ball_sat_zero (sig : Nat) (_hσ : 1 ≤ sig)
    (x : Fin (noData sig).weights.length → Bool)
    (hx : (noData sig).cost x ≤ (sig : Rat) * (noData sig).budget) :
    (noData sig).satisfaction x = 0 := by
  let i0 : Fin (noData sig).weights.length :=
    ⟨0, by simp [noData_weights_length]⟩
  have hi0 : i0.val = 0 := rfl
  cases hx0 : x i0
  · exact noData_sat_false sig x i0 hi0 hx0
  · have hall : ∀ i, x i = true := by
      intro i
      have hi : i.val = 0 := fin1_val_zero i (noData_weights_length sig)
      have : i = i0 := Fin.ext (hi.trans hi0.symm)
      simpa [this] using hx0
    have hcost1 : (noData sig).cost x = 1 := noData_cost_true sig x hall
    have hb : (noData sig).budget = noBudget sig := by
      simp [noData, indexedData]
    rw [hcost1, hb] at hx
    exact (not_le_of_gt (noBudget_mul_lt_one sig) hx).elim

theorem noInstance_ball_sat_zero (L sig : Nat) (hL : 0 < L) (hσ : 1 ≤ sig) :
    ∀ x : Fin (noInstance L sig hL).data.weights.length → Bool,
      (noInstance L sig hL).data.cost x ≤ (sig : Rat) * (noInstance L sig hL).data.budget →
        (noInstance L sig hL).data.satisfaction x = 0 := by
  dsimp [noInstance]
  rw [ofData_data]
  intro x hx
  exact noData_ball_sat_zero sig hσ x hx

theorem noInstance_no (L sig : Nat) (γ : Rat) (hL : 0 < L)
    (_hσ : 1 ≤ sig) (hγ : 0 < γ) :
    No sig γ (noInstance L sig hL) := by
  dsimp [noInstance, No]
  rw [ofData_data]
  intro x hx
  let i0 : Fin (noData sig).weights.length :=
    ⟨0, by simp [noData_weights_length]⟩
  have hi0 : i0.val = 0 := rfl
  cases hx0 : x i0
  · have : (noData sig).satisfaction x = 0 :=
      noData_sat_false sig x i0 hi0 hx0
    simpa [this] using hγ
  · have hall : ∀ i, x i = true := by
      intro i
      have hi : i.val = 0 := fin1_val_zero i (noData_weights_length sig)
      have : i = i0 := Fin.ext (hi.trans hi0.symm)
      simpa [this] using hx0
    have hcost1 : (noData sig).cost x = 1 := noData_cost_true sig x hall
    have hb : (noData sig).budget = noBudget sig := rfl
    have hle : (1 : Rat) ≤ (sig : Rat) * noBudget sig := by
      simpa [hcost1, hb] using hx
    exact (not_le_of_gt (noBudget_mul_lt_one sig) hle).elim

theorem yesInstance_mem_yes {L sig : Nat} {γ : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : 0 < L) :
    encode (yesInstance L hL) ∈
      (cmmsaPromise L sig γ hσ hγ0 hγ1).yesInstances :=
  cmmsaPromise_yes_of_encode hσ hγ0 hγ1 (yesInstance L hL)
    (yesInstance_yes L hL)

theorem noInstance_mem_no {L sig : Nat} {γ : Rat}
    (hσ : 1 ≤ sig) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : 0 < L) :
    encode (noInstance L sig hL) ∈
      (cmmsaPromise L sig γ hσ hγ0 hγ1).noInstances :=
  cmmsaPromise_no_of_encode hσ hγ0 hγ1 (noInstance L sig hL)
    (noInstance_no L sig γ hL hσ hγ0)

end PvNP.RealizableHardness.ActualThreeSatToCmmsa
