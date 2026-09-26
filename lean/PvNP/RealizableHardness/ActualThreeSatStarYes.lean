import PvNP.RealizableHardness.ActualThreeSatStarFp
import PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import Mathlib.Algebra.BigOperators.Fin

/-!
Grassmann-alphabet 1-clause polarity-OR `Data` at `ROf L`: `Yes 0` via
lighting coordinate `0`, and not `No σ_L γ_L` by the same cheap witness.

This is the semantic instance whose `encodeData` layout `starEncFn`
emits.  It is not a general-φ `paramStarData` packing, not a No-map on
unsat 3SAT, not `if-sat`, and does not inhabit `hSrcCmmsa`.
Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarYes

open Complexity hiding Data
open Complexity.SAT
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFp
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

def unitStarN (L : Nat) : Nat := 2 * ROf L

theorem unitStarN_pos (L : Nat) : 0 < unitStarN L :=
  Nat.mul_pos Nat.two_pos (ROf_pos L)

def unitStarWeights (L : Nat) : Fin (unitStarN L) → Rat :=
  fun _ => (1 : Rat) / (unitStarN L : Rat)

theorem unitStarWeights_pos (L : Nat) (v : Fin (unitStarN L)) :
    0 < unitStarWeights L v :=
  div_pos (by norm_num) (Nat.cast_pos.mpr (unitStarN_pos L))

theorem unitStarWeights_sum (L : Nat) :
    (∑ v : Fin (unitStarN L), unitStarWeights L v) = 1 := by
  simp [unitStarWeights]
  have h : (unitStarN L : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (unitStarN_pos L).ne'
  field_simp [h, Fintype.card_fin]

def unitStarOr {L : Nat} : Formula (Fin (unitStarN L)) :=
  or3 (.var ⟨0, unitStarN_pos L⟩) (.var ⟨0, unitStarN_pos L⟩)
    (.var ⟨0, unitStarN_pos L⟩)

def unitStarFormulas (L : Nat) : Fin 1 → Formula (Fin (unitStarN L)) :=
  fun _ => unitStarOr

def unitStarData (L : Nat) : Data :=
  indexedData (unitStarWeights L) (unitStarFormulas L) (compactBudget (ROf L))

theorem unitStarData_valid {L : Nat} (hL : 3 ≤ L) :
    Valid L (unitStarData L) := by
  refine indexedData_valid (unitStarWeights L) (unitStarFormulas L)
    (compactBudget (ROf L)) (unitStarWeights_pos L) (unitStarWeights_sum L)
    (Nat.succ_pos 0) ?_ (compactBudget_pos (ROf_pos L))
    (compactBudget_le_one (ROf_pos L))
  intro i
  simp [unitStarFormulas, unitStarOr, or3, Formula.leaves]
  exact hL

theorem unitStarData_len (L : Nat) :
    (unitStarData L).weights.length = unitStarN L := by
  simp [unitStarData, indexedData]

private theorem unitStar_cost_coord0 (L : Nat) :
    (unitStarData L).cost
      (fun i => decide (i.val = 0)) = unitStarWeights L ⟨0, unitStarN_pos L⟩ := by
  unfold Data.cost Data.coordinateWeights weight unitStarData indexedData
  simp only [List.get_ofFn, unitStarWeights]
  refine Eq.trans (Finset.sum_eq_single
      (⟨0, by simp [unitStarN_pos]⟩ :
        Fin (List.ofFn (unitStarWeights L)).length) ?_ ?_) ?_
  · intro b _ hb
    have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [hb0]
  · simp
  · simp

private theorem unitStar_eval_coord0 (L : Nat) :
    Formula.eval (fun i : Fin (unitStarN L) => decide (i.val = 0))
      unitStarOr = true := by
  simp [unitStarOr, or3, Formula.eval]

theorem unitStarData_yes {L : Nat} (hL : 3 ≤ L) :
    Yes 0 (ofData (unitStarData L) (unitStarData_valid hL)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => decide (i.val = 0), ?_, ?_⟩
  · have hcost := unitStar_cost_coord0 L
    have hle : unitStarWeights L ⟨0, unitStarN_pos L⟩ ≤ compactBudget (ROf L) := by
      unfold unitStarWeights compactBudget unitStarN
      have hR : (0 : Rat) < (ROf L : Rat) := Nat.cast_pos.mpr (ROf_pos L)
      have hn : (0 : Rat) < ((2 * ROf L : Nat) : Rat) :=
        Nat.cast_pos.mpr (Nat.mul_pos Nat.two_pos (ROf_pos L))
      rw [div_le_div_iff₀ hn hR]
      simp [two_mul]
    exact hcost.trans_le (by simpa [unitStarData, indexedData] using hle)
  · haveI : Nonempty (Fin (unitStarData L).formulas.length) := by
      simp [unitStarData, indexedData]
      exact ⟨⟨0, Nat.zero_lt_one⟩⟩
    unfold Data.satisfaction
    have hall : ∀ j : Fin (unitStarData L).formulas.length,
        Formula.eval (fun i => decide (i.val = 0))
          ((unitStarData L).indexedFormulas j) = true := by
      intro j
      have heval := indexedData_eval (unitStarWeights L) (unitStarFormulas L)
        (compactBudget (ROf L))
        (fun i => decide (i.val = 0)) ⟨0, Nat.zero_lt_one⟩
      have hj : j = ⟨0, by simpa [unitStarData, indexedData] using j.isLt⟩ :=
        Fin.ext (Nat.lt_one_iff.mp (by simpa [unitStarData, indexedData] using j.isLt))
      rw [hj, Data.indexedFormulas]
      simp only [unitStarData, indexedData] at heval ⊢
      rw [heval]
      refine (congrArg (fun x => Formula.eval x unitStarOr) ?_).trans
        (unitStar_eval_coord0 L)
      funext v
      simp
    rw [show (fun j => Formula.eval (fun i => decide (i.val = 0))
          ((unitStarData L).indexedFormulas j)) = fun _ => true from
      funext hall]
    have hsat1 := average_true (I := Fin (unitStarData L).formulas.length)
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat1.symm)

theorem unitStarData_not_no {L : Nat} (hL : 3 ≤ L)
    (hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (unitStarData L) (unitStarData_valid hL)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  have hY := unitStarData_yes (L := L) hL
  dsimp [Yes] at hY
  rw [ofData_data] at hY
  obtain ⟨y, hcost, hsat⟩ := hY
  have hbud : (0 : Rat) < (unitStarData L).budget :=
    compactBudget_pos (ROf_pos L)
  have hσQ : (1 : Rat) ≤ (rofSigma L : Rat) := Nat.one_le_cast.mpr hσ
  have hscale : (unitStarData L).budget ≤
      (rofSigma L : Rat) * (unitStarData L).budget :=
    le_mul_of_one_le_left (le_of_lt hbud) hσQ
  have hcost' : (unitStarData L).cost y ≤
      (rofSigma L : Rat) * (unitStarData L).budget :=
    le_trans hcost hscale
  have hsat1 : (1 : Rat) ≤ (unitStarData L).satisfaction y := by
    simpa using hsat
  have h1lt : (1 : Rat) < gammaL L :=
    lt_of_le_of_lt hsat1 (hall y hcost')
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

theorem unitStarData_yes_mem {L : Nat} (hL : 3 ≤ L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    encodeData (unitStarData L) (unitStarData_valid hL) ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).yesInstances :=
  cmmsaPromise_yes_of_encode hσ hγ0 hγ1
    (ofData (unitStarData L) (unitStarData_valid hL))
    (unitStarData_yes hL)

end
end PvNP.RealizableHardness.ActualThreeSatStarYes
