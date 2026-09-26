import PvNP.RealizableHardness.ActualThreeSatAndAllNo
import Complexitylib.SAT.ThreeSAT

/-!
3SAT-tape-dependent Grassmann-alphabet `No` packing at `ROf L`.

Weights and budget are the AND-all gadget (`1/ROf L`).  Formulas are
`z.length + 1` copies of `andAllFormula`, so the encoded tree depends on
the 3SAT tape length.  Cheap assignments miss a coordinate, so every
formula is false and satisfaction is `0`.  All-true costs `1 > σ_L · budget`.

This sends **unsat well-formed** 3SAT encodings (and every other tape) to
`No σ_L γ_L`.  It is not 8-symbol `graphData`, not identity, not `if-sat`,
and not LeafFold/`unsatCnf`.  It is **not** a Yes-map, so it does not
inhabit `hSrcCmmsa` by itself.

The packing is semantic `encodeData` of that instance. A Cobham parser for
`decode3?` / this `dataTree` is a separate wire and is not claimed here.
-/
namespace PvNP.RealizableHardness.ActualThreeSatRofNo

open Complexity
open Complexity.SAT
open RandomizedReduction
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatAndAllNo
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

theorem ROf_add_one_le_L {L : Nat} (h : 256 ≤ mOf L) : ROf L + 1 ≤ L := by
  have hfit := compactLeaves_le h
  have htwo : 2 ≤ mOf L + 1 :=
    Nat.succ_le_succ (le_trans (by decide : 1 ≤ 256) h)
  have h2R : 2 * ROf L ≤ (mOf L + 1) * ROf L :=
    Nat.mul_le_mul_right (ROf L) htwo
  have hR1 : ROf L + 1 ≤ 2 * ROf L := by
    have := ROf_pos L
    omega
  exact hR1.trans (h2R.trans hfit)

/-- One AND-all copy per input bit, plus a trailing copy so the list is nonempty. -/
def rofNoFormulas (L : Nat) (z : List Bool) :
    Fin (z.length + 1) → Formula (Fin (ROf L)) :=
  fun _ => andAllFormula L

def rofNoData (L : Nat) (z : List Bool) : Data :=
  indexedData (andAllWeights L) (rofNoFormulas L z) (compactBudget (ROf L))

theorem rofNo_len (L : Nat) (z : List Bool) :
    (rofNoData L z).weights.length = ROf L := by
  simp [rofNoData, indexedData]

theorem rofNoData_valid {L : Nat} (h : 256 ≤ mOf L) (z : List Bool) :
    Valid L (rofNoData L z) := by
  refine indexedData_valid (andAllWeights L) (rofNoFormulas L z)
    (compactBudget (ROf L)) (andAllWeights_pos L) (andAllWeights_sum L)
    (Nat.succ_pos z.length) ?_ (compactBudget_pos (ROf_pos L))
    (compactBudget_le_one (ROf_pos L))
  intro i
  simpa [rofNoFormulas, andAllFormula_leaves] using ROf_le_L h

private theorem getElem_cons_replicate_same {α : Type*} (a : α) (n i : Nat)
    (h : i < n + 1) :
    (a :: List.replicate n a)[i]'(by
      simpa [List.length_cons, List.length_replicate] using h) = a := by
  cases i with
  | zero => simp
  | succ k =>
      have hk : k < n := Nat.lt_of_succ_lt_succ h
      simp [List.getElem_replicate, hk]

theorem rofNo_formula (L : Nat) (z : List Bool)
    (j : Fin (rofNoData L z).formulas.length) :
    (rofNoData L z).indexedFormulas j =
      Formula.rename (Fin.cast (rofNo_len L z).symm) (andAllFormula L) := by
  have hj : j.val < z.length + 1 := by simpa [rofNoData, indexedData] using j.isLt
  unfold Data.indexedFormulas
  change (rofNoData L z).formulas[j.val] = _
  simp [rofNoData, indexedData, rofNoFormulas, getElem_cons_replicate_same, hj]

theorem rofNo_eval_false (L : Nat) (z : List Bool)
    (x : Fin (rofNoData L z).weights.length → Bool)
    (i0 : Fin (rofNoData L z).weights.length) (hx0 : x i0 = false)
    (j : Fin (rofNoData L z).formulas.length) :
    Formula.eval x ((rofNoData L z).indexedFormulas j) = false := by
  rw [rofNo_formula, Formula.eval_rename]
  cases hZ : Formula.eval (fun v => x (Fin.cast (rofNo_len L z).symm v))
      (andAllFormula L) with
  | false => rfl
  | true =>
    have hall :=
      (eval_andAllFormula L (fun v => x (Fin.cast (rofNo_len L z).symm v))).mp hZ
    have hx := hall ⟨i0.val, by simpa [rofNo_len L z] using i0.isLt⟩
    have hcast :
        Fin.cast (rofNo_len L z).symm
          ⟨i0.val, by simpa [rofNo_len L z] using i0.isLt⟩ = i0 :=
      Fin.ext rfl
    rw [hcast] at hx
    simp [hx0] at hx

theorem rofNo_sat_zero (L : Nat) (z : List Bool)
    (x : Fin (rofNoData L z).weights.length → Bool)
    (i0 : Fin (rofNoData L z).weights.length) (hx0 : x i0 = false) :
    (rofNoData L z).satisfaction x = 0 := by
  have : Nonempty (Fin (rofNoData L z).formulas.length) := by
    simp [rofNoData, indexedData]
    infer_instance
  unfold Data.satisfaction
  rw [show (fun j => Formula.eval x ((rofNoData L z).indexedFormulas j)) =
      fun _ => false from funext (rofNo_eval_false L z x i0 hx0)]
  simp [average]

theorem rofNo_get_weight (L : Nat) (z : List Bool)
    (i : Fin (rofNoData L z).weights.length) :
    (rofNoData L z).weights.get i = (1 : Rat) / (ROf L : Rat) := by
  change (rofNoData L z).weights[i.val] = _
  simp [rofNoData, indexedData, List.getElem_ofFn, andAllWeights]

theorem rofNo_cost_all_true (L : Nat) (z : List Bool)
    (x : Fin (rofNoData L z).weights.length → Bool)
    (hx : ∀ i, x i = true) :
    (rofNoData L z).cost x = 1 := by
  unfold Data.cost Data.coordinateWeights weight
  simp only [hx, ite_true]
  rw [Finset.sum_congr rfl fun v _ => rofNo_get_weight L z v]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
    rofNo_len]
  have hR : (ROf L : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ROf_pos L).ne'
  field_simp [hR]

theorem rofNoInstance_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ : 0 < gammaL L) (_h8 : 8 ≤ ROf L)
    (z : List Bool) :
    No (rofSigma L) (gammaL L)
      (ofData (rofNoData L z) (rofNoData_valid h z)) := by
  dsimp [No]
  rw [ofData_data]
  intro x hx
  by_cases hall : ∀ i : Fin (rofNoData L z).weights.length, x i = true
  · have hcost : (rofNoData L z).cost x = 1 := rofNo_cost_all_true L z x hall
    have hb : (rofNoData L z).budget = compactBudget (ROf L) := rfl
    have hle : (1 : Rat) ≤ (rofSigma L : Rat) * compactBudget (ROf L) := by
      simpa [hcost, hb] using hx
    have hσA : (rofSigma L : Rat) * compactBudget (ROf L) =
        (rofSigma L : Rat) / (ROf L : Rat) := by
      unfold compactBudget
      field_simp
    have hlt : (rofSigma L : Rat) / (ROf L : Rat) < 1 := by
      have hRpos : (0 : Rat) < (ROf L : Rat) := Nat.cast_pos.mpr (ROf_pos L)
      exact (div_lt_one hRpos).2 (Nat.cast_lt.2 (rofSigma_lt_ROf L))
    exact (not_le_of_gt (hσA ▸ hlt) hle).elim
  · obtain ⟨i0, hx0⟩ := not_forall.mp hall
    have hx0f : x i0 = false := Bool.eq_false_iff.mpr hx0
    have hz : (rofNoData L z).satisfaction x = 0 :=
      rofNo_sat_zero L z x i0 hx0f
    simpa [hz] using hγ

def rofNoEnc (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) : List Bool :=
  encodeData (rofNoData L z) (rofNoData_valid h z)

theorem rofNoEnc_mem_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) (z : List Bool) :
    rofNoEnc L h z ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances :=
  cmmsaPromise_no_of_encode hσ hγ0 hγ1
    (ofData (rofNoData L z) (rofNoData_valid h z))
    (rofNoInstance_no h hσ hγ0 h8 z)

/-- Unsat well-formed exact-3CNF encodings land in `noInstances`. -/
theorem rofNoEnc_no_of_unsat_wellformed {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hunsat : ¬ φ.Satisfiable) :
    rofNoEnc L h φ.encode ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances := by
  have _ := h3
  have _ := hM
  have _ := hunsat
  exact rofNoEnc_mem_no h hσ hγ0 hγ1 h8 φ.encode

theorem rofNoEnc_ne_id {L : Nat} (h : 256 ≤ mOf L) (z : List Bool) :
    rofNoEnc L h z ≠ [] := by
  intro hz
  have hlen := congrArg List.length hz
  simp [rofNoEnc, encodeData, encode, ofData, dataTree,
    CMMSACodec.Tree.encode] at hlen

end
end PvNP.RealizableHardness.ActualThreeSatRofNo
