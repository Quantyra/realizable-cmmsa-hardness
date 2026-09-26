import PvNP.RealizableHardness.ActualCompactStarCompile
import PvNP.RealizableHardness.ActualThreeSatToCmmsa
import PvNP.RealizableHardness.ActualThreeSatToEncodeInput
import PvNP.RealizableHardness.ActualThreeSatXorStars
import PvNP.RealizableHardness.ActualThreeSatPresentedLeaf

/-!
Grassmann-alphabet CMMSA `No` instance at manuscript `σ_L` / `γ_L`.

`andAllData` uses alphabet `ROf L` (the Grassmann `alph (hOf L)`), uniform
weights, budget `1/ROf L`, and a single AND of every coordinate.  All-true
has cost `1`.  Cheap assignments obey `cost ≤ σ_L / ROf L = 1/8 < 1` once
`8 ≤ ROf L`, so they cannot light every coordinate.  The AND is therefore
false and satisfaction is `0 < γ_L`.

This is the empty-fold compilation of an unsatisfiable Grassmann pair:
no accepting labeling exists, and the packed monotone formula is the
AND over the full live alphabet (larger than `σ_L`).  Identity-projection
stars and 8-symbol `toGraph` packings cannot give `No` because their live
alphabet is `≤ σ_L`.

The instance does **not** by itself inhabit `hSrcCmmsa`: a sat 3SAT must
still map to `Yes 0` via a uniform PCP compiler (the `graphData` Yes-0
map).  Combining those two maps by an `if sat` test is forbidden.
`unsatCnf` / LeafFold is not used as a general 3SAT reduction.
-/
namespace PvNP.RealizableHardness.ActualThreeSatAndAllNo

open Complexity
open RandomizedReduction
open ActualHeadlineParameters
open ActualCompactStarCompile
open ActualThreeSatToCmmsa
open ActualThreeSatToEncodeInput
open ActualThreeSatXorStars
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

def andAllSlots (L : Nat) : Fin (ROf L) → Formula (Fin (ROf L)) :=
  fun a => .var a

def andAllFormula (L : Nat) : Formula (Fin (ROf L)) :=
  Option.get (andFin (ROf L) (andAllSlots L))
    (andFin_isSome (ROf_pos L) _)

theorem andAllFormula_andFin (L : Nat) :
    andFin (ROf L) (andAllSlots L) = some (andAllFormula L) :=
  (Option.some_get (andFin_isSome (ROf_pos L) _)).symm

theorem andAllFormula_leaves (L : Nat) :
    Formula.leaves (andAllFormula L) = ROf L := by
  have h := andFin_leaves (ROf L) (andAllSlots L) (andAllFormula L)
    (andAllFormula_andFin L)
  have hs : ∀ a, Formula.leaves (andAllSlots L a) = 1 := fun _ => rfl
  rw [h, Finset.sum_congr rfl fun a _ => hs a, Finset.sum_const, nsmul_eq_mul]
  simp [Finset.card_univ, Fintype.card_fin]

theorem eval_andAllFormula (L : Nat) (Z : Fin (ROf L) → Bool) :
    Formula.eval Z (andAllFormula L) = true ↔ ∀ a, Z a = true := by
  have h := eval_andFin Z (ROf L) (andAllSlots L) (andAllFormula L)
    (andAllFormula_andFin L)
  constructor
  · intro hf a
    simpa [andAllSlots, Formula.eval] using (h.mp hf) a
  · intro hall
    refine h.mpr ?_
    intro a
    simpa [andAllSlots, Formula.eval] using hall a

def andAllWeights (L : Nat) : Fin (ROf L) → Rat :=
  fun _ => (1 : Rat) / (ROf L : Rat)

theorem andAllWeights_pos (L : Nat) (v : Fin (ROf L)) :
    0 < andAllWeights L v :=
  div_pos (by norm_num) (Nat.cast_pos.mpr (ROf_pos L))

theorem andAllWeights_sum (L : Nat) :
    (∑ v : Fin (ROf L), andAllWeights L v) = 1 := by
  simp [andAllWeights, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  have hR : (ROf L : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ROf_pos L).ne'
  field_simp [hR]

def andAllData (L : Nat) : Data :=
  indexedData (andAllWeights L) (fun _ : Fin 1 => andAllFormula L)
    (compactBudget (ROf L))

theorem andAll_len (L : Nat) : (andAllData L).weights.length = ROf L := by
  simp [andAllData, indexedData]

theorem ROf_le_L {L : Nat} (h : 256 ≤ mOf L) : ROf L ≤ L :=
  le_trans (Nat.le_mul_of_pos_left (ROf L) (Nat.succ_pos (mOf L)))
    (by simpa [Nat.mul_comm] using compactLeaves_le h)

theorem andAllData_valid {L : Nat} (h : 256 ≤ mOf L) :
    Valid L (andAllData L) := by
  refine indexedData_valid (andAllWeights L)
    (fun _ : Fin 1 => andAllFormula L) (compactBudget (ROf L))
    (andAllWeights_pos L) (andAllWeights_sum L)
    (Nat.succ_pos 0) ?_ (compactBudget_pos (ROf_pos L))
    (compactBudget_le_one (ROf_pos L))
  intro _
  simpa [andAllFormula_leaves] using ROf_le_L h

theorem andAll_get_weight (L : Nat)
    (i : Fin (andAllData L).weights.length) :
    (andAllData L).weights.get i = (1 : Rat) / (ROf L : Rat) := by
  change (andAllData L).weights[i.val] = _
  simp [andAllData, indexedData, List.getElem_ofFn, andAllWeights]

theorem andAll_cost_all_true (L : Nat)
    (x : Fin (andAllData L).weights.length → Bool)
    (hx : ∀ i, x i = true) :
    (andAllData L).cost x = 1 := by
  unfold Data.cost Data.coordinateWeights weight
  simp only [hx, ite_true]
  rw [Finset.sum_congr rfl fun v _ => andAll_get_weight L v]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
    andAll_len]
  have hR : (ROf L : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ROf_pos L).ne'
  field_simp [hR]

theorem andAll_formula (L : Nat)
    (j : Fin (andAllData L).formulas.length) :
    (andAllData L).indexedFormulas j =
      Formula.rename (Fin.cast (andAll_len L).symm) (andAllFormula L) := by
  have hj : j.val = 0 :=
    Nat.lt_one_iff.mp (by simpa [andAllData, indexedData] using j.isLt)
  unfold Data.indexedFormulas
  change (andAllData L).formulas[j.val] = _
  simp [andAllData, indexedData, hj]

theorem andAll_eval_false (L : Nat)
    (x : Fin (andAllData L).weights.length → Bool)
    (i0 : Fin (andAllData L).weights.length) (hx0 : x i0 = false)
    (j : Fin (andAllData L).formulas.length) :
    Formula.eval x ((andAllData L).indexedFormulas j) = false := by
  rw [andAll_formula, Formula.eval_rename]
  cases hZ : Formula.eval (fun v => x (Fin.cast (andAll_len L).symm v))
      (andAllFormula L) with
  | false => rfl
  | true =>
    have hall :=
      (eval_andAllFormula L (fun v => x (Fin.cast (andAll_len L).symm v))).mp hZ
    have hx := hall ⟨i0.val, by simpa [andAll_len L] using i0.isLt⟩
    have hcast :
        Fin.cast (andAll_len L).symm
          ⟨i0.val, by simpa [andAll_len L] using i0.isLt⟩ = i0 :=
      Fin.ext rfl
    rw [hcast] at hx
    simp [hx0] at hx

theorem andAll_sat_zero_of_not_all_true (L : Nat)
    (x : Fin (andAllData L).weights.length → Bool)
    (i0 : Fin (andAllData L).weights.length) (hx0 : x i0 = false) :
    (andAllData L).satisfaction x = 0 := by
  have : Nonempty (Fin (andAllData L).formulas.length) := by
    simp [andAllData, indexedData]
    infer_instance
  unfold Data.satisfaction
  rw [show (fun j => Formula.eval x ((andAllData L).indexedFormulas j)) =
      fun _ => false from funext (andAll_eval_false L x i0 hx0)]
  simp [average]

theorem andAllInstance_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ : 0 < gammaL L) (_h8 : 8 ≤ ROf L) :
    No (rofSigma L) (gammaL L)
      (ofData (andAllData L) (andAllData_valid h)) := by
  dsimp [No]
  rw [ofData_data]
  intro x hx
  by_cases hall : ∀ i : Fin (andAllData L).weights.length, x i = true
  · have hcost : (andAllData L).cost x = 1 := andAll_cost_all_true L x hall
    have hb : (andAllData L).budget = compactBudget (ROf L) := rfl
    have hle : (1 : Rat) ≤ (rofSigma L : Rat) * compactBudget (ROf L) := by
      simpa [hcost, hb] using hx
    have hσA : (rofSigma L : Rat) * compactBudget (ROf L) =
        (rofSigma L : Rat) / (ROf L : Rat) := by
      unfold compactBudget
      field_simp
    have hlt : (rofSigma L : Rat) / (ROf L : Rat) < 1 := by
      have hRpos : (0 : Rat) < (ROf L : Rat) :=
        Nat.cast_pos.mpr (ROf_pos L)
      exact (div_lt_one hRpos).2 (Nat.cast_lt.2 (rofSigma_lt_ROf L))
    exact (not_le_of_gt (hσA ▸ hlt) hle).elim
  · obtain ⟨i0, hx0⟩ := not_forall.mp hall
    have hx0f : x i0 = false := Bool.eq_false_iff.mpr hx0
    have hz : (andAllData L).satisfaction x = 0 :=
      andAll_sat_zero_of_not_all_true L x i0 hx0f
    simpa [hz] using hγ

theorem andAllBits_mem_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) :
    encodeData (andAllData L) (andAllData_valid h) ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).noInstances :=
  cmmsaPromise_no_of_encode hσ hγ0 hγ1
    (ofData (andAllData L) (andAllData_valid h))
    (andAllInstance_no h hσ hγ0 h8)

/-- Non-identity FP encoder of the Grassmann-alphabet No instance.
The 3SAT tape is a suffix (`encodeDigitsFn`); the instance itself is the
constant AND-all No gadget.  This does **not** `MapReducesVia` Yes, so it
does not inhabit `hSrcCmmsa`. -/
def threeSatNoEncFn (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) : List Bool :=
  encodeData (andAllData L) (andAllData_valid h) ++ encodeDigitsFn z

theorem threeSatNoEncFn_mem_FP (L : Nat) (h : 256 ≤ mOf L) :
    threeSatNoEncFn L h ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP
    (constFn_mem_FP (encodeData (andAllData L) (andAllData_valid h)))
    encodeDigitsFn_mem_FP

theorem threeSatNoEncFn_ne_id (L : Nat) (h : 256 ≤ mOf L) :
    threeSatNoEncFn L h [] ≠ [] := by
  simp [threeSatNoEncFn, encodeData, encode, ofData, dataTree,
    CMMSACodec.Tree.encode]

end
end PvNP.RealizableHardness.ActualThreeSatAndAllNo
