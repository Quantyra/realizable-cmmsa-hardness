import PvNP.RealizableHardness.ActualRestrictCompile
import PvNP.RealizableHardness.ActualGrassmannDualStar
import PvNP.RealizableHardness.ActualThreeSatXorStars
import PvNP.RealizableHardness.ActualThreeSatStarFamily
import PvNP.RealizableHardness.ActualCMMSARandomizedReduction
import Mathlib.Algebra.BigOperators.Fin

/-!
3SAT-dependent m-ary Grassmann *restriction* stars (`compileRes`, `k = 1`),
not identity-projection, not polarity-OR, not XOR-star.

Each 3-clause supplies the center (`clausePol` lit 0).  Leaves are
`mOf L` dummy Grassmann vertices.  The compiled formula has
`(mOf L + 1) * ROf L` leaves and fits `L` once `256 ≤ mOf L`.
`restrictLow` on the first bit is not the identity.

The monochromatic label-0 1-hot satisfies every such star, so the family
is `Yes 0` on every nonempty 3CNF, including unsat.  It is therefore not
`No σ_L γ_L` and does not inhabit `hSrcCmmsa`.  Not `if-sat`.
Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGrassmannRes

open Complexity
open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualRestrictCompile
open ActualGrassmannDualStar
open ActualThreeSatXorStars
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFamily
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

def resH (L : Nat) : Nat := hOf L (mOf L)

def resK : Nat := 1

theorem resK_le {L : Nat} (hh : 0 < resH L) : resK ≤ 2 * resH L :=
  one_le_two_mul hh

theorem resK_lt {L : Nat} (hh : 0 < resH L) : resK < 2 * resH L :=
  one_lt_two_mul hh

def resN (L : Nat) (φ : CNF) : Nat := nPol φ + paramN L

theorem resN_pos (L : Nat) (φ : CNF) : 0 < resN L φ :=
  Nat.add_pos_right _ (paramN_pos L)

def resCenter {L : Nat} (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Fin (resN L φ) :=
  ⟨(clausePol φ h3 i 0).val,
    Nat.lt_add_right (paramN L) (clausePol φ h3 i 0).isLt⟩

def resLeaf (L : Nat) (φ : CNF) : Fin (paramM L) → Fin (resN L φ) :=
  fun j =>
    ⟨nPol φ + (j.val + 1), by
      have hj : j.val + 1 < paramN L := Nat.succ_lt_succ j.isLt
      exact Nat.add_lt_add_left hj (nPol φ)⟩

def resFormula {L : Nat} (hh : 0 < resH L) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Formula (Fin (resN L φ * alph (resH L))) :=
  compileRes (resK_le hh) (resCenter φ h3 i) (resLeaf L φ)

theorem resFormula_leaves {L : Nat} (hh : 0 < resH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.leaves (resFormula hh φ h3 i) =
      alph (resH L) * (paramM L + 1) := by
  simpa [resFormula, paramM] using
    compileRes_leaves (resK_le hh) (resCenter φ h3 i) (resLeaf L φ)

def resFormulas {L : Nat} (hh : 0 < resH L) (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (resN L φ * alph (resH L))) :=
  fun i => resFormula hh φ h3 i

def resStarData {L : Nat} (hh : 0 < resH L) (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (resN L φ) (alph (resH L)) (resN_pos L φ) (alph_pos _))
    (resFormulas hh φ h3) (compactBudget (alph (resH L)))

theorem resStarData_valid {L : Nat} (h : 256 ≤ mOf L) (hh : 0 < resH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (resStarData hh φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (resN L φ) (alph (resH L)) (resN_pos L φ) (alph_pos _))
    (resFormulas hh φ h3) (compactBudget (alph (resH L)))
    (compactWeights_pos (resN_pos L φ) (alph_pos _))
    (compactWeights_sum (resN_pos L φ) (alph_pos _)) hM ?_
    (compactBudget_pos (alph_pos _)) (compactBudget_le_one (alph_pos _))
  intro i
  have hle := compactLeaves_le h
  have hA : alph (resH L) = ROf L := alph_eq_ROf L
  have hleaves : alph (resH L) * (paramM L + 1) ≤ L := by
    simpa [hA, paramM, Nat.mul_comm] using hle
  simpa [resFormulas, resFormula_leaves] using hleaves

private theorem resStar_len {L : Nat} (hh : 0 < resH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (resStarData hh φ h3 hM).weights.length =
      resN L φ * alph (resH L) := by
  simp [resStarData, indexedData]

private theorem res_honest_eval {L : Nat} (hh : 0 < resH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (resH L)))
      (resFormula hh φ h3 i) = true := by
  refine (eval_compileRes (resK_le hh)
      (honest (n := resN L φ) (alph_pos (resH L)))
      (resCenter φ h3 i) (resLeaf L φ)).mpr
    ⟨⟨0, alph_pos (resH L)⟩, ?_, ?_⟩
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (resH L) + (0 : Nat)) %
          alph (resH L) = 0) = true
    have hmod :
        ((resCenter (L := L) φ h3 i).val * alph (resH L)) %
          alph (resH L) = 0 :=
      Nat.mul_mod_left _ _
    simpa [hmod]
  · intro j
    have h0 :
        restrictLow (resK_le hh)
          (⟨0, alph_pos (resH L)⟩ : Fin (alph (resH L))) =
        ⟨0, alph_pos (resH L)⟩ :=
      restrictLow_zero (resK_le hh)
    change decide
        (((resLeaf L φ j).val * alph (resH L) +
          (restrictLow (resK_le hh)
            (⟨0, alph_pos (resH L)⟩ : Fin (alph (resH L)))).val) %
          alph (resH L) = 0) = true
    simp [h0, Nat.mul_mod_left]

private theorem honest_weight {n A : Nat} (hn : 0 < n) (hA : 0 < A) :
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
    have hval : (finProdFinEquiv (v, a)).val = a.val + A * v.val := rfl
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

private theorem res_honest_cost {L : Nat} (hh : 0 < resH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (resStarData hh φ h3 hM).cost
      (fun i => honest (n := resN L φ) (alph_pos (resH L)) ⟨i.val,
        (resStar_len hh φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph (resH L)) := by
  have hlen := resStar_len hh φ h3 hM
  unfold Data.cost Data.coordinateWeights
  simp only [resStarData, indexedData, List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (resN L φ) (alph (resH L))
        (resN_pos L φ) (alph_pos (resH L)))).length ≃
      Fin (resN L φ * alph (resH L)) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := honest_weight (resN_pos L φ) (alph_pos (resH L))
  unfold weight compactWeights honest at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights, honest]

private theorem res_honest_sat {L : Nat} (hh : 0 < resH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (resStarData hh φ h3 hM).satisfaction
      (fun i => honest (n := resN L φ) (alph_pos (resH L)) ⟨i.val,
        (resStar_len hh φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (resStarData hh φ h3 hM).formulas.length) := by
    simp [resStarData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (resStarData hh φ h3 hM).formulas.length,
      Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (resH L)) ⟨i.val,
          (resStar_len hh φ h3 hM) ▸ i.isLt⟩)
        ((resStarData hh φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [resStarData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (resH L)) (resN_pos L φ) (alph_pos _))
      (resFormulas hh φ h3) (compactBudget (alph (resH L)))
      (fun i => honest (n := resN L φ) (alph_pos (resH L)) ⟨i.val, by
        simpa [resStarData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [resStarData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [resStarData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (resFormulas hh φ h3 ⟨j.val, hj⟩)) ?_).trans
      (res_honest_eval hh φ h3 ⟨j.val, hj⟩)
    funext v
    exact congrArg (honest (n := resN L φ) (alph_pos (resH L)))
      (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (resH L)) ⟨i.val,
          (resStar_len hh φ h3 hM) ▸ i.isLt⟩)
        ((resStarData hh φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem resStarData_yes {L : Nat} (h : 256 ≤ mOf L) (hh : 0 < resH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Yes 0 (ofData (resStarData hh φ h3 hM)
      (resStarData_valid h hh φ h3 hM)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := resN L φ) (alph_pos (resH L)) ⟨i.val,
      (resStar_len hh φ h3 hM) ▸ i.isLt⟩, ?_, ?_⟩
  · have hcost := res_honest_cost hh φ h3 hM
    have hle : compactBudget (alph (resH L)) ≤
        (resStarData hh φ h3 hM).budget := by
      simp [resStarData, indexedData]
    exact hcost.trans_le hle
  · have hsat := res_honest_sat hh φ h3 hM
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

theorem resStarData_not_no {L : Nat} (h : 256 ≤ mOf L) (hh : 0 < resH L)
    (hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (resStarData hh φ h3 hM)
        (resStarData_valid h hh φ h3 hM)) := by
  dsimp [No]
  rw [ofData_data]
  intro hall
  have hY := resStarData_yes h hh φ h3 hM
  dsimp [Yes] at hY
  rw [ofData_data] at hY
  obtain ⟨y, hcost, hsat⟩ := hY
  have hbud : (0 : Rat) < (resStarData hh φ h3 hM).budget :=
    compactBudget_pos (alph_pos (resH L))
  have hσQ : (1 : Rat) ≤ (rofSigma L : Rat) := Nat.one_le_cast.mpr hσ
  have hscale : (resStarData hh φ h3 hM).budget ≤
      (rofSigma L : Rat) * (resStarData hh φ h3 hM).budget :=
    le_mul_of_one_le_left (le_of_lt hbud) hσQ
  have hcost' : (resStarData hh φ h3 hM).cost y ≤
      (rofSigma L : Rat) * (resStarData hh φ h3 hM).budget :=
    le_trans hcost hscale
  have hsat1 : (1 : Rat) ≤ (resStarData hh φ h3 hM).satisfaction y := by
    simpa using hsat
  have h1lt : (1 : Rat) < gammaL L :=
    lt_of_le_of_lt hsat1 (hall y hcost')
  exact (lt_irrefl (1 : Rat) (h1lt.trans hγ1))

theorem resStarData_yes_mem {L : Nat} (h : 256 ≤ mOf L) (hh : 0 < resH L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    encodeData (resStarData hh φ h3 hM) (resStarData_valid h hh φ h3 hM) ∈
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1).yesInstances :=
  cmmsaPromise_yes_of_encode hσ hγ0 hγ1
    (ofData (resStarData hh φ h3 hM) (resStarData_valid h hh φ h3 hM))
    (resStarData_yes h hh φ h3 hM)

theorem res_proj_ne_id {L : Nat} (hh : 0 < resH L) :
    restrictLow (resK_le hh)
        ⟨2 ^ resK, two_pow_lt_two_pow (resK_lt hh)⟩ ≠
      ⟨2 ^ resK, two_pow_lt_two_pow (resK_lt hh)⟩ :=
  restrictLow_ne_id (resK_lt hh)

end
end PvNP.RealizableHardness.ActualThreeSatGrassmannRes
