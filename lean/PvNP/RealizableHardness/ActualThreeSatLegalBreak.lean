import PvNP.RealizableHardness.ActualThreeSatLegalRes
import PvNP.RealizableHardness.ActualThreeSatClauseOrFp

/-!
Low-bit `legal3Lin`-filtered m-ary Grassmann stars (`e0+e1+e2`), `k = 2h-1`.

This is the LegalRes packing with DualStar `legal3Lin` (coordinates `0,1,2`)
instead of the high-bit window `(h,h+1,h+2)`.  Label `2^h` has low-bit
parity `0` once `2 < h`, so the LegalRes `{0, 2^h}` two-cover does **not**
satisfy an RHS-1 formula.  Sat unit remains `Yes 0` via the label-0 1-hot.

The `{0,1}` two-label assignment still covers mixed RHS (label `1` is
`legal3Lin` RHS `1`), so this is not `No σ_L γ_L` and does not inhabit
`hSrcCmmsa`.  Not `if-sat`.  Checking-transducer `mem_FP` is not rebuilt.

The FP encoder writes a constant low-bit RHS-0 star plus `clauseOrEnc`, so
3SAT data is in the tree.
-/
namespace PvNP.RealizableHardness.ActualThreeSatLegalBreak

open Complexity hiding Data
open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualRestrictCompile
open ActualGrassmannDualStar
open ActualVecLabel
open ActualThreeSatGrassmannRes
open ActualThreeSatLegalRes
open ActualThreeSatCmmsaReduce
open ActualThreeSatStarFamily
open ActualThreeSatClauseOrFp
open ActualCMMSARandomizedReduction
open CMMSACodec hiding Tree
open CMMSAEncoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

theorem two_lt_h_to_one_lt' {h : Nat} (hh : 2 < h) : 1 < h :=
  two_lt_h_to_one_lt hh

theorem legal3Lin_zero {h : Nat} (hh : 2 < h) :
    legal3Lin (two_lt_h_to_one_lt' hh) ⟨0, alph_pos h⟩ 0 := by
  simp [legal3Lin, evalBit, vecOfFin_zero]

theorem legal3Lin_zero_not_one {h : Nat} (hh : 2 < h) :
    ¬ legal3Lin (two_lt_h_to_one_lt' hh) ⟨0, alph_pos h⟩ 1 := by
  intro hleg
  exact zero_ne_one ((legal3Lin_zero hh).symm.trans hleg)

theorem one_lt_alph_of {h : Nat} (hh : 0 < h) : 1 < alph h :=
  Nat.one_lt_two_pow (Nat.mul_pos (by decide : 0 < 2) hh).ne'

def lowOne {h : Nat} (hh : 0 < h) : Fin (alph h) :=
  ⟨1, one_lt_alph_of hh⟩

theorem legal3Lin_one {h : Nat} (hh : 2 < h) :
    legal3Lin (two_lt_h_to_one_lt' hh) (lowOne (two_lt_h_to_pos hh)) 1 := by
  unfold legal3Lin evalBit vecOfFin bit lowOne basis3
  have t0 : (1 : Nat).testBit 0 = true := rfl
  have t1 : (1 : Nat).testBit 1 = false := rfl
  have t2 : (1 : Nat).testBit 2 = false := rfl
  simp [t0, t1, t2]

theorem legal3Lin_highBit_not_one {h : Nat} (hh : 2 < h) :
    ¬ legal3Lin (two_lt_h_to_one_lt' hh)
      (highBit (two_lt_h_to_pos hh)) 1 := by
  intro hleg
  have t0 : (2 ^ h).testBit 0 = false :=
    pow_h_testBit_ne (by omega : (0 : Nat) ≠ h)
  have t1 : (2 ^ h).testBit 1 = false :=
    pow_h_testBit_ne (by omega : (1 : Nat) ≠ h)
  have t2 : (2 ^ h).testBit 2 = false :=
    pow_h_testBit_ne (by omega : (2 : Nat) ≠ h)
  have hz : legal3Lin (two_lt_h_to_one_lt' hh)
      (highBit (two_lt_h_to_pos hh)) 0 := by
    unfold legal3Lin evalBit vecOfFin bit highBit basis3
    simp [t0, t1, t2]
  exact legal3Lin_not_both (two_lt_h_to_one_lt' hh)
    (highBit (two_lt_h_to_pos hh)) ⟨hz, hleg⟩

theorem legal3Lin_exists {h : Nat} (hh : 2 < h) (rhs : ZMod 2) :
    ∃ b : Fin (alph h), legal3Lin (two_lt_h_to_one_lt' hh) b rhs := by
  rcases zmod2_eq_zero_or_one rhs with h0 | h1
  · subst h0
    exact ⟨⟨0, alph_pos h⟩, legal3Lin_zero hh⟩
  · subst h1
    exact ⟨lowOne (two_lt_h_to_pos hh), legal3Lin_one hh⟩

def isLegal3 {h : Nat} (hh : 2 < h) (rhs : ZMod 2) (b : Fin (alph h)) : Bool :=
  decide (legal3Lin (two_lt_h_to_one_lt' hh) b rhs)

theorem isLegal3_true_iff {h : Nat} (hh : 2 < h) (rhs : ZMod 2)
    (b : Fin (alph h)) :
    isLegal3 hh rhs b = true ↔
      legal3Lin (two_lt_h_to_one_lt' hh) b rhs :=
  decide_eq_true_iff

theorem legal3Lin_exists_bool {h : Nat} (hh : 2 < h) (rhs : ZMod 2) :
    ∃ b : Fin (alph h), isLegal3 hh rhs b = true := by
  obtain ⟨b, hb⟩ := legal3Lin_exists hh rhs
  exact ⟨b, (isLegal3_true_iff hh rhs b).mpr hb⟩

def compileLow {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  Option.get
    (orFilter (alph h) (fun b => isLegal3 hh rhs b)
      (fun b => branchRes hk c leaf b))
    (orFilter_isSome (fun b => isLegal3 hh rhs b)
      (fun b => branchRes hk c leaf b) (legal3Lin_exists_bool hh rhs))

theorem compileLow_orFilter {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    orFilter (alph h) (fun b => isLegal3 hh rhs b)
        (fun b => branchRes hk c leaf b) =
      some (compileLow hh hk c leaf rhs) :=
  (Option.some_get (orFilter_isSome (fun b => isLegal3 hh rhs b)
    (fun b => branchRes hk c leaf b) (legal3Lin_exists_bool hh rhs))).symm

theorem compileLow_leaves_le {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula.leaves (compileLow hh hk c leaf rhs) ≤ alph h * (m + 1) := by
  have hsome := compileLow_orFilter hh hk c leaf rhs
  have hle := orFilter_leaves_le (alph h) (fun b => isLegal3 hh rhs b)
    (fun b => branchRes hk c leaf b) (compileLow hh hk c leaf rhs) hsome
  have hb : ∀ b, Formula.leaves (branchRes hk c leaf b) = m + 1 :=
    fun b => branchRes_leaves hk c leaf b
  have hsum : (∑ b : Fin (alph h), Formula.leaves (branchRes hk c leaf b)) =
      alph h * (m + 1) := by
    rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
    simp [Finset.card_univ, Fintype.card_fin]
  exact hle.trans (le_of_eq hsum)

theorem eval_compileLow {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileLow hh hk c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legal3Lin (two_lt_h_to_one_lt' hh) b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          ∀ i : Fin m,
            Z ⟨(leaf i).val * alph h + (restrictLow hk b).val,
              coord_lt (leaf i) (restrictLow hk b) (alph_pos h)⟩ = true := by
  have hor := eval_orFilter Z (alph h) (fun b => isLegal3 hh rhs b)
    (fun b => branchRes hk c leaf b) (compileLow hh hk c leaf rhs)
    (compileLow_orFilter hh hk c leaf rhs)
  have hand (b : Fin (alph h)) :=
    eval_andFin Z (m + 1) (slotVarRes hk c leaf b) (branchRes hk c leaf b)
      (branchRes_andFin hk c leaf b)
  constructor
  · intro hf
    obtain ⟨b, hp, hb⟩ := hor.mp hf
    have hall := (hand b).mp hb
    refine ⟨b, (isLegal3_true_iff hh rhs b).mp hp, ?_, ?_⟩
    · simpa [slotVarRes, varAt, Formula.eval] using hall 0
    · intro i
      simpa [slotVarRes, varAt, Formula.eval] using hall i.succ
  · rintro ⟨b, hleg, hc, hleaf⟩
    refine hor.mpr ⟨b, (isLegal3_true_iff hh rhs b).mpr hleg, (hand b).mpr ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa [slotVarRes, varAt, Formula.eval] using hc
    | succ i => simpa [slotVarRes, varAt, Formula.eval] using hleaf i

def lowFormula {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Formula (Fin (resN L φ * alph (legalH L))) :=
  compileLow hh (legalK_le (legalH_pos_of hh))
    (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

theorem lowFormula_leaves_le {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.leaves (lowFormula hh φ h3 i) ≤
      alph (legalH L) * (paramM L + 1) := by
  simpa [lowFormula, paramM] using
    compileLow_leaves_le hh (legalK_le (legalH_pos_of hh))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

def lowFormulas {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (resN L φ * alph (legalH L))) :=
  fun i => lowFormula hh φ h3 i

def lowResData {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (lowFormulas hh φ h3) (compactBudget (alph (legalH L)))

theorem lowResData_valid {L : Nat} (h : 256 ≤ mOf L) (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (lowResData hh φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (lowFormulas hh φ h3) (compactBudget (alph (legalH L)))
    (compactWeights_pos (resN_pos L φ) (alph_pos _))
    (compactWeights_sum (resN_pos L φ) (alph_pos _)) hM ?_
    (compactBudget_pos (alph_pos _)) (compactBudget_le_one (alph_pos _))
  intro i
  have hle := compactLeaves_le h
  have hA : alph (legalH L) = ROf L := alph_eq_ROf L
  have hleaves : alph (legalH L) * (paramM L + 1) ≤ L := by
    simpa [hA, paramM, Nat.mul_comm] using hle
  exact (lowFormula_leaves_le hh φ h3 i).trans hleaves

private theorem lowRes_len {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (lowResData hh φ h3 hM).weights.length =
      resN L φ * alph (legalH L) := by
  simp [lowResData, indexedData]

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

private theorem honest_eval_low {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (lowFormula hh φ h3 i) = true := by
  refine (eval_compileLow hh (legalK_le (legalH_pos_of hh))
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_⟩
  · simpa [h0] using legal3Lin_zero hh
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (legalH L) + (0 : Nat)) %
          alph (legalH L) = 0) = true
    simpa [Nat.mul_mod_left]
  · intro j
    have hrest := restrictLow_zero (legalK_le (legalH_pos_of hh))
    change decide
        (((resLeaf L φ j).val * alph (legalH L) +
          (restrictLow (legalK_le (legalH_pos_of hh))
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]

/-- LegalRes `{0, 2^h}` two-cover fails an RHS-1 low-bit formula. -/
theorem twoCover_not_eval_rhs1 {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (twoCover (n := resN L φ) (legalH_pos_of hh))
      (lowFormula hh φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileLow hh (legalK_le (legalH_pos_of hh))
      (twoCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [lowFormula] using htrue)
  obtain ⟨b, hleg, hc, _⟩ := he
  have hc' := twoCover_coord (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) b
  have hlit : b.val = 0 ∨ b.val = 2 ^ legalH L := of_decide_eq_true (by
    simpa [hc'] using hc)
  have hleg1 : legal3Lin (two_lt_h_to_one_lt' hh) b 1 := by
    simpa [h1] using hleg
  rcases hlit with hb0 | hbh
  · have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
    exact legal3Lin_zero_not_one hh (by simpa [hb] using hleg1)
  · have hb : b = highBit (legalH_pos_of hh) := Fin.ext (by
      simpa [highBit] using hbh)
    exact legal3Lin_highBit_not_one hh (by simpa [hb] using hleg1)

theorem twoCover_not_eval_unsatCnf {L : Nat} (hh : 2 < legalH L) :
    Formula.eval
      (twoCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (lowFormula hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩) = false :=
  twoCover_not_eval_rhs1 hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩ unsatCnf_rhs1

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

private theorem low_honest_cost {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (lowResData hh φ h3 hM).cost
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (lowRes_len hh φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph (legalH L)) := by
  unfold Data.cost Data.coordinateWeights
  simp only [lowResData, indexedData, List.get_ofFn]
  let e : Fin (List.ofFn
      (compactWeights (resN L φ) (alph (legalH L))
        (resN_pos L φ) (alph_pos (legalH L)))).length ≃
      Fin (resN L φ * alph (legalH L)) :=
    (Fin.castOrderIso (by simp)).toEquiv
  have hsum := honest_weight (resN_pos L φ) (alph_pos (legalH L))
  unfold weight compactWeights honest at hsum
  refine Eq.trans ?_ hsum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  have hval : (e i).val = i.val := by simp [e, Fin.castOrderIso]
  simp [hval, compactWeights, honest]

private theorem low_honest_sat_of_rhs0 {L : Nat} (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hall0 : ∀ i : Fin φ.length, clauseRhs φ h3 i = 0) :
    (lowResData hh φ h3 hM).satisfaction
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (lowRes_len hh φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (lowResData hh φ h3 hM).formulas.length) := by
    simp [lowResData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (lowResData hh φ h3 hM).formulas.length,
      Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (lowRes_len hh φ h3 hM) ▸ i.isLt⟩)
        ((lowResData hh φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [lowResData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
      (lowFormulas hh φ h3) (compactBudget (alph (legalH L)))
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val, by
        simpa [lowResData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [lowResData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [lowResData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (lowFormulas hh φ h3 ⟨j.val, hj⟩)) ?_).trans
      (honest_eval_low hh φ h3 ⟨j.val, hj⟩ (hall0 ⟨j.val, hj⟩))
    funext v
    exact congrArg (honest (n := resN L φ) (alph_pos (legalH L)))
      (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (lowRes_len hh φ h3 hM) ▸ i.isLt⟩)
        ((lowResData hh φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem lowResData_yes_unit3 {L : Nat} (h : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Yes 0 (ofData (lowResData hh unit3 unit3_is3 unit3_len)
      (lowResData_valid h hh unit3 unit3_is3 unit3_len)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := resN L unit3) (alph_pos (legalH L)) ⟨i.val,
      (lowRes_len hh unit3 unit3_is3 unit3_len) ▸ i.isLt⟩, ?_, ?_⟩
  · have hcost := low_honest_cost hh unit3 unit3_is3 unit3_len
    have hle : compactBudget (alph (legalH L)) ≤
        (lowResData hh unit3 unit3_is3 unit3_len).budget := by
      simp [lowResData, indexedData]
    exact hcost.trans_le hle
  · have hsat := low_honest_sat_of_rhs0 hh unit3 unit3_is3 unit3_len
      unit3_all_rhs0
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

/-- Constant low-bit RHS-0 star plus clause-0 3-OR. 3SAT data in the tree. -/
def lowWeightRat (L : Nat) : Rat :=
  (1 : Rat) / ((paramN L * ROf L : Nat) : Rat)

def lowBudgetRat (L : Nat) : Rat :=
  (1 : Rat) / (ROf L : Rat)

def lowWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L) (ratTree (lowWeightRat L))))

def lowBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree (lowBudgetRat L))

def lowFormulaTree {L : Nat} (hh : 2 < legalH L) : CMMSACodec.Tree :=
  formulaTree
    (compileLow hh (legalK_le (legalH_pos_of hh))
      (paramCenter L) (paramLeaf L) 0)

def lowFormulaEnc {L : Nat} (hh : 2 < legalH L) : List Bool :=
  CMMSACodec.Tree.encode (lowFormulaTree hh)

def lowFormsEnc {L : Nat} (hh : 2 < legalH L) (z : List Bool) : List Bool :=
  true :: lowFormulaEnc hh ++ (true :: clauseOrEnc z ++ [false])

theorem lowFormsEnc_mem_FP {L : Nat} (hh : 2 < legalH L) :
    lowFormsEnc (L := L) hh ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: lowFormulaEnc hh)) htail

def lowEncFn {L : Nat} (hh : 2 < legalH L) (z : List Bool) : List Bool :=
  true :: lowWeightsEnc L ++ true :: lowFormsEnc hh z ++ lowBudgetEnc L

theorem lowEncFn_mem_FP {L : Nat} (hh : 2 < legalH L) :
    lowEncFn (L := L) hh ∈ Complexity.FP := by
  have hforms : (fun z => true :: lowFormsEnc hh z) ∈ Complexity.FP :=
    mem_FP_comp (lowFormsEnc_mem_FP hh) (Cobham.cons_mem_FP true)
  have hleft : (fun z => true :: lowWeightsEnc L ++ true :: lowFormsEnc hh z) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: lowWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (lowBudgetEnc L))

theorem lowEncFn_ne_id {L : Nat} (hh : 2 < legalH L) :
    lowEncFn (L := L) hh [] ≠ [] := by
  simp [lowEncFn, lowWeightsEnc, CMMSACodec.Tree.encode]

end
end PvNP.RealizableHardness.ActualThreeSatLegalBreak
