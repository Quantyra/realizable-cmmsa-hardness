import PvNP.RealizableHardness.ActualThreeSatDualWindow

/-!
Half-width DualWindow: `compileBoth` at restriction `k = h` instead of
`k = 2h-1`.  `restrictLow` at width `h` sends DualWindow's leftover
`dualBit = 1+2^h` to `1`, which dualCover does not light, so `{0, 1+2^h}`
fails RHS-1 once dummy leaves exist (`256 ≤ mOf L`).

Any spatially constant 2-label palette fails mixed RHS: a 1-legal center
is not a `k = h` fixed point, and its restriction keeps the low 3XOR so
it cannot be 0-legal.  Sat unit remains `Yes 0` via label `0`.

The 3-label palette `{0, 1, 1+2^h}` still satisfies mixed RHS, so this is
not `No σ_L γ_L` and does not inhabit `hSrcCmmsa`.  Not `if-sat`.
Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatHalfWidth

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
open ActualThreeSatLegalBreak
open ActualThreeSatDualWindow
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

def midK (h : Nat) : Nat := h

theorem midK_le {h : Nat} (hh : 0 < h) : midK h ≤ 2 * h :=
  Nat.le_mul_of_pos_left h (by decide : 0 < 2)

theorem midK_lt {h : Nat} (hh : 0 < h) : midK h < 2 * h := by
  unfold midK
  have : h < h + h := Nat.lt_add_of_pos_right hh
  simpa [two_mul] using this

theorem midK_proj_ne_id {h : Nat} (hh : 0 < h) :
    restrictLow (midK_le hh)
        ⟨2 ^ midK h, two_pow_lt_two_pow (midK_lt hh)⟩ ≠
      ⟨2 ^ midK h, two_pow_lt_two_pow (midK_lt hh)⟩ :=
  restrictLow_ne_id (midK_lt hh)

theorem paramM_pos_of {L : Nat} (h : 256 ≤ mOf L) : 0 < paramM L :=
  lt_of_lt_of_le (by decide : 0 < 256) (by simpa [paramM] using h)

theorem legalBoth_not_both {h : Nat} (hh : 2 < h) (a : Fin (alph h)) :
    ¬ (legalBoth hh a 0 ∧ legalBoth hh a 1) := by
  intro ⟨h0, h1⟩
  exact legal3Lin_not_both (two_lt_h_to_one_lt hh) a ⟨h0.1, h1.1⟩

theorem legal3Lin_restrictLow_mid {h : Nat} (hh : 2 < h)
    (a : Fin (alph h)) (rhs : ZMod 2) :
    legal3Lin (two_lt_h_to_one_lt hh)
        (restrictLow (midK_le (two_lt_h_to_pos hh)) a) rhs ↔
      legal3Lin (two_lt_h_to_one_lt hh) a rhs := by
  unfold legal3Lin
  have h0 := evalBit_restrictLow (midK_le (two_lt_h_to_pos hh)) a
    (basis3 (two_lt_h_to_one_lt hh) 0)
    (Nat.lt_trans (by decide : (0 : Nat) < 2) hh)
  have h1 := evalBit_restrictLow (midK_le (two_lt_h_to_pos hh)) a
    (basis3 (two_lt_h_to_one_lt hh) 1)
    (Nat.lt_trans (by decide : (1 : Nat) < 2) hh)
  have h2 := evalBit_restrictLow (midK_le (two_lt_h_to_pos hh)) a
    (basis3 (two_lt_h_to_one_lt hh) 2) hh
  simp [h0, h1, h2]

theorem legalHigh_restrictLow_mid_zero {h : Nat} (hh : 2 < h)
    (a : Fin (alph h)) :
    legalHigh hh (restrictLow (midK_le (two_lt_h_to_pos hh)) a) 0 := by
  unfold legalHigh evalBit vecOfFin bit restrictLow highBasis3
  simp [midK]

theorem restrictLow_ne_of_legalHigh_one {h : Nat} (hh : 2 < h)
    (a : Fin (alph h)) (hleg : legalHigh hh a 1) :
    restrictLow (midK_le (two_lt_h_to_pos hh)) a ≠ a := by
  intro heq
  have hz := legalHigh_restrictLow_mid_zero hh a
  rw [heq] at hz
  exact legalHigh_not_both hh a ⟨hz, hleg⟩

theorem restrictLow_dualBit_eq_one {h : Nat} (hh : 2 < h) :
    restrictLow (midK_le (two_lt_h_to_pos hh))
        (dualBit (two_lt_h_to_pos hh)) =
      lowOne (two_lt_h_to_pos hh) := by
  apply Fin.ext
  have hlt : 1 < 2 ^ h := Nat.one_lt_two_pow (two_lt_h_to_pos hh).ne'
  have hmod : (1 + 2 ^ h) % 2 ^ h = 1 := by
    rw [Nat.add_comm, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
  rw [restrictLow_val]
  convert hmod
  · rfl
  · rfl
  · rfl

def compileMid {n h m : Nat} (hh : 2 < h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  compileBoth hh (midK_le (two_lt_h_to_pos hh)) c leaf rhs

theorem eval_compileMid {n h m : Nat} (hh : 2 < h)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileMid hh c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legalBoth hh b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          ∀ i : Fin m,
            Z ⟨(leaf i).val * alph h +
                (restrictLow (midK_le (two_lt_h_to_pos hh)) b).val,
              coord_lt (leaf i)
                (restrictLow (midK_le (two_lt_h_to_pos hh)) b)
                (alph_pos h)⟩ = true :=
  eval_compileBoth hh (midK_le (two_lt_h_to_pos hh)) Z c leaf rhs

def midFormula {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Formula (Fin (resN L φ * alph (legalH L))) :=
  compileMid hh (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

theorem compileMid_leaves_le {n h m : Nat} (hh : 2 < h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula.leaves (compileMid hh c leaf rhs) ≤ alph h * (m + 1) := by
  have hsome := compileBoth_orFilter hh (midK_le (two_lt_h_to_pos hh))
    c leaf rhs
  have hle := orFilter_leaves_le (alph h) (fun b => isLegalBoth hh rhs b)
    (fun b => branchRes (midK_le (two_lt_h_to_pos hh)) c leaf b)
    (compileMid hh c leaf rhs) (by simpa [compileMid] using hsome)
  have hb : ∀ b, Formula.leaves
      (branchRes (midK_le (two_lt_h_to_pos hh)) c leaf b) = m + 1 :=
    fun b => branchRes_leaves (midK_le (two_lt_h_to_pos hh)) c leaf b
  have hsum :
      (∑ b : Fin (alph h), Formula.leaves
        (branchRes (midK_le (two_lt_h_to_pos hh)) c leaf b)) =
      alph h * (m + 1) := by
    rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
    simp [Finset.card_univ, Fintype.card_fin]
  exact hle.trans (le_of_eq hsum)

theorem midFormula_leaves_le {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.leaves (midFormula hh φ h3 i) ≤
      alph (legalH L) * (paramM L + 1) := by
  simpa [midFormula, compileMid, paramM] using
    compileMid_leaves_le hh (resCenter φ h3 i) (resLeaf L φ)
      (clauseRhs φ h3 i)

def midFormulas {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (resN L φ * alph (legalH L))) :=
  fun i => midFormula hh φ h3 i

def midResData {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (midFormulas hh φ h3) (compactBudget (alph (legalH L)))

theorem midResData_valid {L : Nat} (h : 256 ≤ mOf L) (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (midResData hh φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (midFormulas hh φ h3) (compactBudget (alph (legalH L)))
    (compactWeights_pos (resN_pos L φ) (alph_pos _))
    (compactWeights_sum (resN_pos L φ) (alph_pos _)) hM ?_
    (compactBudget_pos (alph_pos _)) (compactBudget_le_one (alph_pos _))
  intro i
  have hle := compactLeaves_le h
  have hA : alph (legalH L) = ROf L := alph_eq_ROf L
  have hleaves : alph (legalH L) * (paramM L + 1) ≤ L := by
    simpa [hA, paramM, Nat.mul_comm] using hle
  exact (midFormula_leaves_le hh φ h3 i).trans hleaves

private theorem midRes_len {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (midResData hh φ h3 hM).weights.length =
      resN L φ * alph (legalH L) := by
  simp [midResData, indexedData]

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

def dualCover {n h : Nat} (hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i =>
    decide (i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h)

theorem dualCover_coord {n h : Nat} (hh : 0 < h) (v : Fin n)
    (a : Fin (alph h)) :
    dualCover (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 + 2 ^ h) := by
  unfold dualCover
  have hmod := coord_mod (alph_pos h) v a
  simp [hmod]

theorem dualCover_not_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (dualCover (n := resN L φ) (legalH_pos_of hh))
      (midFormula hh φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileMid hh
      (dualCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [midFormula, compileMid] using htrue)
  obtain ⟨b, hleg, hc, hleaf⟩ := he
  have hc' := dualCover_coord (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) b
  have hlit : b.val = 0 ∨ b.val = 1 + 2 ^ legalH L := of_decide_eq_true (by
    simpa [hc'] using hc)
  have hleg1 : legalBoth hh b 1 := by simpa [h1] using hleg
  rcases hlit with hb0 | hbd
  · have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
    exact legal3Lin_zero_not_one hh (by simpa [hb] using hleg1.1)
  · have hb : b = dualBit (legalH_pos_of hh) := Fin.ext (by
      simpa [dualBit] using hbd)
    let j : Fin (paramM L) := ⟨0, paramM_pos_of hm⟩
    have hleaf0 := hleaf j
    have hrest : restrictLow (midK_le (legalH_pos_of hh)) b =
        lowOne (legalH_pos_of hh) := by
      simpa [hb] using restrictLow_dualBit_eq_one hh
    have hcL := dualCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ j)
      (restrictLow (midK_le (legalH_pos_of hh)) b)
    have hlitL : (restrictLow (midK_le (legalH_pos_of hh)) b).val = 0 ∨
        (restrictLow (midK_le (legalH_pos_of hh)) b).val =
          1 + 2 ^ legalH L := of_decide_eq_true (by
      simpa [hcL] using hleaf0)
    have hv : (restrictLow (midK_le (legalH_pos_of hh)) b).val = 1 := by
      simpa [lowOne] using congrArg Fin.val hrest
    rcases hlitL with hz | hd
    · exact (by decide : ¬ (1 : Nat) = 0) (hv.symm.trans hz)
    · have hne : (1 : Nat) ≠ 1 + 2 ^ legalH L := by
        have : 0 < 2 ^ legalH L := Nat.two_pow_pos _
        omega
      exact hne (hv.symm.trans hd)

theorem dualCover_not_eval_unsatCnf {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Formula.eval
      (dualCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (midFormula hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩) = false :=
  dualCover_not_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩
    unsatCnf_rhs1

def globalPalette {n h : Nat} (S : Finset (Fin (alph h))) :
    Fin (n * alph h) → Bool :=
  fun i => decide (⟨i.val % alph h, Nat.mod_lt _ (alph_pos h)⟩ ∈ S)

theorem globalPalette_coord {n h : Nat} (S : Finset (Fin (alph h)))
    (v : Fin n) (a : Fin (alph h)) :
    globalPalette (n := n) S
        ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a ∈ S) := by
  unfold globalPalette
  have hmod := coord_mod (alph_pos h) v a
  simp [hmod]

theorem twoHot_not_both_rhs {n h m : Nat} (hh : 2 < h)
    (hm : 0 < m) (S : Finset (Fin (alph h))) (hcard : S.card ≤ 2)
    (c0 c1 : Fin n) (leaf : Fin m → Fin n)
    (h0 : Formula.eval (globalPalette (n := n) S)
      (compileMid hh c0 leaf 0) = true)
    (h1 : Formula.eval (globalPalette (n := n) S)
      (compileMid hh c1 leaf 1) = true) :
    False := by
  have he0 := (eval_compileMid hh (globalPalette (n := n) S) c0 leaf 0).mp h0
  have he1 := (eval_compileMid hh (globalPalette (n := n) S) c1 leaf 1).mp h1
  obtain ⟨b0, hleg0, hc0, hleaf0⟩ := he0
  obtain ⟨b1, hleg1, hc1, hleaf1⟩ := he1
  have hb0S : b0 ∈ S := of_decide_eq_true (by
    simpa [globalPalette_coord S c0 b0] using hc0)
  have hb1S : b1 ∈ S := of_decide_eq_true (by
    simpa [globalPalette_coord S c1 b1] using hc1)
  let j : Fin m := ⟨0, hm⟩
  have hr0S : restrictLow (midK_le (two_lt_h_to_pos hh)) b0 ∈ S :=
    of_decide_eq_true (by
      simpa [globalPalette_coord S (leaf j)
        (restrictLow (midK_le (two_lt_h_to_pos hh)) b0)] using hleaf0 j)
  have hr1S : restrictLow (midK_le (two_lt_h_to_pos hh)) b1 ∈ S :=
    of_decide_eq_true (by
      simpa [globalPalette_coord S (leaf j)
        (restrictLow (midK_le (two_lt_h_to_pos hh)) b1)] using hleaf1 j)
  have hne : restrictLow (midK_le (two_lt_h_to_pos hh)) b1 ≠ b1 :=
    restrictLow_ne_of_legalHigh_one hh b1 hleg1.2
  have hpair : ({b1, restrictLow (midK_le (two_lt_h_to_pos hh)) b1} :
      Finset (Fin (alph h))) ⊆ S := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hb1S
    · exact hr1S
  have hpair2 :
      ({b1, restrictLow (midK_le (two_lt_h_to_pos hh)) b1} :
        Finset (Fin (alph h))).card = 2 :=
    Finset.card_insert_of_notMem (Finset.notMem_singleton.2 hne.symm)
  have hEq : ({b1, restrictLow (midK_le (two_lt_h_to_pos hh)) b1} :
      Finset (Fin (alph h))) = S :=
    Finset.eq_of_subset_of_card_le hpair (hcard.trans_eq hpair2.symm)
  have hb0pair : b0 ∈
      ({b1, restrictLow (midK_le (two_lt_h_to_pos hh)) b1} :
        Finset (Fin (alph h))) := by
    simpa [hEq] using hb0S
  have hb0ne : b0 ≠ b1 := by
    intro hbe
    exact legalBoth_not_both hh b0 ⟨hleg0, by simpa [hbe] using hleg1⟩
  have hb0r : b0 = restrictLow (midK_le (two_lt_h_to_pos hh)) b1 := by
    simp [hb0ne] at hb0pair
    exact hb0pair
  have hlin0 : legal3Lin (two_lt_h_to_one_lt hh) b0 0 := hleg0.1
  have hlin1 : legal3Lin (two_lt_h_to_one_lt hh)
      (restrictLow (midK_le (two_lt_h_to_pos hh)) b1) 1 :=
    (legal3Lin_restrictLow_mid hh b1 1).mpr hleg1.1
  have hlin0' : legal3Lin (two_lt_h_to_one_lt hh)
      (restrictLow (midK_le (two_lt_h_to_pos hh)) b1) 0 := by
    simpa [hb0r] using hlin0
  exact legal3Lin_not_both (two_lt_h_to_one_lt hh)
    (restrictLow (midK_le (two_lt_h_to_pos hh)) b1) ⟨hlin0', hlin1⟩

def threeCover {n h : Nat} (hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i =>
    decide (i.val % alph h = 0 ∨ i.val % alph h = 1 ∨
      i.val % alph h = 1 + 2 ^ h)

theorem threeCover_coord {n h : Nat} (hh : 0 < h) (v : Fin n)
    (a : Fin (alph h)) :
    threeCover (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 ∨ a.val = 1 + 2 ^ h) := by
  unfold threeCover
  have hmod := coord_mod (alph_pos h) v a
  simp [hmod]

theorem threeCover_eval_rhs0 {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (threeCover (n := resN L φ) (legalH_pos_of hh))
      (midFormula hh φ h3 i) = true := by
  refine (eval_compileMid hh
      (threeCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_⟩
  · simpa [h0] using legalBoth_zero hh
  · have hc := threeCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resCenter (L := L) φ h3 i) ⟨0, alph_pos (legalH L)⟩
    simpa using hc
  · intro j
    have hrest := restrictLow_zero (midK_le (legalH_pos_of hh))
    rw [hrest]
    have hc := threeCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ j) ⟨0, alph_pos (legalH L)⟩
    simpa using hc

theorem threeCover_eval_rhs1 {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (threeCover (n := resN L φ) (legalH_pos_of hh))
      (midFormula hh φ h3 i) = true := by
  refine (eval_compileMid hh
      (threeCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨dualBit (legalH_pos_of hh), ?_, ?_, ?_⟩
  · simpa [h1] using legalBoth_dualBit hh
  · have hc := threeCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resCenter (L := L) φ h3 i) (dualBit (legalH_pos_of hh))
    simpa [dualBit] using hc
  · intro j
    have hrest := restrictLow_dualBit_eq_one hh
    rw [hrest]
    have hc := threeCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ j) (lowOne (legalH_pos_of hh))
    simpa [lowOne] using hc

theorem threeCover_eval_unsatCnf_rhs1 {L : Nat} (hh : 2 < legalH L) :
    Formula.eval
      (threeCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (midFormula hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩) = true :=
  threeCover_eval_rhs1 hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩ unsatCnf_rhs1

private theorem honest_eval_mid {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (midFormula hh φ h3 i) = true := by
  refine (eval_compileMid hh
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_⟩
  · simpa [h0] using legalBoth_zero hh
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (legalH L) + (0 : Nat)) %
          alph (legalH L) = 0) = true
    simpa [Nat.mul_mod_left]
  · intro j
    have hrest := restrictLow_zero (midK_le (legalH_pos_of hh))
    change decide
        (((resLeaf L φ j).val * alph (legalH L) +
          (restrictLow (midK_le (legalH_pos_of hh))
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]

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

private theorem mid_honest_cost {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (midResData hh φ h3 hM).cost
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (midRes_len hh φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph (legalH L)) := by
  unfold Data.cost Data.coordinateWeights
  simp only [midResData, indexedData, List.get_ofFn]
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

private theorem mid_honest_sat_of_rhs0 {L : Nat} (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hall0 : ∀ i : Fin φ.length, clauseRhs φ h3 i = 0) :
    (midResData hh φ h3 hM).satisfaction
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (midRes_len hh φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (midResData hh φ h3 hM).formulas.length) := by
    simp [midResData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (midResData hh φ h3 hM).formulas.length,
      Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (midRes_len hh φ h3 hM) ▸ i.isLt⟩)
        ((midResData hh φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [midResData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
      (midFormulas hh φ h3) (compactBudget (alph (legalH L)))
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val, by
        simpa [midResData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [midResData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [midResData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (midFormulas hh φ h3 ⟨j.val, hj⟩)) ?_).trans
      (honest_eval_mid hh φ h3 ⟨j.val, hj⟩ (hall0 ⟨j.val, hj⟩))
    funext v
    exact congrArg (honest (n := resN L φ) (alph_pos (legalH L)))
      (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (midRes_len hh φ h3 hM) ▸ i.isLt⟩)
        ((midResData hh φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem midResData_yes_unit3 {L : Nat} (h : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Yes 0 (ofData (midResData hh unit3 unit3_is3 unit3_len)
      (midResData_valid h hh unit3 unit3_is3 unit3_len)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := resN L unit3) (alph_pos (legalH L)) ⟨i.val,
      (midRes_len hh unit3 unit3_is3 unit3_len) ▸ i.isLt⟩, ?_, ?_⟩
  · have hcost := mid_honest_cost hh unit3 unit3_is3 unit3_len
    have hle : compactBudget (alph (legalH L)) ≤
        (midResData hh unit3 unit3_is3 unit3_len).budget := by
      simp [midResData, indexedData]
    exact hcost.trans_le hle
  · have hsat := mid_honest_sat_of_rhs0 hh unit3 unit3_is3 unit3_len
      unit3_all_rhs0
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

def midWeightRat (L : Nat) : Rat :=
  (1 : Rat) / ((paramN L * ROf L : Nat) : Rat)

def midBudgetRat (L : Nat) : Rat :=
  (1 : Rat) / (ROf L : Rat)

def midWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L) (ratTree (midWeightRat L))))

def midBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree (midBudgetRat L))

def midFormulaTree {L : Nat} (hh : 2 < legalH L) : CMMSACodec.Tree :=
  formulaTree
    (compileMid hh (paramCenter L) (paramLeaf L) 0)

def midFormulaEnc {L : Nat} (hh : 2 < legalH L) : List Bool :=
  CMMSACodec.Tree.encode (midFormulaTree hh)

def midFormsEnc {L : Nat} (hh : 2 < legalH L) (z : List Bool) : List Bool :=
  true :: midFormulaEnc hh ++ (true :: clauseOrEnc z ++ [false])

theorem midFormsEnc_mem_FP {L : Nat} (hh : 2 < legalH L) :
    midFormsEnc (L := L) hh ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: midFormulaEnc hh)) htail

def midEncFn {L : Nat} (hh : 2 < legalH L) (z : List Bool) : List Bool :=
  true :: midWeightsEnc L ++ true :: midFormsEnc hh z ++ midBudgetEnc L

theorem midEncFn_mem_FP {L : Nat} (hh : 2 < legalH L) :
    midEncFn (L := L) hh ∈ Complexity.FP := by
  have hforms : (fun z => true :: midFormsEnc hh z) ∈ Complexity.FP :=
    mem_FP_comp (midFormsEnc_mem_FP hh) (Cobham.cons_mem_FP true)
  have hleft : (fun z => true :: midWeightsEnc L ++ true :: midFormsEnc hh z) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: midWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (midBudgetEnc L))

theorem midEncFn_ne_id {L : Nat} (hh : 2 < legalH L) :
    midEncFn (L := L) hh [] ≠ [] := by
  simp [midEncFn, midWeightsEnc]

end
end PvNP.RealizableHardness.ActualThreeSatHalfWidth
