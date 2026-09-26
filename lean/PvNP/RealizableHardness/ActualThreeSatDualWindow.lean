import PvNP.RealizableHardness.ActualThreeSatLegalBreak

/-!
Dual-window filter: one `orFilter` branch whose center label satisfies
both DualStar `legal3Lin` (bits `0,1,2`) and LegalRes `legalHigh`
(bits `h,h+1,h+2`) for the clause RHS.

Sat unit is `Yes 0` via label `0`.  `{0,1}` fails RHS-1 (`legalHigh` of
`1` is false).  `{0, 2^h}` fails RHS-1 (`legal3Lin` of `2^h` is false).
Remaining 2-cover `{0, 1+2^h}` is still cheap, so this is not
`No σ_L γ_L` and does not inhabit `hSrcCmmsa`.  Not `if-sat`.
Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatDualWindow

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

theorem testBit_one_of_pos {k : Nat} (hk : 0 < k) :
    (1 : Nat).testBit k = false := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  have hlt : 1 < 2 ^ n.succ := Nat.one_lt_two_pow (Nat.succ_ne_zero n)
  have hdiv : (1 : Nat) / 2 ^ n.succ = 0 := Nat.div_eq_of_lt hlt
  have : ((1 : Nat) >>> n.succ) % 2 = 0 := by
    simp [Nat.shiftRight_eq_div_pow, hdiv]
  simpa [Nat.testBit] using this

theorem dualBit_lt {h : Nat} (hh : 0 < h) : 1 + 2 ^ h < alph h := by
  have hlt : 1 < 2 ^ h := Nat.one_lt_two_pow hh.ne'
  have h1 : 1 + 2 ^ h < 2 * 2 ^ h := by omega
  have h2 : 2 * 2 ^ h = 2 ^ (h + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have h3 : 2 ^ (h + 1) ≤ 2 ^ (2 * h) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) <| by
      have : h < h + h := Nat.lt_add_of_pos_right hh
      exact Nat.succ_le_of_lt (by simpa [two_mul] using this)
  exact lt_of_lt_of_le (h2 ▸ h1) (by simpa [alph] using h3)

def dualBit {h : Nat} (hh : 0 < h) : Fin (alph h) :=
  ⟨1 + 2 ^ h, dualBit_lt hh⟩

theorem one_add_pow_div {h : Nat} (hh : 0 < h) :
    (1 + 2 ^ h) / 2 ^ h = 1 := by
  have hpos := Nat.two_pow_pos h
  have : 1 + 2 ^ h = 2 ^ h * 1 + 1 := by ring
  rw [this, Nat.mul_add_div hpos, Nat.div_eq_of_lt (Nat.one_lt_two_pow hh.ne')]

theorem testBit_dual_zero {h : Nat} (hh : 0 < h) :
    (1 + 2 ^ h).testBit 0 = true := by
  have he : (2 ^ h) % 2 = 0 :=
    Nat.even_iff.mp (Nat.even_pow.2 ⟨by decide, hh.ne'⟩)
  have : (1 + 2 ^ h) % 2 = 1 := by simp [Nat.add_mod, he]
  have : ((1 + 2 ^ h) >>> 0) % 2 = 1 := by simpa [Nat.shiftRight_zero]
  simpa [Nat.testBit] using this

theorem testBit_dual_one {h : Nat} (hh : 1 < h) :
    (1 + 2 ^ h).testBit 1 = false := by
  have hh0 : 0 < h := lt_trans Nat.zero_lt_one hh
  have hpow : 2 ^ h = 2 * 2 ^ (h - 1) := by
    cases h with
    | zero => cases hh0
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  have hdiv2 : (1 + 2 ^ h) / 2 = 2 ^ (h - 1) := by
    have : 1 + 2 ^ h = 2 * 2 ^ (h - 1) + 1 := by omega
    rw [this, Nat.mul_add_div (by decide : 0 < 2),
      Nat.div_eq_of_lt (by decide : 1 < 2)]
    simp
  have hpos : 0 < h - 1 := Nat.sub_pos_of_lt hh
  have heven : (2 ^ (h - 1)) % 2 = 0 :=
    Nat.even_iff.mp (Nat.even_pow.2 ⟨by decide, hpos.ne'⟩)
  have : ((1 + 2 ^ h) >>> 1) % 2 = 0 := by
    simp [Nat.shiftRight_eq_div_pow, hdiv2, heven]
  simpa [Nat.testBit] using this

theorem testBit_dual_two {h : Nat} (hh : 2 < h) :
    (1 + 2 ^ h).testBit 2 = false := by
  have hh2 : 2 ≤ h := Nat.succ_le_of_lt (two_lt_h_to_one_lt hh)
  have hpow : 2 ^ h = 4 * 2 ^ (h - 2) := by
    have : 2 ^ h = 2 ^ (2 + (h - 2)) := by rw [Nat.add_comm, Nat.sub_add_cancel hh2]
    simpa [Nat.pow_add] using this
  have hdiv4 : (1 + 2 ^ h) / 4 = 2 ^ (h - 2) := by
    have : 1 + 2 ^ h = 4 * 2 ^ (h - 2) + 1 := by omega
    rw [this, Nat.mul_add_div (by decide : 0 < 4),
      Nat.div_eq_of_lt (by decide : 1 < 4)]
    simp
  have hpos : 0 < h - 2 := Nat.sub_pos_of_lt hh
  have heven : (2 ^ (h - 2)) % 2 = 0 :=
    Nat.even_iff.mp (Nat.even_pow.2 ⟨by decide, hpos.ne'⟩)
  have : ((1 + 2 ^ h) >>> 2) % 2 = 0 := by
    simp [Nat.shiftRight_eq_div_pow, hdiv4, heven]
  simpa [Nat.testBit] using this

theorem testBit_dual_h {h : Nat} (hh : 0 < h) :
    (1 + 2 ^ h).testBit h = true := by
  have : ((1 + 2 ^ h) >>> h) % 2 = 1 := by
    simp [Nat.shiftRight_eq_div_pow, one_add_pow_div hh]
  simpa [Nat.testBit] using this

theorem testBit_dual_succ_h {h k : Nat} (hh : 0 < h) (hk : 0 < k) :
    (1 + 2 ^ h).testBit (h + k) = false := by
  have hltpow : 1 < 2 ^ h := Nat.one_lt_two_pow hh.ne'
  have h1 : 1 + 2 ^ h < 2 * 2 ^ h := by omega
  have h2 : 2 * 2 ^ h = 2 ^ (h + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have h3 : 2 ^ (h + 1) ≤ 2 ^ (h + k) :=
    Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.add_le_add_left (Nat.succ_le_of_lt hk) h)
  have hlt : 1 + 2 ^ h < 2 ^ (h + k) :=
    lt_of_lt_of_le (h2 ▸ h1) h3
  have : ((1 + 2 ^ h) >>> (h + k)) % 2 = 0 := by
    simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
  simpa [Nat.testBit] using this

def legalBoth {h : Nat} (hh : 2 < h) (b : Fin (alph h)) (rhs : ZMod 2) : Prop :=
  legal3Lin (two_lt_h_to_one_lt hh) b rhs ∧ legalHigh hh b rhs

theorem legalBoth_zero {h : Nat} (hh : 2 < h) :
    legalBoth hh ⟨0, alph_pos h⟩ 0 :=
  ⟨legal3Lin_zero hh, legalHigh_zero hh⟩

theorem legalHigh_lowOne_not_one {h : Nat} (hh : 2 < h) :
    ¬ legalHigh hh (lowOne (two_lt_h_to_pos hh)) 1 := by
  intro hleg
  unfold legalHigh evalBit vecOfFin bit highBasis3 lowOne at hleg
  have t0 : (1 : Nat).testBit h = false :=
    testBit_one_of_pos (two_lt_h_to_pos hh)
  have t1 : (1 : Nat).testBit (h + 1) = false :=
    testBit_one_of_pos (Nat.succ_pos h)
  have t2 : (1 : Nat).testBit (h + 2) = false :=
    testBit_one_of_pos (Nat.succ_pos _)
  simp [t0, t1, t2] at hleg

theorem legalBoth_lowOne_not_one {h : Nat} (hh : 2 < h) :
    ¬ legalBoth hh (lowOne (two_lt_h_to_pos hh)) 1 :=
  fun ⟨_, hH⟩ => legalHigh_lowOne_not_one hh hH

theorem legalBoth_highBit_not_one {h : Nat} (hh : 2 < h) :
    ¬ legalBoth hh (highBit (two_lt_h_to_pos hh)) 1 :=
  fun ⟨hL, _⟩ => legal3Lin_highBit_not_one hh hL

theorem legalBoth_dualBit {h : Nat} (hh : 2 < h) :
    legalBoth hh (dualBit (two_lt_h_to_pos hh)) 1 := by
  refine ⟨?_, ?_⟩
  · unfold legal3Lin evalBit vecOfFin bit basis3 dualBit
    have t0 := testBit_dual_zero (two_lt_h_to_pos hh)
    have t1 := testBit_dual_one (two_lt_h_to_one_lt hh)
    have t2 := testBit_dual_two hh
    simp [t0, t1, t2]
  · unfold legalHigh evalBit vecOfFin bit highBasis3 dualBit
    have t0 := testBit_dual_h (two_lt_h_to_pos hh)
    have t1 := testBit_dual_succ_h (two_lt_h_to_pos hh) (by decide : 0 < 1)
    have t2 := testBit_dual_succ_h (two_lt_h_to_pos hh) (by decide : 0 < 2)
    simp [t0, t1, t2]

theorem legalBoth_exists {h : Nat} (hh : 2 < h) (rhs : ZMod 2) :
    ∃ b : Fin (alph h), legalBoth hh b rhs := by
  rcases zmod2_eq_zero_or_one rhs with h0 | h1
  · subst h0
    exact ⟨⟨0, alph_pos h⟩, legalBoth_zero hh⟩
  · subst h1
    exact ⟨dualBit (two_lt_h_to_pos hh), legalBoth_dualBit hh⟩

def isLegalBoth {h : Nat} (hh : 2 < h) (rhs : ZMod 2) (b : Fin (alph h)) :
    Bool :=
  decide (legalBoth hh b rhs)

theorem isLegalBoth_true_iff {h : Nat} (hh : 2 < h) (rhs : ZMod 2)
    (b : Fin (alph h)) :
    isLegalBoth hh rhs b = true ↔ legalBoth hh b rhs :=
  decide_eq_true_iff

theorem legalBoth_exists_bool {h : Nat} (hh : 2 < h) (rhs : ZMod 2) :
    ∃ b : Fin (alph h), isLegalBoth hh rhs b = true := by
  obtain ⟨b, hb⟩ := legalBoth_exists hh rhs
  exact ⟨b, (isLegalBoth_true_iff hh rhs b).mpr hb⟩

def compileBoth {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  Option.get
    (orFilter (alph h) (fun b => isLegalBoth hh rhs b)
      (fun b => branchRes hk c leaf b))
    (orFilter_isSome (fun b => isLegalBoth hh rhs b)
      (fun b => branchRes hk c leaf b) (legalBoth_exists_bool hh rhs))

theorem compileBoth_orFilter {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    orFilter (alph h) (fun b => isLegalBoth hh rhs b)
        (fun b => branchRes hk c leaf b) =
      some (compileBoth hh hk c leaf rhs) :=
  (Option.some_get (orFilter_isSome (fun b => isLegalBoth hh rhs b)
    (fun b => branchRes hk c leaf b) (legalBoth_exists_bool hh rhs))).symm

theorem eval_compileBoth {n h k m : Nat} (hh : 2 < h) (hk : k ≤ 2 * h)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileBoth hh hk c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legalBoth hh b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          ∀ i : Fin m,
            Z ⟨(leaf i).val * alph h + (restrictLow hk b).val,
              coord_lt (leaf i) (restrictLow hk b) (alph_pos h)⟩ = true := by
  have hor := eval_orFilter Z (alph h) (fun b => isLegalBoth hh rhs b)
    (fun b => branchRes hk c leaf b) (compileBoth hh hk c leaf rhs)
    (compileBoth_orFilter hh hk c leaf rhs)
  have hand (b : Fin (alph h)) :=
    eval_andFin Z (m + 1) (slotVarRes hk c leaf b) (branchRes hk c leaf b)
      (branchRes_andFin hk c leaf b)
  constructor
  · intro hf
    obtain ⟨b, hp, hb⟩ := hor.mp hf
    have hall := (hand b).mp hb
    refine ⟨b, (isLegalBoth_true_iff hh rhs b).mp hp, ?_, ?_⟩
    · simpa [slotVarRes, varAt, Formula.eval] using hall 0
    · intro i
      simpa [slotVarRes, varAt, Formula.eval] using hall i.succ
  · rintro ⟨b, hleg, hc, hleaf⟩
    refine hor.mpr ⟨b, (isLegalBoth_true_iff hh rhs b).mpr hleg, (hand b).mpr ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa [slotVarRes, varAt, Formula.eval] using hc
    | succ i => simpa [slotVarRes, varAt, Formula.eval] using hleaf i

def bothFormula {L : Nat} (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Formula (Fin (resN L φ * alph (legalH L))) :=
  compileBoth hh (legalK_le (legalH_pos_of hh))
    (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

def oneCover {n h : Nat} (_hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i => decide (i.val % alph h = 0 ∨ i.val % alph h = 1)

theorem oneCover_coord {n h : Nat} (hh : 0 < h) (v : Fin n)
    (a : Fin (alph h)) :
    oneCover (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1) := by
  unfold oneCover
  have hmod : (v.val * alph h + a.val) % alph h = a.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
  simp [hmod]

theorem twoCover_not_eval_rhs1 {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (twoCover (n := resN L φ) (legalH_pos_of hh))
      (bothFormula hh φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileBoth hh (legalK_le (legalH_pos_of hh))
      (twoCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [bothFormula] using htrue)
  obtain ⟨b, hleg, hc, _⟩ := he
  have hc' := twoCover_coord (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) b
  have hlit : b.val = 0 ∨ b.val = 2 ^ legalH L := of_decide_eq_true (by
    simpa [hc'] using hc)
  have hleg1 : legalBoth hh b 1 := by simpa [h1] using hleg
  rcases hlit with hb0 | hbh
  · have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
    exact legal3Lin_zero_not_one hh (by simpa [hb] using hleg1.1)
  · have hb : b = highBit (legalH_pos_of hh) := Fin.ext (by
      simpa [highBit] using hbh)
    exact legalBoth_highBit_not_one hh (by simpa [hb] using hleg1)

theorem oneCover_not_eval_rhs1 {L : Nat} (hh : 2 < legalH L) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (oneCover (n := resN L φ) (legalH_pos_of hh))
      (bothFormula hh φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileBoth hh (legalK_le (legalH_pos_of hh))
      (oneCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [bothFormula] using htrue)
  obtain ⟨b, hleg, hc, _⟩ := he
  have hc' := oneCover_coord (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) b
  have hlit : b.val = 0 ∨ b.val = 1 := of_decide_eq_true (by
    simpa [hc'] using hc)
  have hleg1 : legalBoth hh b 1 := by simpa [h1] using hleg
  rcases hlit with hb0 | hb1
  · have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
    exact legal3Lin_zero_not_one hh (by simpa [hb] using hleg1.1)
  · have hb : b = lowOne (legalH_pos_of hh) := Fin.ext (by
      simpa [lowOne] using hb1)
    exact legalBoth_lowOne_not_one hh (by simpa [hb] using hleg1)

theorem twoCover_not_eval_unsatCnf {L : Nat} (hh : 2 < legalH L) :
    Formula.eval
      (twoCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (bothFormula hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩) = false :=
  twoCover_not_eval_rhs1 hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩ unsatCnf_rhs1

theorem oneCover_not_eval_unsatCnf {L : Nat} (hh : 2 < legalH L) :
    Formula.eval
      (oneCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (bothFormula hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩) = false :=
  oneCover_not_eval_rhs1 hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩ unsatCnf_rhs1

def bothFormulaTree {L : Nat} (hh : 2 < legalH L) : CMMSACodec.Tree :=
  formulaTree
    (compileBoth hh (legalK_le (legalH_pos_of hh))
      (paramCenter L) (paramLeaf L) 0)

def bothFormulaEnc {L : Nat} (hh : 2 < legalH L) : List Bool :=
  CMMSACodec.Tree.encode (bothFormulaTree hh)

def bothWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L)
      (ratTree ((1 : Rat) / ((paramN L * ROf L : Nat) : Rat)))))

def bothBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree ((1 : Rat) / (ROf L : Rat)))

def bothFormsEnc {L : Nat} (hh : 2 < legalH L) (z : List Bool) : List Bool :=
  true :: bothFormulaEnc hh ++ (true :: clauseOrEnc z ++ [false])

theorem bothFormsEnc_mem_FP {L : Nat} (hh : 2 < legalH L) :
    bothFormsEnc (L := L) hh ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: bothFormulaEnc hh)) htail

def bothEncFn {L : Nat} (hh : 2 < legalH L) (z : List Bool) : List Bool :=
  true :: bothWeightsEnc L ++ true :: bothFormsEnc hh z ++ bothBudgetEnc L

theorem bothEncFn_mem_FP {L : Nat} (hh : 2 < legalH L) :
    bothEncFn (L := L) hh ∈ Complexity.FP := by
  have hforms : (fun z => true :: bothFormsEnc hh z) ∈ Complexity.FP :=
    mem_FP_comp (bothFormsEnc_mem_FP hh) (Cobham.cons_mem_FP true)
  have hleft : (fun z => true :: bothWeightsEnc L ++ true :: bothFormsEnc hh z) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: bothWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (bothBudgetEnc L))

theorem bothEncFn_ne_id {L : Nat} (hh : 2 < legalH L) :
    bothEncFn (L := L) hh [] ≠ [] := by
  simp [bothEncFn, bothWeightsEnc]

end
end PvNP.RealizableHardness.ActualThreeSatDualWindow
