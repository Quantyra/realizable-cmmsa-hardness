import PvNP.RealizableHardness.ActualThreeSatHalfWidth

/-!
Overlapping high-bit restriction chart on a DualWindow `legalBoth` star:
each branch lights center color `b` and dummy leaf `0` at `restrictHigh b`
(high half of the `2h`-bit label).  Combined with half-width `legalBoth`
this is two restriction charts of the same center color.

The HalfWidth vertex-dependent 2-list (centers `{0,1+2^h}`, other
vertices `{0,1}`) fails RHS-1: every 1-legal color has
`restrictHigh ≥ 2^h`, which those leaves do not light.  Sat unit remains
`Yes 0` via label `0`.

The 4-label palette `{0, 1, 2^h, 1+2^h}` still covers mixed RHS, so this
is not `No σ_L γ_L` and does not inhabit `hSrcCmmsa`.  Not `if-sat`.
Not `compileMid` / `threeCover` / `twoHot`.  Checking-transducer `mem_FP`
is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatOverlap

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
open ActualThreeSatHalfWidth
open ActualThreeSatXorStars
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

theorem restrictHigh_lt {h : Nat} (hh : 0 < h) (a : Fin (alph h)) :
    (a.val / 2 ^ h) * 2 ^ h < alph h := by
  have hpos := Nat.two_pow_pos h
  have hdiv : a.val / 2 ^ h < 2 ^ h := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have hab : a.val < 2 ^ (2 * h) := by simpa [alph] using a.isLt
    have hpow : 2 ^ h * 2 ^ h = 2 ^ (2 * h) := by simp [two_mul, Nat.pow_add]
    exact hab.trans_eq hpow.symm
  have hmul : (a.val / 2 ^ h) * 2 ^ h < 2 ^ h * 2 ^ h :=
    Nat.mul_lt_mul_of_pos_right hdiv hpos
  have hpow : 2 ^ h * 2 ^ h = 2 ^ (2 * h) := by simp [two_mul, Nat.pow_add]
  simpa [alph, hpow] using hmul

def restrictHigh {h : Nat} (hh : 0 < h) (a : Fin (alph h)) : Fin (alph h) :=
  ⟨(a.val / 2 ^ h) * 2 ^ h, restrictHigh_lt hh a⟩

theorem restrictHigh_zero {h : Nat} (hh : 0 < h) :
    restrictHigh hh ⟨0, alph_pos h⟩ = ⟨0, alph_pos h⟩ :=
  Fin.ext (by simp [restrictHigh])

theorem restrictHigh_ne_id {h : Nat} (hh : 0 < h) :
    restrictHigh hh ⟨1, one_lt_alph_of hh⟩ ≠ ⟨1, one_lt_alph_of hh⟩ := by
  intro heq
  have hval : (1 / 2 ^ h) * 2 ^ h = 1 := congrArg Fin.val heq
  have hlt : 1 < 2 ^ h := Nat.one_lt_two_pow hh.ne'
  have hdiv : (1 : Nat) / 2 ^ h = 0 := Nat.div_eq_of_lt hlt
  simp [hdiv] at hval

theorem restrictHigh_dualBit {h : Nat} (hh : 2 < h) :
    restrictHigh (two_lt_h_to_pos hh) (dualBit (two_lt_h_to_pos hh)) =
      highBit (two_lt_h_to_pos hh) := by
  apply Fin.ext
  have hdiv := one_add_pow_div (two_lt_h_to_pos hh)
  simp [restrictHigh, dualBit, highBit, hdiv]

theorem testBit_of_lt_pow {x i : Nat} (h : x < 2 ^ i) :
    x.testBit i = false := by
  have : x / 2 ^ i = 0 := Nat.div_eq_of_lt h
  have : (x >>> i) % 2 = 0 := by
    simp [Nat.shiftRight_eq_div_pow, this]
  simpa [Nat.testBit] using this

theorem restrictHigh_of_legalHigh_one {h : Nat} (hh : 2 < h)
    (a : Fin (alph h)) (hleg : legalHigh hh a 1) :
    2 ^ h ≤ (restrictHigh (two_lt_h_to_pos hh) a).val := by
  by_contra hlt
  have hlt' : (restrictHigh (two_lt_h_to_pos hh) a).val < 2 ^ h :=
    Nat.not_le.mp hlt
  have hmul : (a.val / 2 ^ h) * 2 ^ h < 2 ^ h := by
    simpa [restrictHigh] using hlt'
  have hpos := Nat.two_pow_pos h
  have hdiv0 : a.val / 2 ^ h = 0 := by
    have hmul1 : (a.val / 2 ^ h) * 2 ^ h < 1 * 2 ^ h := by simpa using hmul
    have : a.val / 2 ^ h < 1 := Nat.lt_of_mul_lt_mul_right hmul1
    exact Nat.lt_one_iff.mp this
  have habs : a.val < 2 ^ h := by
    have hiff := (Nat.div_eq_zero_iff (a := a.val) (b := 2 ^ h)).mp hdiv0
    rcases hiff with h0 | hltabs
    · exact False.elim (hpos.ne' h0)
    · exact hltabs
  have hz : legalHigh hh a 0 := by
    unfold legalHigh evalBit vecOfFin bit highBasis3
    have t0 : a.val.testBit h = false := testBit_of_lt_pow habs
    have t1 : a.val.testBit (h + 1) = false :=
      testBit_of_lt_pow (lt_trans habs (Nat.pow_lt_pow_right
        (by decide : 1 < 2) (Nat.lt_succ_self h)))
    have t2 : a.val.testBit (h + 2) = false :=
      testBit_of_lt_pow (lt_trans habs (Nat.pow_lt_pow_right
        (by decide : 1 < 2) (by omega)))
    simp [t0, t1, t2]
  exact legalHigh_not_both hh a ⟨hz, hleg⟩

theorem restrictHigh_ne_lowOne {h : Nat} (hh : 2 < h)
    (a : Fin (alph h)) (hleg : legalHigh hh a 1) :
    restrictHigh (two_lt_h_to_pos hh) a ≠
      lowOne (two_lt_h_to_pos hh) := by
  intro heq
  have hval : (restrictHigh (two_lt_h_to_pos hh) a).val = 1 := by
    simpa [lowOne] using congrArg Fin.val heq
  have hge := restrictHigh_of_legalHigh_one hh a hleg
  have hlt : 1 < 2 ^ h := Nat.one_lt_two_pow (two_lt_h_to_pos hh).ne'
  omega

def slotVarOverlap {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Fin 2 → Formula (Fin (n * alph h)) :=
  fun i =>
    if i.val = 0 then varAt (alph_pos h) c b
    else varAt (alph_pos h) (leaf ⟨0, hm⟩) (restrictHigh hh b)

def branchOverlap {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Formula (Fin (n * alph h)) :=
  Option.get (andFin 2 (slotVarOverlap hh hm c leaf b))
    (andFin_isSome (by decide : 0 < 2) _)

theorem branchOverlap_andFin {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    andFin 2 (slotVarOverlap hh hm c leaf b) =
      some (branchOverlap hh hm c leaf b) :=
  (Option.some_get (andFin_isSome (by decide : 0 < 2) _)).symm

theorem eval_branchOverlap {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (b : Fin (alph h)) :
    Formula.eval Z (branchOverlap hh hm c leaf b) = true ↔
      Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
        Z ⟨(leaf ⟨0, hm⟩).val * alph h + (restrictHigh hh b).val,
          coord_lt (leaf ⟨0, hm⟩) (restrictHigh hh b) (alph_pos h)⟩ =
          true := by
  have hand := eval_andFin Z 2 (slotVarOverlap hh hm c leaf b)
    (branchOverlap hh hm c leaf b) (branchOverlap_andFin hh hm c leaf b)
  constructor
  · intro hf
    have hall := hand.mp hf
    refine ⟨?_, ?_⟩
    · have h0 := hall ⟨0, by decide⟩
      simpa [slotVarOverlap, varAt, Formula.eval] using h0
    · have h1 := hall ⟨1, by decide⟩
      simpa [slotVarOverlap, varAt, Formula.eval] using h1
  · rintro ⟨hc, hhi⟩
    refine hand.mpr ?_
    intro j
    by_cases hj : j.val = 0
    · have : j = ⟨0, by decide⟩ := Fin.ext hj
      simpa [this, slotVarOverlap, varAt, Formula.eval] using hc
    · have : j = ⟨1, by decide⟩ := Fin.ext (by
        have hpos : 0 < j.val := Nat.pos_of_ne_zero hj
        have hle : j.val ≤ 1 := Nat.le_of_lt_succ j.isLt
        exact Nat.le_antisymm hle (Nat.succ_le_of_lt hpos))
      simpa [this, slotVarOverlap, varAt, Formula.eval] using hhi

def compileOverlap {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  Option.get
    (orFilter (alph h) (fun b => isLegalBoth hh rhs b)
      (fun b => branchOverlap (two_lt_h_to_pos hh) hm c leaf b))
    (orFilter_isSome (fun b => isLegalBoth hh rhs b)
      (fun b => branchOverlap (two_lt_h_to_pos hh) hm c leaf b)
      (legalBoth_exists_bool hh rhs))

theorem compileOverlap_orFilter {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    orFilter (alph h) (fun b => isLegalBoth hh rhs b)
        (fun b => branchOverlap (two_lt_h_to_pos hh) hm c leaf b) =
      some (compileOverlap hh hm c leaf rhs) :=
  (Option.some_get (orFilter_isSome (fun b => isLegalBoth hh rhs b)
    (fun b => branchOverlap (two_lt_h_to_pos hh) hm c leaf b)
    (legalBoth_exists_bool hh rhs))).symm

theorem eval_compileOverlap {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileOverlap hh hm c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legalBoth hh b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          Z ⟨(leaf ⟨0, hm⟩).val * alph h +
              (restrictHigh (two_lt_h_to_pos hh) b).val,
            coord_lt (leaf ⟨0, hm⟩)
              (restrictHigh (two_lt_h_to_pos hh) b) (alph_pos h)⟩ = true := by
  have hor := eval_orFilter Z (alph h) (fun b => isLegalBoth hh rhs b)
    (fun b => branchOverlap (two_lt_h_to_pos hh) hm c leaf b)
    (compileOverlap hh hm c leaf rhs)
    (compileOverlap_orFilter hh hm c leaf rhs)
  constructor
  · intro hf
    obtain ⟨b, hp, hb⟩ := hor.mp hf
    obtain ⟨hc, hhi⟩ :=
      (eval_branchOverlap (two_lt_h_to_pos hh) hm Z c leaf b).mp hb
    exact ⟨b, (isLegalBoth_true_iff hh rhs b).mp hp, hc, hhi⟩
  · rintro ⟨b, hleg, hc, hhi⟩
    refine hor.mpr ⟨b, (isLegalBoth_true_iff hh rhs b).mpr hleg, ?_⟩
    exact (eval_branchOverlap (two_lt_h_to_pos hh) hm Z c leaf b).mpr
      ⟨hc, hhi⟩

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

def vdCover {n h : Nat} (hh : 0 < h) (c : Fin n) : Fin (n * alph h) → Bool :=
  fun i =>
    if i.val / alph h = c.val then
      decide (i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h)
    else
      decide (i.val % alph h = 0 ∨ i.val % alph h = 1)

theorem vdCover_center {n h : Nat} (hh : 0 < h) (c : Fin n)
    (a : Fin (alph h)) :
    vdCover (n := n) hh c
        ⟨c.val * alph h + a.val, coord_lt c a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 + 2 ^ h) := by
  unfold vdCover
  have hdiv : (c.val * alph h + a.val) / alph h = c.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (alph_pos h),
      Nat.div_eq_of_lt a.isLt]
    simp
  have hmod := coord_mod (alph_pos h) c a
  simp [hdiv, hmod]

theorem vdCover_other {n h : Nat} (hh : 0 < h) (c v : Fin n)
    (hv : v ≠ c) (a : Fin (alph h)) :
    vdCover (n := n) hh c
        ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1) := by
  unfold vdCover
  have hdiv : (v.val * alph h + a.val) / alph h = v.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (alph_pos h),
      Nat.div_eq_of_lt a.isLt]
    simp
  have hmod := coord_mod (alph_pos h) v a
  have hne : v.val ≠ c.val := fun h => hv (Fin.ext h)
  simp [hdiv, hmod, hne]

theorem resCenter_ne_resLeaf {L : Nat} (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) (j : Fin (paramM L)) :
    resCenter (L := L) φ h3 i ≠ resLeaf L φ j := by
  intro heq
  have hval := congrArg Fin.val heq
  have hc : (resCenter (L := L) φ h3 i).val < nPol φ := by
    unfold resCenter
    exact (clausePol φ h3 i 0).isLt
  have hl : nPol φ < (resLeaf L φ j).val := by
    unfold resLeaf
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  exact Nat.lt_irrefl _ (lt_trans hc (hval ▸ hl))

def overlapFormula {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula (Fin (resN L φ * alph (legalH L))) :=
  compileOverlap hh hm (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

theorem vdCover_not_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (vdCover (n := resN L φ) (legalH_pos_of hh)
        (resCenter (L := L) φ h3 i))
      (overlapFormula hh (paramM_pos_of hm) φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileOverlap hh (paramM_pos_of hm)
      (vdCover (n := resN L φ) (legalH_pos_of hh)
        (resCenter (L := L) φ h3 i))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [overlapFormula] using htrue)
  obtain ⟨b, hleg, hc, hhi⟩ := he
  have hleg1 : legalBoth hh b 1 := by simpa [h1] using hleg
  have hne := resCenter_ne_resLeaf (L := L) φ h3 i ⟨0, paramM_pos_of hm⟩
  have hcL := vdCover_other (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) (resLeaf L φ ⟨0, paramM_pos_of hm⟩) hne.symm
    (restrictHigh (legalH_pos_of hh) b)
  have hlit : (restrictHigh (legalH_pos_of hh) b).val = 0 ∨
      (restrictHigh (legalH_pos_of hh) b).val = 1 := of_decide_eq_true (by
    simpa [hcL] using hhi)
  have hne0 : restrictHigh (legalH_pos_of hh) b ≠
      ⟨0, alph_pos (legalH L)⟩ := by
    intro hz
    have hge := restrictHigh_of_legalHigh_one hh b hleg1.2
    have hzv : (restrictHigh (legalH_pos_of hh) b).val = 0 :=
      congrArg Fin.val hz
    have hpos := Nat.two_pow_pos (legalH L)
    omega
  have hne1 := restrictHigh_ne_lowOne hh b hleg1.2
  rcases hlit with hz | h1b
  · exact hne0 (Fin.ext hz)
  · have hb : restrictHigh (legalH_pos_of hh) b =
        lowOne (legalH_pos_of hh) := Fin.ext (by simpa [lowOne] using h1b)
    exact hne1 hb

theorem vdCover_not_eval_unsatCnf {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Formula.eval
      (vdCover (n := resN L unsatCnf) (legalH_pos_of hh)
        (resCenter (L := L) unsatCnf unsatCnf_is3 ⟨1, by decide⟩))
      (overlapFormula hh (paramM_pos_of hm) unsatCnf unsatCnf_is3
        ⟨1, by decide⟩) = false :=
  vdCover_not_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩
    unsatCnf_rhs1

def fourCover {n h : Nat} (_hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i =>
    decide (i.val % alph h = 0 ∨ i.val % alph h = 1 ∨
      i.val % alph h = 2 ^ h ∨ i.val % alph h = 1 + 2 ^ h)

theorem fourCover_coord {n h : Nat} (hh : 0 < h) (v : Fin n)
    (a : Fin (alph h)) :
    fourCover (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ^ h ∨ a.val = 1 + 2 ^ h) := by
  unfold fourCover
  have hmod := coord_mod (alph_pos h) v a
  simp [hmod]

theorem fourCover_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (fourCover (n := resN L φ) (legalH_pos_of hh))
      (overlapFormula hh (paramM_pos_of hm) φ h3 i) = true := by
  refine (eval_compileOverlap hh (paramM_pos_of hm)
      (fourCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨dualBit (legalH_pos_of hh), ?_, ?_, ?_⟩
  · simpa [h1] using legalBoth_dualBit hh
  · have hc := fourCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resCenter (L := L) φ h3 i) (dualBit (legalH_pos_of hh))
    simpa [dualBit] using hc
  · have hrest := restrictHigh_dualBit hh
    rw [hrest]
    have hc := fourCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ ⟨0, paramM_pos_of hm⟩) (highBit (legalH_pos_of hh))
    simpa [highBit] using hc

theorem fourCover_eval_unsatCnf_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Formula.eval
      (fourCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (overlapFormula hh (paramM_pos_of hm) unsatCnf unsatCnf_is3
        ⟨1, by decide⟩) = true :=
  fourCover_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩ unsatCnf_rhs1

private theorem honest_eval_overlap {L : Nat} (hh : 2 < legalH L)
    (hm : 0 < paramM L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (overlapFormula hh hm φ h3 i) = true := by
  refine (eval_compileOverlap hh hm
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_⟩
  · simpa [h0] using legalBoth_zero hh
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (legalH L) + (0 : Nat)) %
          alph (legalH L) = 0) = true
    simpa [Nat.mul_mod_left]
  · have hrest := restrictHigh_zero (legalH_pos_of hh)
    change decide
        (((resLeaf L φ ⟨0, hm⟩).val * alph (legalH L) +
          (restrictHigh (legalH_pos_of hh)
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]

def overlapFormulaTree {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    CMMSACodec.Tree :=
  formulaTree
    (compileOverlap hh hm (paramCenter L) (paramLeaf L) 0)

def overlapFormulaEnc {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    List Bool :=
  CMMSACodec.Tree.encode (overlapFormulaTree hh hm)

def overlapWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L)
      (ratTree ((1 : Rat) / ((paramN L * ROf L : Nat) : Rat)))))

def overlapBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree ((1 : Rat) / (ROf L : Rat)))

def overlapFormsEnc {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (z : List Bool) : List Bool :=
  true :: overlapFormulaEnc hh hm ++ (true :: clauseOrEnc z ++ [false])

theorem overlapFormsEnc_mem_FP {L : Nat} (hh : 2 < legalH L)
    (hm : 0 < paramM L) :
    overlapFormsEnc (L := L) hh hm ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: overlapFormulaEnc hh hm)) htail

def overlapEncFn {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (z : List Bool) : List Bool :=
  true :: overlapWeightsEnc L ++ true :: overlapFormsEnc hh hm z ++
    overlapBudgetEnc L

theorem overlapEncFn_mem_FP {L : Nat} (hh : 2 < legalH L)
    (hm : 0 < paramM L) :
    overlapEncFn (L := L) hh hm ∈ Complexity.FP := by
  have hforms : (fun z => true :: overlapFormsEnc hh hm z) ∈ Complexity.FP :=
    mem_FP_comp (overlapFormsEnc_mem_FP hh hm) (Cobham.cons_mem_FP true)
  have hleft :
      (fun z => true :: overlapWeightsEnc L ++ true :: overlapFormsEnc hh hm z) ∈
        Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: overlapWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (overlapBudgetEnc L))

theorem overlapEncFn_ne_id {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    overlapEncFn (L := L) hh hm [] ≠ [] := by
  simp [overlapEncFn, overlapWeightsEnc]

end
end PvNP.RealizableHardness.ActualThreeSatOverlap
