import PvNP.RealizableHardness.ActualThreeSatRotate

/-!
Overlapping three-leaf restriction fan: DualWindow `legalBoth` plus
distinct dummy leaves `0,1,2` at left-shifts `restrictShift j`
(`b * 2^j mod 2^{2h}`), not dummy-leaf-only.

Kills Rotate leftover `sevenCover` (shift-2 sends `1+2^h` to
`4+2^{h+2}`) and `cheapTwo` (leaf 0 must copy the center color).
Sat unit is packed `Yes 0` via label `0`.

The vertex-dependent 2-list (center `{0,1+2^h}`, leaf `j` lights
`{0, (1+2^h)<<j}`) has only the i-dependent, unconstrained local
RHS-1 witness `vdFan_eval_rhs1`: it proves neither one global assignment
nor feasibility/cost.  `ActualThreeSatFanQuadKill` gives the global
4-label palette and shows `fanData` is not manuscript `No` once
`4 ≤ manuscriptSigma`.
Not `if-sat`.
Not `compileRotate` / `sevenCover` / `compileOverlap` / `fourCover`.
Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGrassmannFan

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
open ActualThreeSatOverlap
open ActualThreeSatRotate
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

theorem three_lt_h_to_two_lt {h : Nat} (hh : 3 < h) : 2 < h :=
  lt_trans (by decide : 2 < 3) hh

theorem three_lt_h_to_pos {h : Nat} (hh : 3 < h) : 0 < h :=
  lt_trans (by decide : 0 < 3) hh

theorem three_lt_h_to_one_lt {h : Nat} (hh : 3 < h) : 1 < h :=
  lt_trans (by decide : 1 < 3) hh

theorem paramM_ge_3 {L : Nat} (h : 256 ≤ mOf L) : 3 ≤ paramM L :=
  le_trans (by decide : 3 ≤ 256) (by simpa [paramM] using h)

def restrictShift {h : Nat} (_hh : 0 < h) (j : Nat) (a : Fin (alph h)) :
    Fin (alph h) :=
  ⟨(a.val * 2 ^ j) % alph h, Nat.mod_lt _ (alph_pos h)⟩

theorem restrictShift_zero {h : Nat} (hh : 0 < h) (j : Nat) :
    restrictShift hh j ⟨0, alph_pos h⟩ = ⟨0, alph_pos h⟩ :=
  Fin.ext (by simp [restrictShift])

theorem restrictShift_id {h : Nat} (hh : 0 < h) (a : Fin (alph h)) :
    restrictShift hh 0 a = a := by
  apply Fin.ext
  have hmod : a.val % alph h = a.val := Nat.mod_eq_of_lt a.isLt
  simp [restrictShift, hmod]

theorem restrictShift_one {h : Nat} (hh : 0 < h) (a : Fin (alph h)) :
    restrictShift hh 1 a = restrictRot hh a := by
  apply Fin.ext
  simp [restrictShift, restrictRot]

theorem mul_shift_val (h j : Nat) :
    (1 + 2 ^ h) * 2 ^ j = 2 ^ j + 2 ^ (h + j) := by
  rw [Nat.add_mul, Nat.one_mul, Nat.pow_add]

theorem shift_dual_lt_alph {h j : Nat} (hh : 3 < h) (hj : j ≤ 2) :
    2 ^ j + 2 ^ (h + j) < alph h := by
  have hlt : 2 ^ j + 2 ^ (h + j) < 2 ^ (h + j + 1) := by
    have : 2 ^ j < 2 ^ (h + j) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.lt_add_of_pos_left (three_lt_h_to_pos hh) : j < h + j)
    have hpow : 2 ^ (h + j + 1) = 2 * 2 ^ (h + j) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    omega
  have hle : 2 ^ (h + j + 1) ≤ 2 ^ (2 * h) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by
      have : j + 1 ≤ h := by
        have : 3 ≤ h := Nat.le_of_lt hh
        omega
      have : h + j + 1 ≤ h + h := by
        have := Nat.add_le_add_left this h
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      simpa [two_mul] using this)
  exact lt_of_lt_of_le hlt (by simpa [alph] using hle)

theorem restrictShift_dualBit {h : Nat} (hh : 3 < h) {j : Nat}
    (hj : j ≤ 2) :
    (restrictShift (three_lt_h_to_pos hh) j
        (dualBit (three_lt_h_to_pos hh))).val =
      2 ^ j + 2 ^ (h + j) := by
  have hlt := shift_dual_lt_alph hh hj
  simp [restrictShift, dualBit]
  rw [mul_shift_val]
  exact Nat.mod_eq_of_lt (by simpa [alph] using hlt)

theorem restrictShift_ne_id {h : Nat} (hh : 0 < h) :
    restrictShift hh 1 ⟨1, one_lt_alph_of hh⟩ ≠
      ⟨1, one_lt_alph_of hh⟩ := by
  intro heq
  have : (2 : Nat) = 1 := by
    have hmod : (2 : Nat) % alph h = 2 := Nat.mod_eq_of_lt (two_lt_alph hh)
    simpa [restrictShift, hmod] using congrArg Fin.val heq
  exact (by decide : ¬ (2 : Nat) = 1) this

def slotVarFan {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Fin 4 → Formula (Fin (n * alph h)) :=
  fun i =>
    if i.val = 0 then varAt (alph_pos h) c b
    else if i.val = 1 then
      varAt (alph_pos h) (leaf ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩)
        (restrictShift (three_lt_h_to_pos hh) 0 b)
    else if i.val = 2 then
      varAt (alph_pos h) (leaf ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩)
        (restrictShift (three_lt_h_to_pos hh) 1 b)
    else
      varAt (alph_pos h) (leaf ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩)
        (restrictShift (three_lt_h_to_pos hh) 2 b)

def branchFan {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Formula (Fin (n * alph h)) :=
  Option.get (andFin 4 (slotVarFan hh hm c leaf b))
    (andFin_isSome (by decide : 0 < 4) _)

theorem branchFan_andFin {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    andFin 4 (slotVarFan hh hm c leaf b) =
      some (branchFan hh hm c leaf b) :=
  (Option.some_get (andFin_isSome (by decide : 0 < 4) _)).symm

theorem fin4_eq {j : Fin 4} :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
  have : j.val < 4 := j.isLt
  omega

theorem eval_branchFan {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (b : Fin (alph h)) :
    Formula.eval Z (branchFan hh hm c leaf b) = true ↔
      Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
        Z ⟨(leaf ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩).val * alph h +
            (restrictShift (three_lt_h_to_pos hh) 0 b).val,
          coord_lt (leaf ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩)
            (restrictShift (three_lt_h_to_pos hh) 0 b) (alph_pos h)⟩ = true ∧
          Z ⟨(leaf ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩).val * alph h +
              (restrictShift (three_lt_h_to_pos hh) 1 b).val,
            coord_lt (leaf ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩)
              (restrictShift (three_lt_h_to_pos hh) 1 b) (alph_pos h)⟩ = true ∧
            Z ⟨(leaf ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩).val * alph h +
                (restrictShift (three_lt_h_to_pos hh) 2 b).val,
              coord_lt (leaf ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩)
                (restrictShift (three_lt_h_to_pos hh) 2 b) (alph_pos h)⟩ =
              true := by
  have hand := eval_andFin Z 4 (slotVarFan hh hm c leaf b)
    (branchFan hh hm c leaf b) (branchFan_andFin hh hm c leaf b)
  constructor
  · intro hf
    have hall := hand.mp hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [slotVarFan, varAt, Formula.eval] using hall ⟨0, by decide⟩
    · simpa [slotVarFan, varAt, Formula.eval] using hall ⟨1, by decide⟩
    · simpa [slotVarFan, varAt, Formula.eval] using hall ⟨2, by decide⟩
    · simpa [slotVarFan, varAt, Formula.eval] using hall ⟨3, by decide⟩
  · rintro ⟨hc, h0, h1, h2⟩
    refine hand.mpr ?_
    intro j
    rcases fin4_eq (j := j) with hz | h1' | h2' | h3
    · have : j = ⟨0, by decide⟩ := Fin.ext hz
      simpa [this, slotVarFan, varAt, Formula.eval] using hc
    · have : j = ⟨1, by decide⟩ := Fin.ext h1'
      simpa [this, slotVarFan, varAt, Formula.eval] using h0
    · have : j = ⟨2, by decide⟩ := Fin.ext h2'
      simpa [this, slotVarFan, varAt, Formula.eval] using h1
    · have : j = ⟨3, by decide⟩ := Fin.ext h3
      simpa [this, slotVarFan, varAt, Formula.eval] using h2

def compileFan {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  Option.get
    (orFilter (alph h) (fun b => isLegalBoth (three_lt_h_to_two_lt hh) rhs b)
      (fun b => branchFan hh hm c leaf b))
    (orFilter_isSome (fun b => isLegalBoth (three_lt_h_to_two_lt hh) rhs b)
      (fun b => branchFan hh hm c leaf b)
      (legalBoth_exists_bool (three_lt_h_to_two_lt hh) rhs))

theorem compileFan_orFilter {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    orFilter (alph h) (fun b => isLegalBoth (three_lt_h_to_two_lt hh) rhs b)
        (fun b => branchFan hh hm c leaf b) =
      some (compileFan hh hm c leaf rhs) :=
  (Option.some_get (orFilter_isSome
    (fun b => isLegalBoth (three_lt_h_to_two_lt hh) rhs b)
    (fun b => branchFan hh hm c leaf b)
    (legalBoth_exists_bool (three_lt_h_to_two_lt hh) rhs))).symm

theorem eval_compileFan {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileFan hh hm c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legalBoth (three_lt_h_to_two_lt hh) b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          Z ⟨(leaf ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩).val * alph h +
              (restrictShift (three_lt_h_to_pos hh) 0 b).val,
            coord_lt (leaf ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩)
              (restrictShift (three_lt_h_to_pos hh) 0 b) (alph_pos h)⟩ =
            true ∧
            Z ⟨(leaf ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩).val * alph h +
                (restrictShift (three_lt_h_to_pos hh) 1 b).val,
              coord_lt (leaf ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩)
                (restrictShift (three_lt_h_to_pos hh) 1 b) (alph_pos h)⟩ =
              true ∧
              Z ⟨(leaf ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩).val *
                    alph h +
                  (restrictShift (three_lt_h_to_pos hh) 2 b).val,
                coord_lt (leaf ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩)
                  (restrictShift (three_lt_h_to_pos hh) 2 b)
                  (alph_pos h)⟩ = true := by
  have hor := eval_orFilter Z (alph h)
    (fun b => isLegalBoth (three_lt_h_to_two_lt hh) rhs b)
    (fun b => branchFan hh hm c leaf b)
    (compileFan hh hm c leaf rhs)
    (compileFan_orFilter hh hm c leaf rhs)
  constructor
  · intro hf
    obtain ⟨b, hp, hb⟩ := hor.mp hf
    obtain ⟨hc, h0, h1, h2⟩ := (eval_branchFan hh hm Z c leaf b).mp hb
    exact ⟨b, (isLegalBoth_true_iff (three_lt_h_to_two_lt hh) rhs b).mp hp,
      hc, h0, h1, h2⟩
  · rintro ⟨b, hleg, hc, h0, h1, h2⟩
    refine hor.mpr ⟨b,
      (isLegalBoth_true_iff (three_lt_h_to_two_lt hh) rhs b).mpr hleg, ?_⟩
    exact (eval_branchFan hh hm Z c leaf b).mpr ⟨hc, h0, h1, h2⟩

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

def fanFormula {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula (Fin (resN L φ * alph (legalH L))) :=
  compileFan hh hm (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

theorem twoBit_lt {h : Nat} (hh : 0 < h) : 2 < alph h :=
  two_lt_alph hh

theorem legalBoth_twoBit_not_one {h : Nat} (hh : 3 < h) :
    ¬ legalBoth (three_lt_h_to_two_lt hh) ⟨2, twoBit_lt (three_lt_h_to_pos hh)⟩
      1 := by
  intro hleg
  have hH := hleg.2
  unfold legalHigh evalBit vecOfFin bit highBasis3 at hH
  have t0 : (2 : Nat).testBit h = false :=
    testBit_of_lt_pow (Nat.lt_trans (by decide : (2 : Nat) < 8)
      (Nat.pow_lt_pow_right (by decide : 1 < 2) hh))
  have t1 : (2 : Nat).testBit (h + 1) = false :=
    testBit_of_lt_pow (Nat.lt_trans (by decide : (2 : Nat) < 16)
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.succ_lt_succ hh)))
  have t2 : (2 : Nat).testBit (h + 2) = false :=
    testBit_of_lt_pow (Nat.lt_trans (by decide : (2 : Nat) < 32)
      (Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.succ_lt_succ (Nat.succ_lt_succ hh))))
  simp [t0, t1, t2] at hH

theorem succHigh_lt {h : Nat} (hh : 3 < h) : 2 ^ (h + 1) < alph h :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) (by
    have : h + 1 < h + h := Nat.add_lt_add_left (three_lt_h_to_one_lt hh) h
    simpa [two_mul] using this)

theorem legalBoth_succHigh_not_one {h : Nat} (hh : 3 < h) :
    ¬ legalBoth (three_lt_h_to_two_lt hh) ⟨2 ^ (h + 1), succHigh_lt hh⟩ 1 := by
  intro hleg
  have hL := hleg.1
  unfold legal3Lin evalBit vecOfFin bit basis3 at hL
  have t0 : (2 ^ (h + 1)).testBit 0 = false := by
    simp [Nat.testBit_two_pow]
  have t1 : (2 ^ (h + 1)).testBit 1 = false := by
    simp [Nat.testBit_two_pow]
    omega
  have t2 : (2 ^ (h + 1)).testBit 2 = false := by
    simp [Nat.testBit_two_pow]
    omega
  simp [t0, t1, t2] at hL

theorem sevenCover_not_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 3 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (sevenCover (n := resN L φ) (three_lt_h_to_pos hh))
      (fanFormula hh (paramM_ge_3 hm) φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileFan hh (paramM_ge_3 hm)
      (sevenCover (n := resN L φ) (three_lt_h_to_pos hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [fanFormula] using htrue)
  obtain ⟨b, hleg, hc, h0, h1s, h2⟩ := he
  have hleg1 : legalBoth (three_lt_h_to_two_lt hh) b 1 := by
    simpa [h1] using hleg
  have hc' := sevenCover_coord (n := resN L φ) (three_lt_h_to_pos hh)
    (resCenter (L := L) φ h3 i) b
  have hlit : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ∨ b.val = 2 ^ legalH L ∨
      b.val = 2 ^ (legalH L + 1) ∨ b.val = 1 + 2 ^ legalH L ∨
        b.val = 2 + 2 ^ (legalH L + 1) := of_decide_eq_true (by
    simpa [hc'] using hc)
  rcases hlit with hb0 | hb1 | hb2 | hbh | hbs | hbd | hbr
  · have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
    exact legal3Lin_zero_not_one (three_lt_h_to_two_lt hh)
      (by simpa [hb] using hleg1.1)
  · have hb : b = lowOne (three_lt_h_to_pos hh) := Fin.ext (by
      simpa [lowOne] using hb1)
    exact legalBoth_lowOne_not_one (three_lt_h_to_two_lt hh)
      (by simpa [hb] using hleg1)
  · have hb : b = ⟨2, twoBit_lt (three_lt_h_to_pos hh)⟩ := Fin.ext hb2
    exact legalBoth_twoBit_not_one hh (by simpa [hb] using hleg1)
  · have hb : b = highBit (three_lt_h_to_pos hh) := Fin.ext (by
      simpa [highBit] using hbh)
    exact legalBoth_highBit_not_one (three_lt_h_to_two_lt hh)
      (by simpa [hb] using hleg1)
  · have hb : b = ⟨2 ^ (legalH L + 1), succHigh_lt hh⟩ := Fin.ext hbs
    exact legalBoth_succHigh_not_one hh (by simpa [hb] using hleg1)
  · have hb : b = dualBit (three_lt_h_to_pos hh) := Fin.ext (by
      simpa [dualBit] using hbd)
    have hsh : (restrictShift (three_lt_h_to_pos hh) 2 b).val =
        4 + 2 ^ (legalH L + 2) := by
      have := restrictShift_dualBit hh (j := 2) (by decide : (2 : Nat) ≤ 2)
      simpa [hb, Nat.pow_succ, Nat.mul_comm, two_mul] using this
    have hcL := sevenCover_coord (n := resN L φ) (three_lt_h_to_pos hh)
      (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩)
      (restrictShift (three_lt_h_to_pos hh) 2 b)
    have hlitL : (restrictShift (three_lt_h_to_pos hh) 2 b).val = 0 ∨
        (restrictShift (three_lt_h_to_pos hh) 2 b).val = 1 ∨
          (restrictShift (three_lt_h_to_pos hh) 2 b).val = 2 ∨
            (restrictShift (three_lt_h_to_pos hh) 2 b).val =
              2 ^ legalH L ∨
              (restrictShift (three_lt_h_to_pos hh) 2 b).val =
                2 ^ (legalH L + 1) ∨
                (restrictShift (three_lt_h_to_pos hh) 2 b).val =
                  1 + 2 ^ legalH L ∨
                  (restrictShift (three_lt_h_to_pos hh) 2 b).val =
                    2 + 2 ^ (legalH L + 1) :=
      of_decide_eq_true (by simpa [hcL] using h2)
    have hne0 : 4 + 2 ^ (legalH L + 2) ≠ 0 :=
      (Nat.add_pos_left (by decide : (0 : Nat) < 4) _).ne'
    have hne1 : 4 + 2 ^ (legalH L + 2) ≠ 1 := by
      have : 0 < 2 ^ (legalH L + 2) := Nat.two_pow_pos _
      omega
    have hne2 : 4 + 2 ^ (legalH L + 2) ≠ 2 := by
      have : 0 < 2 ^ (legalH L + 2) := Nat.two_pow_pos _
      omega
    have hpow4 : 2 ^ (legalH L + 2) = 4 * 2 ^ legalH L := by
      have h4 : (4 : Nat) = 2 ^ 2 := rfl
      rw [h4, ← Nat.pow_add, Nat.add_comm]
    have hneh : 4 + 2 ^ (legalH L + 2) ≠ 2 ^ legalH L := by
      rw [hpow4]; omega
    have hnes : 4 + 2 ^ (legalH L + 2) ≠ 2 ^ (legalH L + 1) := by
      have : 2 ^ (legalH L + 1) = 2 * 2 ^ legalH L := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow4, this]; omega
    have hned : 4 + 2 ^ (legalH L + 2) ≠ 1 + 2 ^ legalH L := by
      rw [hpow4]; omega
    have hner : 4 + 2 ^ (legalH L + 2) ≠ 2 + 2 ^ (legalH L + 1) := by
      have : 2 ^ (legalH L + 1) = 2 * 2 ^ legalH L := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow4, this]; omega
    rcases hlitL with hz | h1b | h2b | hhbit | hsbit | hd | hr
    · exact hne0 (hsh.symm.trans hz)
    · exact hne1 (hsh.symm.trans h1b)
    · exact hne2 (hsh.symm.trans h2b)
    · exact hneh (hsh.symm.trans hhbit)
    · exact hnes (hsh.symm.trans hsbit)
    · exact hned (hsh.symm.trans hd)
    · exact hner (hsh.symm.trans hr)
  · have hb : b.val = 2 + 2 ^ (legalH L + 1) := hbr
    have hmul : (2 + 2 ^ (legalH L + 1)) * 4 =
        8 + 2 ^ (legalH L + 3) := by
      rw [Nat.add_mul]
      have hleft : (2 : Nat) * 4 = 8 := rfl
      have hright : 2 ^ (legalH L + 1) * 4 = 2 ^ (legalH L + 3) := by
        have h4 : (4 : Nat) = 2 ^ 2 := rfl
        rw [h4, ← Nat.pow_add]
      rw [hleft, hright]
    have hlt : 8 + 2 ^ (legalH L + 3) < alph (legalH L) := by
      have hlt' : 8 + 2 ^ (legalH L + 3) < 2 ^ (legalH L + 4) := by
        have hpow : 2 ^ (legalH L + 4) = 2 * 2 ^ (legalH L + 3) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow]
        have h8 : (8 : Nat) = 2 ^ 3 := rfl
        have : 8 < 2 ^ (legalH L + 3) := by
          rw [h8]
          exact Nat.pow_lt_pow_right (by decide : 1 < 2)
            (Nat.lt_add_of_pos_left (three_lt_h_to_pos hh) :
              3 < legalH L + 3)
        omega
      have hle : 2 ^ (legalH L + 4) ≤ 2 ^ (2 * legalH L) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by
          have : 4 ≤ legalH L := Nat.succ_le_of_lt hh
          have : legalH L + 4 ≤ legalH L + legalH L :=
            Nat.add_le_add_left this (legalH L)
          simpa [two_mul] using this)
      exact lt_of_lt_of_le hlt' (by simpa [alph] using hle)
    have hval : (restrictShift (three_lt_h_to_pos hh) 2 b).val =
        8 + 2 ^ (legalH L + 3) := by
      have hb' : b.val = 2 + 2 ^ (legalH L + 1) := hb
      simp [restrictShift, hb']
      rw [hmul]
      exact Nat.mod_eq_of_lt (by simpa [alph] using hlt)
    have hcL := sevenCover_coord (n := resN L φ) (three_lt_h_to_pos hh)
      (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩)
      (restrictShift (three_lt_h_to_pos hh) 2 b)
    have hlitL : (restrictShift (three_lt_h_to_pos hh) 2 b).val = 0 ∨
        (restrictShift (three_lt_h_to_pos hh) 2 b).val = 1 ∨
          (restrictShift (three_lt_h_to_pos hh) 2 b).val = 2 ∨
            (restrictShift (three_lt_h_to_pos hh) 2 b).val =
              2 ^ legalH L ∨
              (restrictShift (three_lt_h_to_pos hh) 2 b).val =
                2 ^ (legalH L + 1) ∨
                (restrictShift (three_lt_h_to_pos hh) 2 b).val =
                  1 + 2 ^ legalH L ∨
                  (restrictShift (three_lt_h_to_pos hh) 2 b).val =
                    2 + 2 ^ (legalH L + 1) :=
      of_decide_eq_true (by simpa [hcL] using h2)
    have hne0 : 8 + 2 ^ (legalH L + 3) ≠ 0 :=
      (Nat.add_pos_left (by decide : (0 : Nat) < 8) _).ne'
    have hx : 0 < 2 ^ (legalH L + 3) := Nat.two_pow_pos _
    have hpow8 : 2 ^ (legalH L + 3) = 8 * 2 ^ legalH L := by
      have h8 : (8 : Nat) = 2 ^ 3 := rfl
      rw [h8, ← Nat.pow_add, Nat.add_comm]
    rcases hlitL with hz | h1b | h2b | hhbit | hsbit | hd | hr
    · exact hne0 (hval.symm.trans hz)
    · have hne1 : 8 + 2 ^ (legalH L + 3) ≠ 1 := by
        have : 7 < 2 ^ (legalH L + 3) :=
          lt_trans (by decide : 7 < 8) (by
            rw [show (8 : Nat) = 2 ^ 3 from rfl]
            exact Nat.pow_lt_pow_right (by decide : 1 < 2)
              (Nat.lt_add_of_pos_left (three_lt_h_to_pos hh) :
                3 < legalH L + 3))
        omega
      exact hne1 (hval.symm.trans h1b)
    · have hne : 8 + 2 ^ (legalH L + 3) ≠ 2 := by
        have : 6 < 2 ^ (legalH L + 3) :=
          lt_trans (by decide : 6 < 8) (by
            rw [show (8 : Nat) = 2 ^ 3 from rfl]
            exact Nat.pow_lt_pow_right (by decide : 1 < 2)
              (Nat.lt_add_of_pos_left (three_lt_h_to_pos hh) :
                3 < legalH L + 3))
        omega
      exact hne (hval.symm.trans h2b)
    · have hne : 8 + 2 ^ (legalH L + 3) ≠ 2 ^ legalH L := by
        rw [hpow8]; omega
      exact hne (hval.symm.trans hhbit)
    · have hne : 8 + 2 ^ (legalH L + 3) ≠ 2 ^ (legalH L + 1) := by
        have h2 : 2 ^ (legalH L + 1) = 2 * 2 ^ legalH L := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow8, h2]; omega
      exact hne (hval.symm.trans hsbit)
    · have hne : 8 + 2 ^ (legalH L + 3) ≠ 1 + 2 ^ legalH L := by
        rw [hpow8]; omega
      exact hne (hval.symm.trans hd)
    · have hne : 8 + 2 ^ (legalH L + 3) ≠ 2 + 2 ^ (legalH L + 1) := by
        have h2 : 2 ^ (legalH L + 1) = 2 * 2 ^ legalH L := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow8, h2]; omega
      exact hne (hval.symm.trans hr)

theorem sevenCover_not_eval_unsatCnf {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 3 < legalH L) :
    Formula.eval
      (sevenCover (n := resN L unsatCnf) (three_lt_h_to_pos hh))
      (fanFormula hh (paramM_ge_3 hm) unsatCnf unsatCnf_is3
        ⟨1, by decide⟩) = false :=
  sevenCover_not_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩
    unsatCnf_rhs1

theorem cheapTwo_not_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 3 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (cheapTwo (n := resN L φ) (three_lt_h_to_pos hh)
        (resCenter (L := L) φ h3 i))
      (fanFormula hh (paramM_ge_3 hm) φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileFan hh (paramM_ge_3 hm)
      (cheapTwo (n := resN L φ) (three_lt_h_to_pos hh)
        (resCenter (L := L) φ h3 i))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [fanFormula] using htrue)
  obtain ⟨b, hleg, hc, h0, h1s, h2⟩ := he
  have hleg1 : legalBoth (three_lt_h_to_two_lt hh) b 1 := by
    simpa [h1] using hleg
  have hne := resCenter_ne_resLeaf (L := L) φ h3 i
    ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩
  have hid := restrictShift_id (three_lt_h_to_pos hh) b
  have hcL := cheapTwo_other (n := resN L φ) (three_lt_h_to_pos hh)
    (resCenter (L := L) φ h3 i)
    (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
    hne.symm (restrictShift (three_lt_h_to_pos hh) 0 b)
  have hlit : (restrictShift (three_lt_h_to_pos hh) 0 b).val = 0 ∨
      (restrictShift (three_lt_h_to_pos hh) 0 b).val = 2 ^ legalH L :=
    of_decide_eq_true (by simpa [hcL] using h0)
  rw [hid] at hlit
  rcases hlit with hz | hhbit
  · have hb0 : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hz
    exact legal3Lin_zero_not_one (three_lt_h_to_two_lt hh)
      (by simpa [hb0] using hleg1.1)
  · have hbh : b = highBit (three_lt_h_to_pos hh) := Fin.ext (by
      simpa [highBit] using hhbit)
    exact legalBoth_highBit_not_one (three_lt_h_to_two_lt hh)
      (by simpa [hbh] using hleg1)

theorem cheapTwo_not_eval_unsatCnf {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 3 < legalH L) :
    Formula.eval
      (cheapTwo (n := resN L unsatCnf) (three_lt_h_to_pos hh)
        (resCenter (L := L) unsatCnf unsatCnf_is3 ⟨1, by decide⟩))
      (fanFormula hh (paramM_ge_3 hm) unsatCnf unsatCnf_is3
        ⟨1, by decide⟩) = false :=
  cheapTwo_not_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩
    unsatCnf_rhs1

/-- Cheaper leftover: center `{0, dualBit}`, leaf `j` lights `{0, dualBit<<j}`. -/
def vdFan {n h : Nat} (_hh : 0 < h) (c l0 l1 l2 : Fin n) :
    Fin (n * alph h) → Bool :=
  fun i =>
    let v := i.val / alph h
    let a := i.val % alph h
    if v = c.val then decide (a = 0 ∨ a = 1 + 2 ^ h)
    else if v = l0.val then decide (a = 0 ∨ a = 1 + 2 ^ h)
    else if v = l1.val then decide (a = 0 ∨ a = 2 + 2 ^ (h + 1))
    else if v = l2.val then decide (a = 0 ∨ a = 4 + 2 ^ (h + 2))
    else decide (a = 0)

private theorem coord_div {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) / A = v.val := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm, Nat.mul_add_div hA,
    Nat.div_eq_of_lt a.isLt, Nat.add_zero]

theorem vdFan_center {n h : Nat} (hh : 0 < h) (c l0 l1 l2 : Fin n)
    (a : Fin (alph h)) :
    vdFan (n := n) hh c l0 l1 l2
        ⟨c.val * alph h + a.val, coord_lt c a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 + 2 ^ h) := by
  unfold vdFan
  have hdiv := coord_div (alph_pos h) c a
  have hmod := coord_mod (alph_pos h) c a
  simp [hdiv, hmod]

theorem vdFan_leaf0 {n h : Nat} (hh : 0 < h) (c l0 l1 l2 : Fin n)
    (hne : l0 ≠ c) (a : Fin (alph h)) :
    vdFan (n := n) hh c l0 l1 l2
        ⟨l0.val * alph h + a.val, coord_lt l0 a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 + 2 ^ h) := by
  unfold vdFan
  have hdiv := coord_div (alph_pos h) l0 a
  have hmod := coord_mod (alph_pos h) l0 a
  have hne' : l0.val ≠ c.val := fun h => hne (Fin.ext h)
  simp [hdiv, hmod, hne']

theorem vdFan_leaf1 {n h : Nat} (hh : 0 < h) (c l0 l1 l2 : Fin n)
    (hne : l1 ≠ c) (hne0 : l1 ≠ l0) (a : Fin (alph h)) :
    vdFan (n := n) hh c l0 l1 l2
        ⟨l1.val * alph h + a.val, coord_lt l1 a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 2 + 2 ^ (h + 1)) := by
  unfold vdFan
  have hdiv := coord_div (alph_pos h) l1 a
  have hmod := coord_mod (alph_pos h) l1 a
  have hnec : l1.val ≠ c.val := fun h => hne (Fin.ext h)
  have hne0' : l1.val ≠ l0.val := fun h => hne0 (Fin.ext h)
  simp [hdiv, hmod, hnec, hne0']

theorem vdFan_leaf2 {n h : Nat} (hh : 0 < h) (c l0 l1 l2 : Fin n)
    (hne : l2 ≠ c) (hne0 : l2 ≠ l0) (hne1 : l2 ≠ l1) (a : Fin (alph h)) :
    vdFan (n := n) hh c l0 l1 l2
        ⟨l2.val * alph h + a.val, coord_lt l2 a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 4 + 2 ^ (h + 2)) := by
  unfold vdFan
  have hdiv := coord_div (alph_pos h) l2 a
  have hmod := coord_mod (alph_pos h) l2 a
  have hnec : l2.val ≠ c.val := fun h => hne (Fin.ext h)
  have hne0' : l2.val ≠ l0.val := fun h => hne0 (Fin.ext h)
  have hne1' : l2.val ≠ l1.val := fun h => hne1 (Fin.ext h)
  simp [hdiv, hmod, hnec, hne0', hne1']

theorem resLeaf_ne {L : Nat} (φ : CNF) {j k : Fin (paramM L)}
    (hne : j ≠ k) : resLeaf L φ j ≠ resLeaf L φ k := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [resLeaf] at hval
  exact hne (Fin.ext hval)

private theorem finMk_ne {n a b : Nat} (ha : a < n) (hb : b < n)
    (h : a ≠ b) : (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ :=
  Fin.ne_of_val_ne (by simpa using h)

theorem vdFan_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 3 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (vdFan (n := resN L φ) (three_lt_h_to_pos hh)
        (resCenter (L := L) φ h3 i)
        (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
        (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩)
        (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩))
      (fanFormula hh (paramM_ge_3 hm) φ h3 i) = true := by
  refine (eval_compileFan hh (paramM_ge_3 hm)
      (vdFan (n := resN L φ) (three_lt_h_to_pos hh)
        (resCenter (L := L) φ h3 i)
        (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
        (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩)
        (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨dualBit (three_lt_h_to_pos hh), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [h1] using legalBoth_dualBit (three_lt_h_to_two_lt hh)
  · have hc := vdFan_center (n := resN L φ) (three_lt_h_to_pos hh)
      (resCenter (L := L) φ h3 i)
      (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩)
      (dualBit (three_lt_h_to_pos hh))
    simpa [dualBit] using hc
  · have hid := restrictShift_id (three_lt_h_to_pos hh)
      (dualBit (three_lt_h_to_pos hh))
    have hne := resCenter_ne_resLeaf (L := L) φ h3 i
      ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩
    rw [hid]
    have hc := vdFan_leaf0 (n := resN L φ) (three_lt_h_to_pos hh)
      (resCenter (L := L) φ h3 i)
      (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩)
      hne.symm (dualBit (three_lt_h_to_pos hh))
    simpa [dualBit] using hc
  · have hsh := restrictShift_dualBit hh (j := 1) (by decide : (1 : Nat) ≤ 2)
    have hne := resCenter_ne_resLeaf (L := L) φ h3 i
      ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩
    have hne0 := resLeaf_ne (L := L) φ
      (finMk_ne (lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm))
        (lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm))
        (by decide : (1 : Nat) ≠ 0))
    have hc := vdFan_leaf1 (n := resN L φ) (three_lt_h_to_pos hh)
      (resCenter (L := L) φ h3 i)
      (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩)
      hne.symm hne0
      (restrictShift (three_lt_h_to_pos hh) 1
        (dualBit (three_lt_h_to_pos hh)))
    simpa [hsh] using hc
  · have hsh := restrictShift_dualBit hh (j := 2) (by decide : (2 : Nat) ≤ 2)
    have hne := resCenter_ne_resLeaf (L := L) φ h3 i
      ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩
    have hne0 := resLeaf_ne (L := L) φ
      (finMk_ne (lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm))
        (lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm))
        (by decide : (2 : Nat) ≠ 0))
    have hne1 := resLeaf_ne (L := L) φ
      (finMk_ne (lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm))
        (lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm))
        (by decide : (2 : Nat) ≠ 1))
    have hc := vdFan_leaf2 (n := resN L φ) (three_lt_h_to_pos hh)
      (resCenter (L := L) φ h3 i)
      (resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) (paramM_ge_3 hm)⟩)
      (resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) (paramM_ge_3 hm)⟩)
      hne.symm hne0 hne1
      (restrictShift (three_lt_h_to_pos hh) 2
        (dualBit (three_lt_h_to_pos hh)))
    have hpow : 2 ^ 2 + 2 ^ (legalH L + 2) = 4 + 2 ^ (legalH L + 2) := by
      simp
    simpa [hsh, hpow] using hc

private theorem honest_eval_fan {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (fanFormula hh hm φ h3 i) = true := by
  refine (eval_compileFan hh hm
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [h0] using legalBoth_zero (three_lt_h_to_two_lt hh)
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (legalH L) + (0 : Nat)) %
          alph (legalH L) = 0) = true
    simpa [Nat.mul_mod_left]
  · have hrest := restrictShift_zero (three_lt_h_to_pos hh) 0
    change decide
        (((resLeaf L φ ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hm⟩).val *
          alph (legalH L) +
          (restrictShift (three_lt_h_to_pos hh) 0
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]
  · have hrest := restrictShift_zero (three_lt_h_to_pos hh) 1
    change decide
        (((resLeaf L φ ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hm⟩).val *
          alph (legalH L) +
          (restrictShift (three_lt_h_to_pos hh) 1
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]
  · have hrest := restrictShift_zero (three_lt_h_to_pos hh) 2
    change decide
        (((resLeaf L φ ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hm⟩).val *
          alph (legalH L) +
          (restrictShift (three_lt_h_to_pos hh) 2
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]

theorem compileFan_leaves_le {n h m : Nat} (hh : 3 < h) (hm : 3 ≤ m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula.leaves (compileFan hh hm c leaf rhs) ≤ alph h * 4 := by
  have hsome := compileFan_orFilter hh hm c leaf rhs
  have hle := orFilter_leaves_le (alph h)
    (fun b => isLegalBoth (three_lt_h_to_two_lt hh) rhs b)
    (fun b => branchFan hh hm c leaf b)
    (compileFan hh hm c leaf rhs) hsome
  have hb : ∀ b, Formula.leaves (branchFan hh hm c leaf b) = 4 := by
    intro b
    have h := andFin_leaves 4 (slotVarFan hh hm c leaf b)
      (branchFan hh hm c leaf b) (branchFan_andFin hh hm c leaf b)
    have hs : ∀ j, Formula.leaves (slotVarFan hh hm c leaf b j) = 1 := by
      intro j
      unfold slotVarFan
      split_ifs <;> rfl
    simpa [h, hs, Fintype.card_fin] using
      (Finset.sum_const_nat (n := 1) fun _ _ => rfl)
  have hsum :
      (∑ b : Fin (alph h), Formula.leaves (branchFan hh hm c leaf b)) =
      alph h * 4 := by
    rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
    simp [Finset.card_univ, Fintype.card_fin]
  exact hle.trans (le_of_eq hsum)

def fanFormulas {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (resN L φ * alph (legalH L))) :=
  fun i => fanFormula hh hm φ h3 i

def fanData {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (fanFormulas hh hm φ h3) (compactBudget (alph (legalH L)))

theorem fanData_valid {L : Nat} (h : 256 ≤ mOf L) (hh : 3 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (fanData hh (paramM_ge_3 h) φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (fanFormulas hh (paramM_ge_3 h) φ h3)
    (compactBudget (alph (legalH L)))
    (compactWeights_pos (resN_pos L φ) (alph_pos _))
    (compactWeights_sum (resN_pos L φ) (alph_pos _)) hM ?_
    (compactBudget_pos (alph_pos _)) (compactBudget_le_one (alph_pos _))
  intro i
  have hle := compactLeaves_le h
  have hA : alph (legalH L) = ROf L := alph_eq_ROf L
  have h4 : 4 ≤ paramM L + 1 := by
    have : 3 ≤ paramM L := paramM_ge_3 h
    omega
  have hleaves : alph (legalH L) * 4 ≤ L := by
    have hfit : alph (legalH L) * (paramM L + 1) ≤ L := by
      simpa [hA, paramM, Nat.mul_comm] using hle
    exact (Nat.mul_le_mul_left _ h4).trans hfit
  exact (compileFan_leaves_le hh (paramM_ge_3 h)
    (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).trans hleaves

private theorem fan_len {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (fanData hh hm φ h3 hM).weights.length =
      resN L φ * alph (legalH L) := by
  simp [fanData, indexedData]

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

private theorem fan_honest_cost {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (fanData hh hm φ h3 hM).cost
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (fan_len hh hm φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph (legalH L)) := by
  unfold Data.cost Data.coordinateWeights
  simp only [fanData, indexedData, List.get_ofFn]
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

private theorem fan_honest_sat_of_rhs0 {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hall0 : ∀ i : Fin φ.length, clauseRhs φ h3 i = 0) :
    (fanData hh hm φ h3 hM).satisfaction
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (fan_len hh hm φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (fanData hh hm φ h3 hM).formulas.length) := by
    simp [fanData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (fanData hh hm φ h3 hM).formulas.length,
      Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (fan_len hh hm φ h3 hM) ▸ i.isLt⟩)
        ((fanData hh hm φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [fanData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
      (fanFormulas hh hm φ h3) (compactBudget (alph (legalH L)))
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val, by
        simpa [fanData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [fanData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [fanData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (fanFormulas hh hm φ h3 ⟨j.val, hj⟩)) ?_).trans
      (honest_eval_fan hh hm φ h3 ⟨j.val, hj⟩ (hall0 ⟨j.val, hj⟩))
    funext v
    exact congrArg (honest (n := resN L φ) (alph_pos (legalH L)))
      (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (fan_len hh hm φ h3 hM) ▸ i.isLt⟩)
        ((fanData hh hm φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem fanData_yes_unit3 {L : Nat} (h : 256 ≤ mOf L)
    (hh : 3 < legalH L) :
    Yes 0 (ofData (fanData hh (paramM_ge_3 h) unit3 unit3_is3 unit3_len)
      (fanData_valid h hh unit3 unit3_is3 unit3_len)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := resN L unit3) (alph_pos (legalH L)) ⟨i.val,
      (fan_len hh (paramM_ge_3 h) unit3 unit3_is3 unit3_len) ▸ i.isLt⟩,
    ?_, ?_⟩
  · have hcost := fan_honest_cost hh (paramM_ge_3 h) unit3 unit3_is3 unit3_len
    have hle : compactBudget (alph (legalH L)) ≤
        (fanData hh (paramM_ge_3 h) unit3 unit3_is3 unit3_len).budget := by
      simp [fanData, indexedData]
    exact hcost.trans_le hle
  · have hsat := fan_honest_sat_of_rhs0 hh (paramM_ge_3 h) unit3
      unit3_is3 unit3_len unit3_all_rhs0
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

def fanFormulaTree {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L) :
    CMMSACodec.Tree :=
  formulaTree
    (compileFan hh hm (paramCenter L) (paramLeaf L) 0)

def fanFormulaEnc {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L) :
    List Bool :=
  CMMSACodec.Tree.encode (fanFormulaTree hh hm)

def fanWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L)
      (ratTree ((1 : Rat) / ((paramN L * ROf L : Nat) : Rat)))))

def fanBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree ((1 : Rat) / (ROf L : Rat)))

def fanFormsEnc {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (z : List Bool) : List Bool :=
  true :: fanFormulaEnc hh hm ++ (true :: clauseOrEnc z ++ [false])

theorem fanFormsEnc_mem_FP {L : Nat} (hh : 3 < legalH L)
    (hm : 3 ≤ paramM L) :
    fanFormsEnc (L := L) hh hm ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: fanFormulaEnc hh hm)) htail

def fanEncFn {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L)
    (z : List Bool) : List Bool :=
  true :: fanWeightsEnc L ++ true :: fanFormsEnc hh hm z ++ fanBudgetEnc L

theorem fanEncFn_mem_FP {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L) :
    fanEncFn (L := L) hh hm ∈ Complexity.FP := by
  have hforms : (fun z => true :: fanFormsEnc hh hm z) ∈ Complexity.FP :=
    mem_FP_comp (fanFormsEnc_mem_FP hh hm) (Cobham.cons_mem_FP true)
  have hleft :
      (fun z => true :: fanWeightsEnc L ++ true :: fanFormsEnc hh hm z) ∈
        Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: fanWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (fanBudgetEnc L))

theorem fanEncFn_ne_id {L : Nat} (hh : 3 < legalH L) (hm : 3 ≤ paramM L) :
    fanEncFn (L := L) hh hm [] ≠ [] := by
  simp [fanEncFn, fanWeightsEnc]

end
end PvNP.RealizableHardness.ActualThreeSatGrassmannFan
