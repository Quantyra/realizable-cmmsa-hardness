import PvNP.RealizableHardness.ActualThreeSatOverlap

/-!
Triple restriction chart: DualWindow `legalBoth` plus dummy-leaf
`restrictLow` (half-width), `restrictHigh`, and left-shift `restrictRot`.

Kills Overlap leftover `fourCover {0,1,2^h,1+2^h}` and the cheaper
vertex-dependent 2-hot (centers `{0,1+2^h}`, dummy `{0,2^h}`): shift
sends `1+2^h` to `2+2^{h+1}`, which those palettes do not light.
Sat unit is packed `Yes 0` via label `0`.

A 7-label leftover still covers mixed RHS, so this is not `No σ_L γ_L`
and does not inhabit `hSrcCmmsa`.  Not `if-sat`.  Not `compileOverlap` /
`fourCover` / `vdCover` / `compileMid`.  Checking-transducer `mem_FP` is
not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatRotate

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

def restrictRot {h : Nat} (_hh : 0 < h) (a : Fin (alph h)) : Fin (alph h) :=
  ⟨(a.val * 2) % alph h, Nat.mod_lt _ (alph_pos h)⟩

theorem restrictRot_zero {h : Nat} (hh : 0 < h) :
    restrictRot hh ⟨0, alph_pos h⟩ = ⟨0, alph_pos h⟩ :=
  Fin.ext (by simp [restrictRot])

theorem two_lt_alph {h : Nat} (hh : 0 < h) : 2 < alph h :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) (by
    have : 2 ≤ 2 * h := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hh)
    exact lt_of_lt_of_le (by decide : 1 < 2) this)

theorem restrictRot_one {h : Nat} (hh : 0 < h) :
    restrictRot hh ⟨1, one_lt_alph_of hh⟩ = ⟨2, two_lt_alph hh⟩ := by
  apply Fin.ext
  have hmod : (2 : Nat) % alph h = 2 := Nat.mod_eq_of_lt (two_lt_alph hh)
  simp [restrictRot, hmod]

theorem restrictRot_ne_id {h : Nat} (hh : 0 < h) :
    restrictRot hh ⟨1, one_lt_alph_of hh⟩ ≠ ⟨1, one_lt_alph_of hh⟩ := by
  intro heq
  have : (2 : Nat) = 1 := by
    simpa [restrictRot_one hh] using congrArg Fin.val heq
  exact (by decide : ¬ (2 : Nat) = 1) this

theorem rotDual_val (h : Nat) : (1 + 2 ^ h) * 2 = 2 + 2 ^ (h + 1) := by
  rw [Nat.add_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (2 ^ h)]

theorem rotDual_lt_alph {h : Nat} (hh : 2 < h) :
    2 + 2 ^ (h + 1) < alph h := by
  have hlt : 2 + 2 ^ (h + 1) < 2 ^ (h + 2) := by
    have hpow : 2 ^ (h + 2) = 2 * 2 ^ (h + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have : 2 < 2 ^ (h + 1) := by
      have h2 : (2 : Nat) = 2 ^ 1 := rfl
      rw [h2]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2)
        (Nat.succ_lt_succ (two_lt_h_to_pos hh))
    omega
  have hle : 2 ^ (h + 2) ≤ 2 ^ (2 * h) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by
      have : 2 ≤ h := Nat.succ_le_of_lt (two_lt_h_to_one_lt hh)
      have : h + 2 ≤ h + h := Nat.add_le_add_left this h
      rwa [← two_mul] at this)
  exact lt_of_lt_of_le hlt (by simpa [alph] using hle)

theorem restrictRot_dualBit {h : Nat} (hh : 2 < h) :
    (restrictRot (two_lt_h_to_pos hh) (dualBit (two_lt_h_to_pos hh))).val =
      2 + 2 ^ (h + 1) := by
  have hlt := rotDual_lt_alph hh
  simp [restrictRot, dualBit]
  rw [rotDual_val]
  exact Nat.mod_eq_of_lt (by simpa [alph] using hlt)

def slotVarRotate {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Fin 4 → Formula (Fin (n * alph h)) :=
  fun i =>
    if i.val = 0 then varAt (alph_pos h) c b
    else if i.val = 1 then
      varAt (alph_pos h) (leaf ⟨0, hm⟩) (restrictLow (midK_le hh) b)
    else if i.val = 2 then
      varAt (alph_pos h) (leaf ⟨0, hm⟩) (restrictHigh hh b)
    else
      varAt (alph_pos h) (leaf ⟨0, hm⟩) (restrictRot hh b)

def branchRotate {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    Formula (Fin (n * alph h)) :=
  Option.get (andFin 4 (slotVarRotate hh hm c leaf b))
    (andFin_isSome (by decide : 0 < 4) _)

theorem branchRotate_andFin {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (b : Fin (alph h)) :
    andFin 4 (slotVarRotate hh hm c leaf b) =
      some (branchRotate hh hm c leaf b) :=
  (Option.some_get (andFin_isSome (by decide : 0 < 4) _)).symm

theorem fin4_eq {j : Fin 4} :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
  have : j.val < 4 := j.isLt
  omega

theorem eval_branchRotate {n h m : Nat} (hh : 0 < h) (hm : 0 < m)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (b : Fin (alph h)) :
    Formula.eval Z (branchRotate hh hm c leaf b) = true ↔
      Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
        Z ⟨(leaf ⟨0, hm⟩).val * alph h +
            (restrictLow (midK_le hh) b).val,
          coord_lt (leaf ⟨0, hm⟩) (restrictLow (midK_le hh) b)
            (alph_pos h)⟩ = true ∧
          Z ⟨(leaf ⟨0, hm⟩).val * alph h + (restrictHigh hh b).val,
            coord_lt (leaf ⟨0, hm⟩) (restrictHigh hh b) (alph_pos h)⟩ =
            true ∧
            Z ⟨(leaf ⟨0, hm⟩).val * alph h + (restrictRot hh b).val,
              coord_lt (leaf ⟨0, hm⟩) (restrictRot hh b) (alph_pos h)⟩ =
              true := by
  have hand := eval_andFin Z 4 (slotVarRotate hh hm c leaf b)
    (branchRotate hh hm c leaf b) (branchRotate_andFin hh hm c leaf b)
  constructor
  · intro hf
    have hall := hand.mp hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [slotVarRotate, varAt, Formula.eval] using hall ⟨0, by decide⟩
    · simpa [slotVarRotate, varAt, Formula.eval] using hall ⟨1, by decide⟩
    · simpa [slotVarRotate, varAt, Formula.eval] using hall ⟨2, by decide⟩
    · simpa [slotVarRotate, varAt, Formula.eval] using hall ⟨3, by decide⟩
  · rintro ⟨hc, hlo, hhi, hro⟩
    refine hand.mpr ?_
    intro j
    rcases fin4_eq (j := j) with h0 | h1 | h2 | h3
    · have : j = ⟨0, by decide⟩ := Fin.ext h0
      simpa [this, slotVarRotate, varAt, Formula.eval] using hc
    · have : j = ⟨1, by decide⟩ := Fin.ext h1
      simpa [this, slotVarRotate, varAt, Formula.eval] using hlo
    · have : j = ⟨2, by decide⟩ := Fin.ext h2
      simpa [this, slotVarRotate, varAt, Formula.eval] using hhi
    · have : j = ⟨3, by decide⟩ := Fin.ext h3
      simpa [this, slotVarRotate, varAt, Formula.eval] using hro

def compileRotate {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula (Fin (n * alph h)) :=
  Option.get
    (orFilter (alph h) (fun b => isLegalBoth hh rhs b)
      (fun b => branchRotate (two_lt_h_to_pos hh) hm c leaf b))
    (orFilter_isSome (fun b => isLegalBoth hh rhs b)
      (fun b => branchRotate (two_lt_h_to_pos hh) hm c leaf b)
      (legalBoth_exists_bool hh rhs))

theorem compileRotate_orFilter {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    orFilter (alph h) (fun b => isLegalBoth hh rhs b)
        (fun b => branchRotate (two_lt_h_to_pos hh) hm c leaf b) =
      some (compileRotate hh hm c leaf rhs) :=
  (Option.some_get (orFilter_isSome (fun b => isLegalBoth hh rhs b)
    (fun b => branchRotate (two_lt_h_to_pos hh) hm c leaf b)
    (legalBoth_exists_bool hh rhs))).symm

theorem eval_compileRotate {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (Z : Fin (n * alph h) → Bool) (c : Fin n) (leaf : Fin m → Fin n)
    (rhs : ZMod 2) :
    Formula.eval Z (compileRotate hh hm c leaf rhs) = true ↔
      ∃ b : Fin (alph h), legalBoth hh b rhs ∧
        Z ⟨c.val * alph h + b.val, coord_lt c b (alph_pos h)⟩ = true ∧
          Z ⟨(leaf ⟨0, hm⟩).val * alph h +
              (restrictLow (midK_le (two_lt_h_to_pos hh)) b).val,
            coord_lt (leaf ⟨0, hm⟩)
              (restrictLow (midK_le (two_lt_h_to_pos hh)) b)
              (alph_pos h)⟩ = true ∧
            Z ⟨(leaf ⟨0, hm⟩).val * alph h +
                (restrictHigh (two_lt_h_to_pos hh) b).val,
              coord_lt (leaf ⟨0, hm⟩)
                (restrictHigh (two_lt_h_to_pos hh) b) (alph_pos h)⟩ = true ∧
              Z ⟨(leaf ⟨0, hm⟩).val * alph h +
                  (restrictRot (two_lt_h_to_pos hh) b).val,
                coord_lt (leaf ⟨0, hm⟩)
                  (restrictRot (two_lt_h_to_pos hh) b) (alph_pos h)⟩ =
                true := by
  have hor := eval_orFilter Z (alph h) (fun b => isLegalBoth hh rhs b)
    (fun b => branchRotate (two_lt_h_to_pos hh) hm c leaf b)
    (compileRotate hh hm c leaf rhs)
    (compileRotate_orFilter hh hm c leaf rhs)
  constructor
  · intro hf
    obtain ⟨b, hp, hb⟩ := hor.mp hf
    obtain ⟨hc, hlo, hhi, hro⟩ :=
      (eval_branchRotate (two_lt_h_to_pos hh) hm Z c leaf b).mp hb
    exact ⟨b, (isLegalBoth_true_iff hh rhs b).mp hp, hc, hlo, hhi, hro⟩
  · rintro ⟨b, hleg, hc, hlo, hhi, hro⟩
    refine hor.mpr ⟨b, (isLegalBoth_true_iff hh rhs b).mpr hleg, ?_⟩
    exact (eval_branchRotate (two_lt_h_to_pos hh) hm Z c leaf b).mpr
      ⟨hc, hlo, hhi, hro⟩

private theorem coord_mod {n A : Nat} (hA : 0 < A) (v : Fin n) (a : Fin A) :
    (v.val * A + a.val) % A = a.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]

def rotFormula {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula (Fin (resN L φ * alph (legalH L))) :=
  compileRotate hh hm (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)

theorem fourCover_not_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (fourCover (n := resN L φ) (legalH_pos_of hh))
      (rotFormula hh (paramM_pos_of hm) φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileRotate hh (paramM_pos_of hm)
      (fourCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [rotFormula] using htrue)
  obtain ⟨b, hleg, hc, hlo, hhi, hro⟩ := he
  have hleg1 : legalBoth hh b 1 := by simpa [h1] using hleg
  have hc' := fourCover_coord (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) b
  have hlit : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ^ legalH L ∨
      b.val = 1 + 2 ^ legalH L := of_decide_eq_true (by
    simpa [hc'] using hc)
  rcases hlit with hb0 | hb1 | hbh | hbd
  · have hb : b = ⟨0, alph_pos (legalH L)⟩ := Fin.ext hb0
    exact legal3Lin_zero_not_one hh (by simpa [hb] using hleg1.1)
  · have hb : b = lowOne (legalH_pos_of hh) := Fin.ext (by
      simpa [lowOne] using hb1)
    exact legalBoth_lowOne_not_one hh (by simpa [hb] using hleg1)
  · have hb : b = highBit (legalH_pos_of hh) := Fin.ext (by
      simpa [highBit] using hbh)
    exact legalBoth_highBit_not_one hh (by simpa [hb] using hleg1)
  · have hb : b = dualBit (legalH_pos_of hh) := Fin.ext (by
      simpa [dualBit] using hbd)
    have hrot : (restrictRot (legalH_pos_of hh) b).val =
        2 + 2 ^ (legalH L + 1) := by
      simpa [hb] using restrictRot_dualBit hh
    have hcL := fourCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ ⟨0, paramM_pos_of hm⟩)
      (restrictRot (legalH_pos_of hh) b)
    have hlitL : (restrictRot (legalH_pos_of hh) b).val = 0 ∨
        (restrictRot (legalH_pos_of hh) b).val = 1 ∨
          (restrictRot (legalH_pos_of hh) b).val = 2 ^ legalH L ∨
            (restrictRot (legalH_pos_of hh) b).val = 1 + 2 ^ legalH L :=
      of_decide_eq_true (by simpa [hcL] using hro)
    have hne0 : 2 + 2 ^ (legalH L + 1) ≠ 0 :=
      (Nat.add_pos_left (by decide : (0 : Nat) < 2) _).ne'
    have hne1 : 2 + 2 ^ (legalH L + 1) ≠ 1 := by
      have : 0 < 2 ^ (legalH L + 1) := Nat.two_pow_pos _
      omega
    have hpow : 2 ^ (legalH L + 1) = 2 * 2 ^ legalH L := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hneh : 2 + 2 ^ (legalH L + 1) ≠ 2 ^ legalH L := by
      omega
    have hned : 2 + 2 ^ (legalH L + 1) ≠ 1 + 2 ^ legalH L := by
      omega
    rcases hlitL with hz | h1b | hhbit | hd
    · exact hne0 (hrot.symm.trans hz)
    · exact hne1 (hrot.symm.trans h1b)
    · exact hneh (hrot.symm.trans hhbit)
    · exact hned (hrot.symm.trans hd)

theorem fourCover_not_eval_unsatCnf {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Formula.eval
      (fourCover (n := resN L unsatCnf) (legalH_pos_of hh))
      (rotFormula hh (paramM_pos_of hm) unsatCnf unsatCnf_is3
        ⟨1, by decide⟩) = false :=
  fourCover_not_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩
    unsatCnf_rhs1

/-- Cheaper leftover from Overlap: centers `{0, dualBit}`, others `{0, 2^h}`. -/
def cheapTwo {n h : Nat} (hh : 0 < h) (c : Fin n) : Fin (n * alph h) → Bool :=
  fun i =>
    if i.val / alph h = c.val then
      decide (i.val % alph h = 0 ∨ i.val % alph h = 1 + 2 ^ h)
    else
      decide (i.val % alph h = 0 ∨ i.val % alph h = 2 ^ h)

theorem cheapTwo_center {n h : Nat} (hh : 0 < h) (c : Fin n)
    (a : Fin (alph h)) :
    cheapTwo (n := n) hh c
        ⟨c.val * alph h + a.val, coord_lt c a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 + 2 ^ h) := by
  unfold cheapTwo
  have hdiv : (c.val * alph h + a.val) / alph h = c.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (alph_pos h),
      Nat.div_eq_of_lt a.isLt]
    simp
  have hmod := coord_mod (alph_pos h) c a
  simp [hdiv, hmod]

theorem cheapTwo_other {n h : Nat} (hh : 0 < h) (c v : Fin n)
    (hv : v ≠ c) (a : Fin (alph h)) :
    cheapTwo (n := n) hh c
        ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 2 ^ h) := by
  unfold cheapTwo
  have hdiv : (v.val * alph h + a.val) / alph h = v.val := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (alph_pos h),
      Nat.div_eq_of_lt a.isLt]
    simp
  have hmod := coord_mod (alph_pos h) v a
  have hne : v.val ≠ c.val := fun h => hv (Fin.ext h)
  simp [hdiv, hmod, hne]

theorem cheapTwo_not_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (cheapTwo (n := resN L φ) (legalH_pos_of hh)
        (resCenter (L := L) φ h3 i))
      (rotFormula hh (paramM_pos_of hm) φ h3 i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have he := (eval_compileRotate hh (paramM_pos_of hm)
      (cheapTwo (n := resN L φ) (legalH_pos_of hh)
        (resCenter (L := L) φ h3 i))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mp
    (by simpa [rotFormula] using htrue)
  obtain ⟨b, hleg, hc, hlo, hhi, hro⟩ := he
  have hleg1 : legalBoth hh b 1 := by simpa [h1] using hleg
  have hne := resCenter_ne_resLeaf (L := L) φ h3 i ⟨0, paramM_pos_of hm⟩
  have hcL := cheapTwo_other (n := resN L φ) (legalH_pos_of hh)
    (resCenter (L := L) φ h3 i) (resLeaf L φ ⟨0, paramM_pos_of hm⟩) hne.symm
    (restrictLow (midK_le (legalH_pos_of hh)) b)
  have hlit : (restrictLow (midK_le (legalH_pos_of hh)) b).val = 0 ∨
      (restrictLow (midK_le (legalH_pos_of hh)) b).val = 2 ^ legalH L :=
    of_decide_eq_true (by simpa [hcL] using hlo)
  -- 1-legal labels have low 3XOR = 1, so restrictLow (preserves bits 0,1,2)
  -- cannot be 0 (3XOR 0) and cannot be 2^h (low bits all 0).
  have hlin := hleg1.1
  have hpres : legal3Lin (two_lt_h_to_one_lt hh)
      (restrictLow (midK_le (legalH_pos_of hh)) b) 1 :=
    (legal3Lin_restrictLow_mid hh b 1).mpr hlin
  rcases hlit with hz | hhbit
  · have hb0 : restrictLow (midK_le (legalH_pos_of hh)) b =
        ⟨0, alph_pos (legalH L)⟩ := Fin.ext hz
    exact legal3Lin_zero_not_one hh (by simpa [hb0] using hpres)
  · have hbh : restrictLow (midK_le (legalH_pos_of hh)) b =
        highBit (legalH_pos_of hh) := Fin.ext (by simpa [highBit] using hhbit)
    exact legal3Lin_highBit_not_one hh (by simpa [hbh] using hpres)

theorem cheapTwo_not_eval_unsatCnf {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Formula.eval
      (cheapTwo (n := resN L unsatCnf) (legalH_pos_of hh)
        (resCenter (L := L) unsatCnf unsatCnf_is3 ⟨1, by decide⟩))
      (rotFormula hh (paramM_pos_of hm) unsatCnf unsatCnf_is3
        ⟨1, by decide⟩) = false :=
  cheapTwo_not_eval_rhs1 hm hh unsatCnf unsatCnf_is3 ⟨1, by decide⟩
    unsatCnf_rhs1

def sevenCover {n h : Nat} (_hh : 0 < h) : Fin (n * alph h) → Bool :=
  fun i =>
    let a := i.val % alph h
    decide (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 2 ^ h ∨ a = 2 ^ (h + 1) ∨
      a = 1 + 2 ^ h ∨ a = 2 + 2 ^ (h + 1))

theorem sevenCover_coord {n h : Nat} (hh : 0 < h) (v : Fin n)
    (a : Fin (alph h)) :
    sevenCover (n := n) hh ⟨v.val * alph h + a.val, coord_lt v a (alph_pos h)⟩ =
      decide (a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 2 ^ h ∨
        a.val = 2 ^ (h + 1) ∨ a.val = 1 + 2 ^ h ∨
          a.val = 2 + 2 ^ (h + 1)) := by
  unfold sevenCover
  have hmod := coord_mod (alph_pos h) v a
  simp [hmod]

theorem sevenCover_eval_rhs1 {L : Nat} (hm : 256 ≤ mOf L)
    (hh : 2 < legalH L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h1 : clauseRhs φ h3 i = 1) :
    Formula.eval
      (sevenCover (n := resN L φ) (legalH_pos_of hh))
      (rotFormula hh (paramM_pos_of hm) φ h3 i) = true := by
  refine (eval_compileRotate hh (paramM_pos_of hm)
      (sevenCover (n := resN L φ) (legalH_pos_of hh))
      (resCenter (L := L) φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨dualBit (legalH_pos_of hh), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [h1] using legalBoth_dualBit hh
  · have hc := sevenCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resCenter (L := L) φ h3 i) (dualBit (legalH_pos_of hh))
    simpa [dualBit] using hc
  · have hrest := restrictLow_dualBit_eq_one hh
    rw [hrest]
    have hc := sevenCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ ⟨0, paramM_pos_of hm⟩) (lowOne (legalH_pos_of hh))
    simpa [lowOne] using hc
  · have hrest := restrictHigh_dualBit hh
    rw [hrest]
    have hc := sevenCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ ⟨0, paramM_pos_of hm⟩) (highBit (legalH_pos_of hh))
    simpa [highBit] using hc
  · have hrot := restrictRot_dualBit hh
    have hc := sevenCover_coord (n := resN L φ) (legalH_pos_of hh)
      (resLeaf L φ ⟨0, paramM_pos_of hm⟩)
      (restrictRot (legalH_pos_of hh) (dualBit (legalH_pos_of hh)))
    simpa [hrot] using hc

private theorem honest_eval_rot {L : Nat} (hh : 2 < legalH L)
    (hm : 0 < paramM L) (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length)
    (h0 : clauseRhs φ h3 i = 0) :
    Formula.eval
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (rotFormula hh hm φ h3 i) = true := by
  refine (eval_compileRotate hh hm
      (honest (n := resN L φ) (alph_pos (legalH L)))
      (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).mpr
    ⟨⟨0, alph_pos (legalH L)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [h0] using legalBoth_zero hh
  · change decide
        (((resCenter (L := L) φ h3 i).val * alph (legalH L) + (0 : Nat)) %
          alph (legalH L) = 0) = true
    simpa [Nat.mul_mod_left]
  · have hrest := restrictLow_zero (midK_le (legalH_pos_of hh))
    change decide
        (((resLeaf L φ ⟨0, hm⟩).val * alph (legalH L) +
          (restrictLow (midK_le (legalH_pos_of hh))
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]
  · have hrest := restrictHigh_zero (legalH_pos_of hh)
    change decide
        (((resLeaf L φ ⟨0, hm⟩).val * alph (legalH L) +
          (restrictHigh (legalH_pos_of hh)
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]
  · have hrest := restrictRot_zero (legalH_pos_of hh)
    change decide
        (((resLeaf L φ ⟨0, hm⟩).val * alph (legalH L) +
          (restrictRot (legalH_pos_of hh)
            (⟨0, alph_pos (legalH L)⟩ : Fin (alph (legalH L)))).val) %
          alph (legalH L) = 0) = true
    simp [hrest, Nat.mul_mod_left]

theorem compileRotate_leaves_le {n h m : Nat} (hh : 2 < h) (hm : 0 < m)
    (c : Fin n) (leaf : Fin m → Fin n) (rhs : ZMod 2) :
    Formula.leaves (compileRotate hh hm c leaf rhs) ≤ alph h * 4 := by
  have hsome := compileRotate_orFilter hh hm c leaf rhs
  have hle := orFilter_leaves_le (alph h) (fun b => isLegalBoth hh rhs b)
    (fun b => branchRotate (two_lt_h_to_pos hh) hm c leaf b)
    (compileRotate hh hm c leaf rhs) hsome
  have hb : ∀ b, Formula.leaves
      (branchRotate (two_lt_h_to_pos hh) hm c leaf b) = 4 := by
    intro b
    have h := andFin_leaves 4 (slotVarRotate (two_lt_h_to_pos hh) hm c leaf b)
      (branchRotate (two_lt_h_to_pos hh) hm c leaf b)
      (branchRotate_andFin (two_lt_h_to_pos hh) hm c leaf b)
    have hs : ∀ j, Formula.leaves
        (slotVarRotate (two_lt_h_to_pos hh) hm c leaf b j) = 1 := by
      intro j
      unfold slotVarRotate
      split_ifs <;> rfl
    simpa [h, hs, Fintype.card_fin] using
      (Finset.sum_const_nat (n := 1) fun _ _ => rfl)
  have hsum :
      (∑ b : Fin (alph h), Formula.leaves
        (branchRotate (two_lt_h_to_pos hh) hm c leaf b)) =
      alph h * 4 := by
    rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, nsmul_eq_mul]
    simp [Finset.card_univ, Fintype.card_fin]
  exact hle.trans (le_of_eq hsum)

def rotFormulas {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (resN L φ * alph (legalH L))) :=
  fun i => rotFormula hh hm φ h3 i

def rotData {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) : Data :=
  indexedData
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (rotFormulas hh hm φ h3) (compactBudget (alph (legalH L)))

theorem rotData_valid {L : Nat} (h : 256 ≤ mOf L) (hh : 2 < legalH L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    Valid L (rotData hh (paramM_pos_of h) φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
    (rotFormulas hh (paramM_pos_of h) φ h3)
    (compactBudget (alph (legalH L)))
    (compactWeights_pos (resN_pos L φ) (alph_pos _))
    (compactWeights_sum (resN_pos L φ) (alph_pos _)) hM ?_
    (compactBudget_pos (alph_pos _)) (compactBudget_le_one (alph_pos _))
  intro i
  have hle := compactLeaves_le h
  have hA : alph (legalH L) = ROf L := alph_eq_ROf L
  have h4 : 4 ≤ paramM L + 1 := by
    have : 3 ≤ paramM L :=
      le_trans (by decide : 3 ≤ 256) (by simpa [paramM] using h)
    omega
  have hleaves : alph (legalH L) * 4 ≤ L := by
    have hfit : alph (legalH L) * (paramM L + 1) ≤ L := by
      simpa [hA, paramM, Nat.mul_comm] using hle
    exact (Nat.mul_le_mul_left _ h4).trans hfit
  exact (compileRotate_leaves_le hh (paramM_pos_of h)
    (resCenter φ h3 i) (resLeaf L φ) (clauseRhs φ h3 i)).trans hleaves

private theorem rot_len {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (rotData hh hm φ h3 hM).weights.length =
      resN L φ * alph (legalH L) := by
  simp [rotData, indexedData]

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

private theorem rot_honest_cost {L : Nat} (hh : 2 < legalH L)
    (hm : 0 < paramM L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length) :
    (rotData hh hm φ h3 hM).cost
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (rot_len hh hm φ h3 hM) ▸ i.isLt⟩) =
      compactBudget (alph (legalH L)) := by
  unfold Data.cost Data.coordinateWeights
  simp only [rotData, indexedData, List.get_ofFn]
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

private theorem rot_honest_sat_of_rhs0 {L : Nat} (hh : 2 < legalH L)
    (hm : 0 < paramM L) (φ : CNF) (h3 : φ.Is3CNF) (hM : 0 < φ.length)
    (hall0 : ∀ i : Fin φ.length, clauseRhs φ h3 i = 0) :
    (rotData hh hm φ h3 hM).satisfaction
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
        (rot_len hh hm φ h3 hM) ▸ i.isLt⟩) = 1 := by
  haveI : Nonempty (Fin (rotData hh hm φ h3 hM).formulas.length) := by
    simp [rotData, indexedData]
    exact ⟨⟨0, hM⟩⟩
  unfold Data.satisfaction
  have hall : ∀ j : Fin (rotData hh hm φ h3 hM).formulas.length,
      Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (rot_len hh hm φ h3 hM) ▸ i.isLt⟩)
        ((rotData hh hm φ h3 hM).indexedFormulas j) = true := by
    intro j
    have hj : j.val < φ.length := by
      simpa [rotData, indexedData] using j.isLt
    have heval := indexedData_eval
      (compactWeights (resN L φ) (alph (legalH L)) (resN_pos L φ) (alph_pos _))
      (rotFormulas hh hm φ h3) (compactBudget (alph (legalH L)))
      (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val, by
        simpa [rotData, indexedData] using i.isLt⟩)
      ⟨j.val, hj⟩
    have hjFin : j = ⟨j.val, by simpa [rotData, indexedData] using j.isLt⟩ :=
      Fin.ext rfl
    rw [hjFin, Data.indexedFormulas]
    simp only [rotData, indexedData] at heval ⊢
    rw [heval]
    refine (congrArg (fun x => Formula.eval x
        (rotFormulas hh hm φ h3 ⟨j.val, hj⟩)) ?_).trans
      (honest_eval_rot hh hm φ h3 ⟨j.val, hj⟩ (hall0 ⟨j.val, hj⟩))
    funext v
    exact congrArg (honest (n := resN L φ) (alph_pos (legalH L)))
      (Fin.ext (by simp))
  rw [show (fun j => Formula.eval
        (fun i => honest (n := resN L φ) (alph_pos (legalH L)) ⟨i.val,
          (rot_len hh hm φ h3 hM) ▸ i.isLt⟩)
        ((rotData hh hm φ h3 hM).indexedFormulas j)) = fun _ => true from
    funext hall]
  exact average_true

theorem rotData_yes_unit3 {L : Nat} (h : 256 ≤ mOf L)
    (hh : 2 < legalH L) :
    Yes 0 (ofData (rotData hh (paramM_pos_of h) unit3 unit3_is3 unit3_len)
      (rotData_valid h hh unit3 unit3_is3 unit3_len)) := by
  dsimp [Yes]
  rw [ofData_data]
  refine ⟨fun i => honest (n := resN L unit3) (alph_pos (legalH L)) ⟨i.val,
      (rot_len hh (paramM_pos_of h) unit3 unit3_is3 unit3_len) ▸ i.isLt⟩,
    ?_, ?_⟩
  · have hcost := rot_honest_cost hh (paramM_pos_of h) unit3 unit3_is3 unit3_len
    have hle : compactBudget (alph (legalH L)) ≤
        (rotData hh (paramM_pos_of h) unit3 unit3_is3 unit3_len).budget := by
      simp [rotData, indexedData]
    exact hcost.trans_le hle
  · have hsat := rot_honest_sat_of_rhs0 hh (paramM_pos_of h) unit3
      unit3_is3 unit3_len unit3_all_rhs0
    exact ((by norm_num : (1 : Rat) - 0 ≤ 1).trans_eq hsat.symm)

def rotFormulaTree {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    CMMSACodec.Tree :=
  formulaTree
    (compileRotate hh hm (paramCenter L) (paramLeaf L) 0)

def rotFormulaEnc {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    List Bool :=
  CMMSACodec.Tree.encode (rotFormulaTree hh hm)

def rotWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L)
      (ratTree ((1 : Rat) / ((paramN L * ROf L : Nat) : Rat)))))

def rotBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree ((1 : Rat) / (ROf L : Rat)))

def rotFormsEnc {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (z : List Bool) : List Bool :=
  true :: rotFormulaEnc hh hm ++ (true :: clauseOrEnc z ++ [false])

theorem rotFormsEnc_mem_FP {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    rotFormsEnc (L := L) hh hm ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: rotFormulaEnc hh hm)) htail

def rotEncFn {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L)
    (z : List Bool) : List Bool :=
  true :: rotWeightsEnc L ++ true :: rotFormsEnc hh hm z ++ rotBudgetEnc L

theorem rotEncFn_mem_FP {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    rotEncFn (L := L) hh hm ∈ Complexity.FP := by
  have hforms : (fun z => true :: rotFormsEnc hh hm z) ∈ Complexity.FP :=
    mem_FP_comp (rotFormsEnc_mem_FP hh hm) (Cobham.cons_mem_FP true)
  have hleft :
      (fun z => true :: rotWeightsEnc L ++ true :: rotFormsEnc hh hm z) ∈
        Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: rotWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (rotBudgetEnc L))

theorem rotEncFn_ne_id {L : Nat} (hh : 2 < legalH L) (hm : 0 < paramM L) :
    rotEncFn (L := L) hh hm [] ≠ [] := by
  simp [rotEncFn, rotWeightsEnc]

end
end PvNP.RealizableHardness.ActualThreeSatRotate
