import PvNP.RealizableHardness.ActualGrassmannDualStar

/-!
LeafLabel / `RespectsAt` folding of the Grassmann dual-restriction star.

A dual label `respectsAt` a 3LIN row when its pairing with `e0+e1+e2`
equals the row RHS (the standard-basis `LeafLabel` condition on
`F2^{2h}`).  Local alphabets are nonempty: the zero functional respects
RHS `0`, and the `e0^*` functional respects RHS `1`.

The unsat pair is one `k = 3` dual-restriction star whose two leaves are
required to `respectsAt` RHS `0` and `1`.  Restriction recovers the first
three dual coordinates, so no labeling can accept.  The family's actual
unsat CSP value is `0`, which meets `hn_zeta_beats_sigma`.  This is not
a 3SAT reduction and does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannLeafFold

open ActualHeadlineParameters
open ActualBitRestriction
open ActualVecLabel
open ActualGrassmannDualStar
open ActualThreeSatStarFamily
open ActualThreeSatXorStars
open StarListDecoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Dual-chart `RespectsAt` for a 3LIN row on `e0+e1+e2`. -/
abbrev respectsAt {h : Nat} (hh : 1 < h) (a : Fin (alph h)) (rhs : ZMod 2) : Prop :=
  legal3Lin hh a rhs

theorem three_le_two_mul {h : Nat} (hh : 1 < h) : 3 ≤ 2 * h :=
  le_of_lt (three_lt_two_mul hh)

theorem one_lt_alph {h : Nat} (hh : 0 < h) : 1 < alph h :=
  Nat.one_lt_two_pow (Nat.mul_pos (by decide : 0 < 2) hh).ne'

theorem respectsAt_zero {h : Nat} (hh : 1 < h) :
    respectsAt hh ⟨0, alph_pos h⟩ 0 := by
  simp [respectsAt, legal3Lin, evalBit, vecOfFin_zero]

theorem respectsAt_one {h : Nat} (hh : 1 < h) :
    respectsAt hh ⟨1, one_lt_alph (lt_trans Nat.zero_lt_one hh)⟩ 1 := by
  unfold respectsAt legal3Lin evalBit vecOfFin bit basis3
  have t0 : (1 : Nat).testBit 0 = true := rfl
  have t1 : (1 : Nat).testBit 1 = false := rfl
  have t2 : (1 : Nat).testBit 2 = false := rfl
  simp [t0, t1, t2]

/-- `k = 3` dual-restriction star on the three 3LIN variables. -/
def leafFoldStar {h : Nat} (hh : 1 < h) :
    Star (Fin 3) (fun _ => Fin (alph h)) 2 :=
  dualStar (three_le_two_mul hh) 0 pairLeaf pair_separated

def leafFoldAccepts {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) : Prop :=
  (leafFoldStar hh).accepts l ∧
    respectsAt hh (l (pairLeaf ⟨0, by decide⟩)) 0 ∧
      respectsAt hh (l (pairLeaf ⟨1, by decide⟩)) 1

private theorem evalBit_center_of_leaf {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h)))
    (hacc : (leafFoldStar hh).accepts l) (i : Fin 2) (j : Fin 3) :
    evalBit (l 0) (basis3 hh j) = evalBit (l (pairLeaf i)) (basis3 hh j) := by
  have hj : (basis3 hh j).val < 3 := j.isLt
  have hrest :=
    evalBit_restrictLow (three_le_two_mul hh) (l (pairLeaf i)) (basis3 hh j) hj
  have hacc_i : restrictLow (three_le_two_mul hh) (l (pairLeaf i)) = l 0 :=
    hacc i
  exact (congrArg (fun a => evalBit a (basis3 hh j)) hacc_i).symm.trans hrest

private theorem legal3Lin_center_of_leaf {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h)))
    (hacc : (leafFoldStar hh).accepts l) (i : Fin 2) (rhs : ZMod 2) :
    legal3Lin hh (l 0) rhs ↔ legal3Lin hh (l (pairLeaf i)) rhs := by
  simp only [legal3Lin]
  rw [evalBit_center_of_leaf hh l hacc i 0,
    evalBit_center_of_leaf hh l hacc i 1,
    evalBit_center_of_leaf hh l hacc i 2]

/-- No LeafLabel-folded labeling accepts the unsat-pair restriction star. -/
theorem leafFold_unsat {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    ¬ leafFoldAccepts hh l := by
  intro ⟨hacc, h0, h1⟩
  have hz : legal3Lin hh (l 0) 0 :=
    (legal3Lin_center_of_leaf hh l hacc ⟨0, by decide⟩ 0).mpr h0
  have ho : legal3Lin hh (l 0) 1 :=
    (legal3Lin_center_of_leaf hh l hacc ⟨1, by decide⟩ 1).mpr h1
  exact legal3Lin_not_both hh (l 0) ⟨hz, ho⟩

noncomputable def leafFoldScore {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) : ℝ :=
  if leafFoldAccepts hh l then 1 else 0

/-- Actual unsat CSP value of the LeafLabel-folded family is `0`. -/
theorem leafFoldScore_eq_zero {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    leafFoldScore hh l = 0 := by
  unfold leafFoldScore
  rw [ite_eq_right (leafFold_unsat hh l)]

theorem leafFoldScore_le_zero {h : Nat} (hh : 1 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    leafFoldScore hh l ≤ 0 :=
  (leafFoldScore_eq_zero hh l).le

def leafFoldZeta : Rat := 0

theorem leafFoldZeta_le_hn_premise {L : Nat} (hσ : 0 < rofSigma L) :
    leafFoldZeta ≤ (5 : Rat) /
      ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1)) := by
  have hdenpos : (0 : Rat) <
      (8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1) :=
    mul_pos (by norm_num)
      (pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (by decide : 0 < 8) hσ)) _)
  exact div_nonneg (by norm_num) hdenpos.le

/-- The family's actual unsat value `0` meets integer-rho HN. -/
theorem leafFold_hn_zeta_beats_sigma {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * leafFoldZeta ≤ (5 : Rat) / 8 :=
  hn_zeta_beats_sigma L leafFoldZeta (leafFoldZeta_le_hn_premise hσ) hσ

theorem leafFold_hn_zeta_beats_ROf {L : Nat} (h8 : 8 ≤ ROf L) (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * leafFoldZeta ≤ (5 : Rat) / 8 :=
  hn_zeta_beats_ROf h8 hσ leafFoldZeta (by
    have hdenpos : (0 : Rat) <
        (8 : Rat) * (ROf L : Rat) ^ (mOf L + 1) :=
      mul_pos (by norm_num)
        (pow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 8) h8)) _)
    exact div_nonneg (by norm_num) hdenpos.le)

end
end PvNP.RealizableHardness.ActualGrassmannLeafFold
