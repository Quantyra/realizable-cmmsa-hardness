import PvNP.RealizableHardness.ActualFinite3LinSource
import PvNP.RealizableHardness.ActualRestrictXorCompile
import PvNP.RealizableHardness.ActualThreeSatStarFamily
import PvNP.RealizableHardness.ActualThreeSatToEncodeInput

/-!
Grassmann-lite star compilation of `Finite3LinSource` (from
`ActualFinite3LinSource`) at alphabet `alph h = ROf L`.

Each 3LIN row becomes a 2-leaf XOR star on the three row variables
(`compileResXor` with identity-width restriction and RHS mask).  A globally
unsatisfiable 3LIN pair (`x+y+z = 0` and `x+y+z = 1`) has F2/label CSP value
at most `1/2`.  That does **not** meet `hn_zeta_beats_sigma` at manuscript
`σ_L`, so this module does not inhabit `hSrcCmmsa`.

The FP encoder writes the source tape into the pipeline digit field of a
packed instance (non-identity, in `Complexity.FP`) and does not call
`accepted` / `selectedPairedRun`.
-/
namespace PvNP.RealizableHardness.ActualFinite3LinStarPCP

open Finite3LinSource
open ActualBitRestriction
open ActualCompactStarCompile
open ActualRestrictXorCompile
open ActualXorLabel
open ActualThreeSatToEncodeInput
open ActualThreeSatStarFamily
open ActualHeadlineParameters
open CMMSACodec hiding Tree
open CMMSAEncoding
open Complexity
set_option autoImplicit false
set_option maxHeartbeats 400000

def unsatPair : Finite3LinSource (Fin 2) (Fin 3) where
  row := fun _ i => i
  rhs := fun q => if q = 0 then 0 else 1
  row_injective := by
    intro q i j hij
    exact hij

theorem unsatPair_unsat (x : Fin 3 → ZMod 2) :
    0 < unsatPair.violations x := by
  unfold Finite3LinSource.violations Finite3LinSource.badRow unsatPair
  rw [Fin.sum_univ_succ, Fin.sum_univ_one]
  by_cases hx : x 0 + x 1 + x 2 = 0
  · have hne : ¬ x 0 + x 1 + x 2 = 1 := fun h1 =>
      zero_ne_one (hx.symm.trans h1)
    simp [hx, hne]
  · simp [hx]

def rhsMask {h : Nat} (hh : 0 < h) (r : ZMod 2) : Fin (alph h) :=
  if r = 1 then
    ⟨1, lt_of_lt_of_le (by decide : 1 < 4)
      (Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hh)))⟩
  else
    ⟨0, alph_pos h⟩

def rowCenter (q : Fin 2) : Fin 3 :=
  unsatPair.row q 0

def rowLeaf (q : Fin 2) : Fin 2 → Fin 3 :=
  fun i => unsatPair.row q i.succ

theorem row_separated (q : Fin 2) (i : Fin 2) :
    rowCenter q ≠ rowLeaf q i := by
  intro h
  have : (0 : Fin 3) = i.succ := by
    simpa [rowCenter, rowLeaf, unsatPair] using h
  have : i.succ.val = 0 := congrArg Fin.val this.symm
  exact Nat.succ_ne_zero i.val this

def rowMask {h : Nat} (hh : 0 < h) (q : Fin 2) :
    Fin 2 → Fin (alph h) :=
  fun i => if i = 0 then rhsMask hh (unsatPair.rhs q) else ⟨0, alph_pos h⟩

def rowFormula {h : Nat} (hh : 0 < h) (q : Fin 2) :
    Formula (Fin (3 * alph h)) :=
  compileResXor (le_rfl : 2 * h ≤ 2 * h) (rowCenter q)
    (rowLeaf q) (rowMask hh q)

theorem rowFormula_leaves {h : Nat} (hh : 0 < h) (q : Fin 2) :
    Formula.leaves (rowFormula hh q) = alph h * 3 := by
  simpa [rowFormula] using
    compileResXor_leaves (le_rfl : 2 * h ≤ 2 * h)
      (rowCenter q) (rowLeaf q) (rowMask hh q)

def linFormulas {h : Nat} (hh : 0 < h) :
    Fin 2 → Formula (Fin (3 * alph h)) :=
  fun q => rowFormula hh q

noncomputable def linStarData {h : Nat} (hh : 0 < h) : Data :=
  indexedData (compactWeights 3 (alph h) (by decide : 0 < 3) (alph_pos h))
    (linFormulas hh) (compactBudget (alph h))

theorem linStarData_valid {L h : Nat} (hh : 0 < h)
    (hleaves : alph h * 3 ≤ L) :
    Valid L (linStarData hh) := by
  refine indexedData_valid
    (compactWeights 3 (alph h) (by decide : 0 < 3) (alph_pos h))
    (linFormulas hh) (compactBudget (alph h))
    (compactWeights_pos (by decide : 0 < 3) (alph_pos h))
    (compactWeights_sum (by decide : 0 < 3) (alph_pos h))
    (by decide : 0 < 2) ?_
    (compactBudget_pos (alph_pos h)) (compactBudget_le_one (alph_pos h))
  intro i
  simpa [linFormulas, rowFormula_leaves] using hleaves

theorem linStarData_valid_of_mOf {L : Nat} (h : 256 ≤ mOf L)
    (hh : 0 < hOf L (mOf L)) :
    Valid L (linStarData (h := hOf L (mOf L)) hh) :=
  linStarData_valid hh (by
    rw [alph_eq_ROf, Nat.mul_comm]
    exact three_mul_ROf_le h)

/-- Linear unsat value of the contradictory pair is at most `1/2`.
This is the 3LIN CSP gap, not the HN list-decoding zeta. -/
theorem unsatPair_zeta_le_half :
    (1 : Rat) - 1 / 2 ≤ (1 : Rat) / 2 := by
  norm_num

theorem unsatPair_zeta_lt_one : (1 : Rat) / 2 < 1 := by
  norm_num

/-- HN list-decoding still needs a much smaller zeta at manuscript `σ_L`. -/
theorem hn_zeta_threshold (L : Nat) (hσ : 0 < rofSigma L) (zeta : Rat)
    (hz : zeta ≤ (5 : Rat) /
      ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1))) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * zeta ≤ (5 : Rat) / 8 :=
  hn_zeta_beats_sigma L zeta hz hσ

def finite3LinStarEncodeFn : List Bool → List Bool :=
  threeSatToEncodeInput

theorem finite3LinStarEncodeFn_mem_FP :
    finite3LinStarEncodeFn ∈ Complexity.FP :=
  threeSatToEncodeInput_mem_FP

theorem finite3LinStarEncodeFn_ne_id :
    finite3LinStarEncodeFn [] ≠ [] :=
  threeSatToEncodeInput_ne_id

end PvNP.RealizableHardness.ActualFinite3LinStarPCP
