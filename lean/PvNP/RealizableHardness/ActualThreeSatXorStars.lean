import PvNP.RealizableHardness.ActualUnsatPairZeta
import PvNP.RealizableHardness.ActualThreeSatStarFamily
import PvNP.RealizableHardness.ActualRestrictXorCompile

/-!
3SAT-dependent 2-leaf XOR stars at alphabet `alph h = ROf L`.

Each 3-clause becomes a `compileResXor` star on the three polarity
coordinates (`litIndex`), with masks from literal signs.  This is not
the constant 3LIN pair: formulas depend on the source 3CNF.

Unsat CSP value is not claimed to meet `hn_zeta_beats_sigma` (integer
`rho = rofSigma`).  `eight_mul_rofSigma_eq_ROf` records that manuscript
`σ_L = ROf L / 8` when `8 ≤ ROf L`.  `hSrcCmmsa` is not inhabited.
-/
namespace PvNP.RealizableHardness.ActualThreeSatXorStars

open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualThreeSatStarFamily
open ActualThreeSatCmmsaReduce
open ActualRestrictXorCompile
open ActualXorLabel
open ActualFinite3LinStarPCP
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem eight_mul_rofSigma_eq_ROf {L : Nat} (h8 : 8 ≤ ROf L) :
    8 * rofSigma L = ROf L := by
  have hk : 3 ≤ 2 * hOf L (mOf L) :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa [ROf] using h8)
  have hdiv : 8 ∣ ROf L := by
    simpa [ROf] using Nat.pow_dvd_pow (a := 2) hk
  unfold rofSigma
  rw [Nat.div_div_eq_div_mul]
  exact Nat.mul_div_cancel' hdiv

def clausePol (φ : CNF) (h3 : φ.Is3CNF) (i : Fin φ.length) (k : Fin 3) :
    Fin (nPol φ) :=
  let hc := h3 φ[i] (List.get_mem φ i)
  let ℓ := clauseNth φ[i] hc k
  litIndex φ ℓ (lit_var_lt_nVars φ φ[i] ℓ (List.get_mem φ i)
    (List.get_mem φ[i] ⟨k.val, by
      rw [hc]
      exact k.isLt⟩))

def clauseMask {h : Nat} (hh : 0 < h) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Fin 2 → Fin (alph h) :=
  fun j =>
    let hc := h3 φ[i] (List.get_mem φ i)
    let ℓ := clauseNth φ[i] hc j.succ
    if ℓ.sign then ⟨0, alph_pos h⟩ else rhsMask hh 1

def clauseXorFormula {h : Nat} (hh : 0 < h) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length) : Formula (Fin (nPol φ * alph h)) :=
  compileResXor (le_rfl : 2 * h ≤ 2 * h) (clausePol φ h3 i 0)
    (fun j : Fin 2 => clausePol φ h3 i j.succ) (clauseMask hh φ h3 i)

theorem clauseXorFormula_leaves {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (i : Fin φ.length) :
    Formula.leaves (clauseXorFormula hh φ h3 i) = alph h * 3 := by
  simpa [clauseXorFormula] using
    compileResXor_leaves (le_rfl : 2 * h ≤ 2 * h)
      (clausePol φ h3 i 0) (fun j : Fin 2 => clausePol φ h3 i j.succ)
      (clauseMask hh φ h3 i)

def xorFormulas {h : Nat} (hh : 0 < h) (φ : CNF) (h3 : φ.Is3CNF) :
    Fin φ.length → Formula (Fin (nPol φ * alph h)) :=
  fun i => clauseXorFormula hh φ h3 i

noncomputable def xorStarData {h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) : Data :=
  indexedData (compactWeights (nPol φ) (alph h) (nPol_pos φ) (alph_pos h))
    (xorFormulas hh φ h3) (compactBudget (alph h))

theorem xorStarData_valid {L h : Nat} (hh : 0 < h) (φ : CNF)
    (h3 : φ.Is3CNF) (hM : 0 < φ.length) (hleaves : alph h * 3 ≤ L) :
    Valid L (xorStarData hh φ h3 hM) := by
  refine indexedData_valid
    (compactWeights (nPol φ) (alph h) (nPol_pos φ) (alph_pos h))
    (xorFormulas hh φ h3) (compactBudget (alph h))
    (compactWeights_pos (nPol_pos φ) (alph_pos h))
    (compactWeights_sum (nPol_pos φ) (alph_pos h)) hM ?_
    (compactBudget_pos (alph_pos h)) (compactBudget_le_one (alph_pos h))
  intro i
  simpa [xorFormulas, clauseXorFormula_leaves] using hleaves

theorem xorStarData_valid_of_mOf {L : Nat} (h : 256 ≤ mOf L)
    (hh : 0 < hOf L (mOf L)) (φ : CNF) (h3 : φ.Is3CNF)
    (hM : 0 < φ.length) :
    Valid L (xorStarData (h := hOf L (mOf L)) hh φ h3 hM) :=
  xorStarData_valid hh φ h3 hM (by
    rw [alph_eq_ROf, Nat.mul_comm]
    exact three_mul_ROf_le h)

/-- Restatement of the HN integer-rho bound with `8 σ_L = ROf L`. -/
theorem hn_zeta_beats_ROf {L : Nat} (h8 : 8 ≤ ROf L) (hσ : 0 < rofSigma L)
    (zeta : Rat)
    (hz : zeta ≤ (5 : Rat) /
      ((8 : Rat) * (ROf L : Rat) ^ (mOf L + 1))) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * zeta ≤ (5 : Rat) / 8 := by
  have hEq := eight_mul_rofSigma_eq_ROf h8
  have hz' : zeta ≤ (5 : Rat) /
      ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1)) := by
    simpa [hEq] using hz
  exact hn_zeta_beats_sigma L zeta hz' hσ

end PvNP.RealizableHardness.ActualThreeSatXorStars
