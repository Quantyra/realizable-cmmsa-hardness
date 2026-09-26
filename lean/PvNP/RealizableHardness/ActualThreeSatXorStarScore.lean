import PvNP.RealizableHardness.ActualThreeSatXorStars
import PvNP.RealizableHardness.ActualUnsatPairZeta

/-!
3SAT-dependent XOR `Star`s (shared polarity vertices) and the HN integer-rho
bound at `zeta = 0`.

`zero_zeta_meets_hn` shows `zeta = 0` satisfies `hn_zeta_beats_sigma`.
`xorUnsat` is the (stronger) statement that every labeling fails some
clause XOR star; under that hypothesis the uniform score is `< 1`.
3SAT-unsat does **not** imply `xorUnsat` (3OR vs 3XOR), so this module
does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatXorStarScore

open Complexity.SAT
open ActualHeadlineParameters
open ActualBitRestriction
open ActualThreeSatStarFamily
open ActualThreeSatCmmsaReduce
open ActualThreeSatXorStars
open ActualXorLabel
open ActualFinite3LinStarPCP
open StarListDecoding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

def clauseXorStar {h : Nat} (hh : 0 < h) (φ : CNF) (h3 : φ.Is3CNF)
    (i : Fin φ.length)
    (hsep : ∀ j : Fin 2, clausePol φ h3 i 0 ≠ clausePol φ h3 i j.succ) :
    Star (Fin (nPol φ)) (fun _ => Fin (alph h)) 2 where
  center := clausePol φ h3 i 0
  leaf := fun j => clausePol φ h3 i j.succ
  projection := fun j a => xorFin a (clauseMask hh φ h3 i j)
  separated := hsep

/-- Every labeling fails at least one clause XOR star. -/
def xorUnsat {h : Nat} (hh : 0 < h) (φ : CNF) (h3 : φ.Is3CNF)
    (hsep : ∀ i, ∀ j : Fin 2, clausePol φ h3 i 0 ≠ clausePol φ h3 i j.succ) :
    Prop :=
  ∀ l : Labeling (fun _ : Fin (nPol φ) => Fin (alph h)),
    ∃ i : Fin φ.length, ¬ (clauseXorStar hh φ h3 i (hsep i)).accepts l

def uniformP {n : Nat} (hn : 0 < n) : Fin n → ℝ := fun _ => (1 : ℝ) / n

theorem uniformP_nonneg {n : Nat} (hn : 0 < n) (i : Fin n) :
    0 ≤ uniformP hn i :=
  div_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- `zeta = 0` meets the HN integer-rho bound. -/
theorem zero_zeta_meets_hn {L : Nat} (_hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * (0 : Rat) ≤ (5 : Rat) / 8 := by
  simp
  norm_num

theorem zero_zeta_le_hn_premise {L : Nat} (hσ : 0 < rofSigma L) :
    (0 : Rat) ≤ (5 : Rat) /
      ((8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1)) := by
  have hdenpos : (0 : Rat) <
      (8 : Rat) * ((8 * rofSigma L : Nat) : Rat) ^ (mOf L + 1) :=
    mul_pos (by norm_num)
      (pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (by decide : 0 < 8) hσ)) _)
  exact div_nonneg (by norm_num) hdenpos.le

theorem zero_zeta_hn_zeta_beats_sigma {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * (0 : Rat) ≤ (5 : Rat) / 8 :=
  hn_zeta_beats_sigma L 0 (zero_zeta_le_hn_premise hσ) hσ

end
end PvNP.RealizableHardness.ActualThreeSatXorStarScore
