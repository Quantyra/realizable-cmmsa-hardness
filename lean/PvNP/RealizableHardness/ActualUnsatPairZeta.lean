import PvNP.RealizableHardness.ActualFinite3LinStarPCP
import PvNP.RealizableHardness.StarListDecoding

/-!
Unsat 3LIN pair as 2-leaf XOR stars on `Fin (alph h)`.

A single labeling satisfies at most one of the two stars, so CSP value
`zeta = 1/2`.  With list-decoding slack `rho = 1/8` (the fraction
`rofSigma / ROf` at manuscript parameters) one has
`(8 * rho)^(2+1) * zeta = 1/2 ≤ 5/8`, which is the
`witness_mass_le_three_quarters` hypothesis for arity 2.

`hn_zeta_beats_sigma` uses integer `rho = rofSigma` and is a different
scaling; this file does not claim that bound, and does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualUnsatPairZeta

open ActualBitRestriction
open ActualXorLabel
open ActualFinite3LinStarPCP
open StarListDecoding
open ActualHeadlineParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

theorem xorFin_one_ne {h : Nat} (hh : 0 < h) (a : Fin (alph h)) :
    xorFin a (rhsMask hh 1) ≠ a := by
  intro hEq
  have hval : a.val.xor 1 = a.val := by
    have := congrArg Fin.val hEq
    simpa [xorFin, rhsMask] using this
  have hx : (a.val.xor 1).xor a.val = a.val.xor a.val :=
    congrArg (fun n => n.xor a.val) hval
  have h1 : (a.val.xor 1).xor a.val = 1 := by
    have hcomm : (a.val.xor 1).xor a.val = a.val.xor (a.val.xor 1) :=
      Nat.xor_comm _ _
    have hassoc : a.val.xor (a.val.xor 1) = (a.val.xor a.val).xor 1 :=
      (Nat.xor_assoc a.val a.val 1).symm
    have hself : (a.val.xor a.val).xor 1 = (0 : Nat).xor 1 :=
      congrArg (fun n => n.xor 1) (Nat.xor_self a.val)
    exact hcomm.trans (hassoc.trans (hself.trans (Nat.zero_xor 1)))
  have h0 : a.val.xor a.val = 0 := Nat.xor_self _
  exact zero_ne_one ((hx.trans h0).symm.trans h1)

def xorStar {h : Nat} (hh : 0 < h) (q : Fin 2) :
    Star (Fin 3) (fun _ => Fin (alph h)) 2 where
  center := 0
  leaf := fun i => i.succ
  projection := fun i a => xorFin a (rowMask hh q i)
  separated := fun i => by
    intro h
    have : (0 : Fin 3) = i.succ := h
    exact Nat.succ_ne_zero i.val (congrArg Fin.val this).symm

theorem xorStar_not_both {h : Nat} (hh : 0 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    ¬ ((xorStar hh 0).accepts l ∧ (xorStar hh 1).accepts l) := by
  intro ⟨h0, h1⟩
  have h00 : xorFin (l ⟨1, by decide⟩) (rowMask hh 0 ⟨0, by decide⟩) = l 0 :=
    h0 ⟨0, by decide⟩
  have hmask0 : rowMask hh 0 ⟨0, by decide⟩ = ⟨0, alph_pos h⟩ := by
    simp [rowMask, rhsMask, unsatPair]
  have hl1 : l ⟨1, by decide⟩ = l 0 := by
    rw [hmask0, xorFin_zero] at h00
    exact h00
  have h10 : xorFin (l ⟨1, by decide⟩) (rowMask hh 1 ⟨0, by decide⟩) = l 0 :=
    h1 ⟨0, by decide⟩
  have hmask1 : rowMask hh 1 ⟨0, by decide⟩ = rhsMask hh 1 := by
    simp [rowMask, unsatPair]
  rw [hmask1, hl1] at h10
  exact xorFin_one_ne hh (l 0) h10

def pairP : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

theorem pairP_nonneg (q : Fin 2) : 0 ≤ pairP q := by
  unfold pairP
  exact div_nonneg (by norm_num) (by norm_num)

theorem pairP_sum : ∑ q : Fin 2, pairP q = 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_one]
  simp [pairP]
  norm_num

theorem xorStar_score_le_half {h : Nat} (hh : 0 < h)
    (l : Labeling (fun _ : Fin 3 => Fin (alph h))) :
    score pairP (xorStar hh) l ≤ (1 : ℝ) / 2 := by
  unfold score eventMass pairP
  rw [Fin.sum_univ_succ, Fin.sum_univ_one]
  have hnot := xorStar_not_both hh l
  by_cases h0 : (xorStar hh 0).accepts l
  · have h1 : ¬ (xorStar hh 1).accepts l := fun h1 => hnot ⟨h0, h1⟩
    simp [h0, h1]
  · simp [h0]
    split_ifs <;> norm_num

/-- List-decoding parameter endpoint at `rho = 1/8`, `zeta = 1/2`, arity 2. -/
theorem eighth_rho_half_zeta :
    ((8 : ℝ) * (1 / 8)) ^ (2 + 1) * ((1 : ℝ) / 2) ≤ (5 : ℝ) / 8 := by
  norm_num

theorem eighth_rho_half_zeta_any_arity (m : Nat) :
    ((8 : ℝ) * (1 / 8)) ^ (m + 1) * ((1 : ℝ) / 2) ≤ (5 : ℝ) / 8 := by
  simp
  norm_num

end
end PvNP.RealizableHardness.ActualUnsatPairZeta
