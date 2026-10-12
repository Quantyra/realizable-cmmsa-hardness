import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
import PvNP.RealizableHardness.GrassmannCounting

/-!
Finite-character proof infrastructure for the universal append spectral
contract.  The average here is the actual unconditional append operator.
No Booleanity is assumed.  The contract is imported only as its target type;
this file is intended to construct its inhabitant from finite Fourier and
finite-rank counting lemmas.
-/

namespace PvNP.RealizableHardness.ActualFiniteAppendSpectral47

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-! ### Change of basis on Fourier coefficients

The trace-pairing identity is the finite-matrix form of MZ24 A.8/A.9.
These lemmas are for arbitrary real functions, not only rank-image
indicators.
-/

theorem pairing_eq_trace_transpose_mul {n d : Nat}
    (Y M : BinaryMatrix n d) :
    pairing Y M = Matrix.trace (Y.transpose * M) := by
  change (∑ i : Fin n, ∑ j : Fin d, Y i j * M i j) =
    ∑ i : Fin d, ∑ j : Fin n, Y j i * M j i
  rw [Finset.sum_comm]

theorem pairing_mul_right_transpose {n d : Nat}
    (Y M : BinaryMatrix n d) (U : BinaryMatrix d d) :
    pairing (Y * U.transpose) M = pairing Y (M * U) := by
  rw [pairing_eq_trace_transpose_mul, pairing_eq_trace_transpose_mul]
  calc
    (Matrix.transpose (Y * U.transpose) * M).trace =
        (U * (Y.transpose * M)).trace := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = ((Y.transpose * M) * U).trace := by
          exact Matrix.trace_mul_comm U (Y.transpose * M)
    _ = (Y.transpose * (M * U)).trace := by rw [Matrix.mul_assoc]

/-- Fourier coefficients are invariant under the dual right action whenever
the original function is invariant under all two-sided basis changes. -/
theorem fourierCoeff_mul_right_transpose_eq
    {n d : Nat} (F : BinaryMatrix n d → Real)
    (basisInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (Z : BinaryMatrix n d) (U V : BinaryMatrix d d)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    fourierCoeff F (Z * U.transpose) = fourierCoeff F Z := by
  classical
  have hchar (M : BinaryMatrix n d) :
      BinaryMatrixFourier.character (Z * U.transpose) M =
        BinaryMatrixFourier.character Z (M * U) := by
    change (if pairing (Z * U.transpose) M = 0 then 1 else -1) =
      if pairing Z (M * U) = 0 then 1 else -1
    rw [pairing_mul_right_transpose Z M U]
  let e : BinaryMatrix n d ≃ BinaryMatrix n d :=
    { toFun := fun M => M * U
      invFun := fun M => M * V
      left_inv := by
        intro M
        change (M * U) * V = M
        calc
          (M * U) * V = M * (U * V) := by rw [Matrix.mul_assoc]
          _ = M := by rw [hUV, Matrix.mul_one]
      right_inv := by
        intro M
        change (M * V) * U = M
        calc
          (M * V) * U = M * (V * U) := by rw [Matrix.mul_assoc]
          _ = M := by rw [hVU, Matrix.mul_one] }
  unfold fourierCoeff uniformMean
  simp_rw [hchar]
  have hchange :
      (∑ M : BinaryMatrix n d,
          F (M * U) * BinaryMatrixFourier.character Z (M * U)) =
        ∑ M : BinaryMatrix n d,
          F M * BinaryMatrixFourier.character Z M := by
    exact Equiv.sum_comp e (fun M =>
      F M * BinaryMatrixFourier.character Z M)
  have hfun : ∀ M : BinaryMatrix n d,
      F M * BinaryMatrixFourier.character Z (M * U) =
        F (M * U) * BinaryMatrixFourier.character Z (M * U) := by
    intro M
    rw [basisInv M U V hUV hVU]
  simp_rw [hfun]
  rw [hchange]

/-- Right multiplication of a frequency by an invertible transpose preserves
its matrix rank. -/
theorem rank_mul_right_transpose_eq
    {n d : Nat} (Z : BinaryMatrix n d) (U V : BinaryMatrix d d)
    (hUV : U * V = 1) :
    (Z * U.transpose).rank = Z.rank := by
  exact Matrix.rank_mul_eq_left_of_isUnit_det U.transpose Z
    (Matrix.isUnit_det_transpose U (Matrix.isUnit_det_of_right_inverse hUV))

/-- General basis invariance for every Fourier rank projection (MZ24 A.10).
This is the functional-level statement required before applying the spectral
calculation to arbitrary real `F`.
-/
theorem rankProjection_mul_right_eq
    {n d i : Nat} (F : BinaryMatrix n d → Real)
    (basisInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (M : BinaryMatrix n d) (U V : BinaryMatrix d d)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    rankProjection i F (M * U) = rankProjection i F M := by
  classical
  let e : BinaryMatrix n d ≃ BinaryMatrix n d :=
    { toFun := fun Z => Z * U.transpose
      invFun := fun Z => Z * V.transpose
      left_inv := by
        intro Z
        change (Z * U.transpose) * V.transpose = Z
        calc
          (Z * U.transpose) * V.transpose =
              Z * (U.transpose * V.transpose) := by rw [Matrix.mul_assoc]
          _ = Z * (V * U).transpose := by rw [← Matrix.transpose_mul]
          _ = Z := by rw [hVU, Matrix.transpose_one, Matrix.mul_one]
      right_inv := by
        intro Z
        change (Z * V.transpose) * U.transpose = Z
        calc
          (Z * V.transpose) * U.transpose =
              Z * (V.transpose * U.transpose) := by rw [Matrix.mul_assoc]
          _ = Z * (U * V).transpose := by rw [← Matrix.transpose_mul]
          _ = Z := by rw [hUV, Matrix.transpose_one, Matrix.mul_one] }
  have hrank (Z : BinaryMatrix n d) : (e Z).rank = Z.rank := by
    exact rank_mul_right_transpose_eq Z U V hUV
  have hchar (Z : BinaryMatrix n d) :
      BinaryMatrixFourier.character Z (M * U) =
        BinaryMatrixFourier.character (e Z) M := by
    change (if pairing Z (M * U) = 0 then 1 else -1) =
      if pairing (Z * U.transpose) M = 0 then 1 else -1
    rw [(pairing_mul_right_transpose Z M U).symm]
  unfold rankProjection
  simp_rw [hchar]
  rw [Finset.sum_filter, Finset.sum_filter]
  have hpoint (Z : BinaryMatrix n d) :
      (if Z.rank = i then
        fourierCoeff F Z * BinaryMatrixFourier.character (e Z) M else 0) =
      (if (e Z).rank = i then
        fourierCoeff F (e Z) * BinaryMatrixFourier.character (e Z) M else 0) := by
    rw [hrank Z]
    have hcoeff := fourierCoeff_mul_right_transpose_eq F basisInv Z U V hUV hVU
    have hcoeff' : fourierCoeff F Z = fourierCoeff F (e Z) := by
      simpa [e] using hcoeff.symm
    rw [hcoeff']
  calc
    (∑ Z : BinaryMatrix n d,
        if Z.rank = i then
          fourierCoeff F Z * BinaryMatrixFourier.character (e Z) M else 0)
        = ∑ Z : BinaryMatrix n d,
            if (e Z).rank = i then
              fourierCoeff F (e Z) * BinaryMatrixFourier.character (e Z) M else 0 := by
                apply Finset.sum_congr rfl
                intro Z _
                exact hpoint Z
    _ = ∑ Z : BinaryMatrix n d,
          if Z.rank = i then
            fourierCoeff F Z * BinaryMatrixFourier.character Z M else 0 := by
              exact Equiv.sum_comp e (fun Z =>
                if Z.rank = i then
                  fourierCoeff F Z * BinaryMatrixFourier.character Z M else 0)

/-! ### Actual append expansion and energy

The surviving frequencies are exactly those whose appended block vanishes.
This section deliberately uses `appendAverage_character`, whose law is
uniform over all appended matrices, not a conditional full-rank law.
-/

def appendedFrequencyPart {n c s : Nat} (Z : BinaryMatrix n (c + s)) :
    BinaryMatrix n s := (appendBinaryMatrixEquiv n c s).symm Z |>.2

def baseFrequencyPart {n c s : Nat} (Z : BinaryMatrix n (c + s)) :
    BinaryMatrix n c := (appendBinaryMatrixEquiv n c s).symm Z |>.1

theorem appendAverage_rankProjection_surviving_sum
    {n c s i : Nat} (F : BinaryMatrix n (c + s) → Real)
    (M : BinaryMatrix n c) :
    appendAverage (rankProjection i F) M =
      ∑ Z ∈ (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
          (fun Z => Z.rank = i),
        if appendedFrequencyPart Z = 0 then
          fourierCoeff F Z *
            BinaryMatrixFourier.character (baseFrequencyPart Z) M
        else 0 := by
  rw [appendAverage_rankProjection_sum]
  apply Finset.sum_congr rfl
  intro Z hZ
  rw [appendAverage_character]
  by_cases hW : ((appendBinaryMatrixEquiv n c s).symm Z).2 = 0
  · simp [appendedFrequencyPart, baseFrequencyPart, hW]
  · simp [appendedFrequencyPart, hW]

/-- The two-character correlation for the unconditional append experiment.
It is the ordinary orthogonality of the retained base frequencies, with no
rank condition on the actual appended matrix.
-/
theorem appendAverage_character_pair
    {n c s : Nat} (Z Z' : BinaryMatrix n (c + s)) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (BinaryMatrixFourier.character Z) M *
        appendAverage (BinaryMatrixFourier.character Z') M) =
      if Z = Z' ∧ appendedFrequencyPart Z = 0 then 1 else 0 := by
  classical
  let e := appendBinaryMatrixEquiv n c s
  let Y := (e.symm Z).1
  let W := (e.symm Z).2
  let Y' := (e.symm Z').1
  let W' := (e.symm Z').2
  have hZ : appendBinaryMatrix Y W = Z := by
    change e (e.symm Z) = Z
    exact e.apply_symm_apply Z
  have hZ' : appendBinaryMatrix Y' W' = Z' := by
    change e (e.symm Z') = Z'
    exact e.apply_symm_apply Z'
  have hOp (M : BinaryMatrix n c) :
      appendAverage (BinaryMatrixFourier.character Z) M =
        if W = 0 then BinaryMatrixFourier.character Y M else 0 := by
    simpa [e, Y, W] using appendAverage_character Z M
  have hOp' (M : BinaryMatrix n c) :
      appendAverage (BinaryMatrixFourier.character Z') M =
        if W' = 0 then BinaryMatrixFourier.character Y' M else 0 := by
    simpa [e, Y', W'] using appendAverage_character Z' M
  have hParts : Z = Z' ↔ Y = Y' ∧ W = W' := by
    constructor
    · intro hz
      have hp := congrArg e.symm hz
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨hy, hw⟩
      calc
        Z = appendBinaryMatrix Y W := hZ.symm
        _ = appendBinaryMatrix Y' W' := by simp [hy, hw]
        _ = Z' := hZ'
  have hPart : appendedFrequencyPart Z = W := by
    simp [appendedFrequencyPart, e, W]
  simp_rw [hOp, hOp']
  by_cases hW : W = 0 <;> by_cases hW' : W' = 0
  · have hEq : Z = Z' ↔ Y = Y' := by
      constructor
      · intro hz
        have hp := congrArg e.symm hz
        exact congrArg Prod.fst hp
      · intro hy
        calc
          Z = appendBinaryMatrix Y W := hZ.symm
          _ = appendBinaryMatrix Y' W' := by simp [hW, hW', hy]
          _ = Z' := hZ'
    have horth := BinaryMatrixFourier.character_orthogonality Y Y'
    calc
      uniformMean (fun M : BinaryMatrix n c =>
          (if W = 0 then BinaryMatrixFourier.character Y M else 0) *
            (if W' = 0 then BinaryMatrixFourier.character Y' M else 0)) =
        uniformMean (fun M : BinaryMatrix n c =>
          BinaryMatrixFourier.character Y M * BinaryMatrixFourier.character Y' M) := by
            simp [hW, hW']
      _ = if Y = Y' then 1 else 0 := horth
      _ = if Z = Z' ∧ appendedFrequencyPart Z = 0 then 1 else 0 := by
        simp [hPart, hW, hEq]
  · have hbad : ¬ (Z = Z' ∧ appendedFrequencyPart Z = 0) := by
      rintro ⟨hzz, hzero⟩
      have hp := congrArg e.symm hzz
      have hw : W = W' := congrArg Prod.snd hp
      have hWzero : W = 0 := hPart.symm.trans hzero
      exact hW' (hw.symm ▸ hWzero)
    simp [uniformMean, hW, hW', hbad]
  · have hbad : ¬ (Z = Z' ∧ appendedFrequencyPart Z = 0) := by
      rintro ⟨_, hzero⟩
      have hWzero : W = 0 := hPart.symm.trans hzero
      exact hW hWzero
    simp [uniformMean, hW, hW', hbad]
  · have hbad : ¬ (Z = Z' ∧ appendedFrequencyPart Z = 0) := by
      rintro ⟨_, hzero⟩
      have hWzero : W = 0 := hPart.symm.trans hzero
      exact hW hWzero
    simp [uniformMean, hW, hW', hbad]

/-- Exact diagonal energy identity for a single Fourier rank after the actual
append average.  This separates the analytic operator step from the finite
rank-fibre counting step below.
-/
theorem appendAverage_rankProjection_energy_eq
    {n c s i : Nat} (F : BinaryMatrix n (c + s) → Real) :
    uniformMean (fun M : BinaryMatrix n c =>
      (appendAverage (rankProjection i F) M) ^ 2) =
      ∑ Z ∈ (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
          (fun Z => Z.rank = i),
        if appendedFrequencyPart Z = 0 then (fourierCoeff F Z) ^ 2 else 0 := by
  classical
  let S := (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
    (fun Z => Z.rank = i)
  let term (Z : BinaryMatrix n (c + s)) (M : BinaryMatrix n c) :=
    fourierCoeff F Z * appendAverage (BinaryMatrixFourier.character Z) M
  have hexp (M : BinaryMatrix n c) :
      appendAverage (rankProjection i F) M = ∑ Z ∈ S, term Z M := by
    simpa [S, term] using appendAverage_rankProjection_sum F M
  have hsquare (M : BinaryMatrix n c) :
      (∑ Z ∈ S, term Z M) ^ 2 =
        ∑ Z ∈ S, ∑ Z' ∈ S, term Z M * term Z' M := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro Z hZ
    rw [Finset.mul_sum]
  have hcross (Z Z' : BinaryMatrix n (c + s)) :
      uniformMean (fun M : BinaryMatrix n c => term Z M * term Z' M) =
        if Z = Z' ∧ appendedFrequencyPart Z = 0 then
          (fourierCoeff F Z) ^ 2 else 0 := by
    have hpoint (M : BinaryMatrix n c) :
        term Z M * term Z' M =
          (fourierCoeff F Z * fourierCoeff F Z') *
            (appendAverage (BinaryMatrixFourier.character Z) M *
              appendAverage (BinaryMatrixFourier.character Z') M) := by
      dsimp [term]
      ring
    rw [show (fun M : BinaryMatrix n c => term Z M * term Z' M) =
        (fun M => (fourierCoeff F Z * fourierCoeff F Z') *
          (appendAverage (BinaryMatrixFourier.character Z) M *
            appendAverage (BinaryMatrixFourier.character Z') M)) from by
              funext M
              exact hpoint M]
    rw [uniformMean_const_mul, appendAverage_character_pair]
    by_cases h : Z = Z' ∧ appendedFrequencyPart Z = 0
    · rcases h with ⟨rfl, hW⟩
      simp [hW, pow_two]
    · simp [h]
  have hcollapse :
      (∑ Z ∈ S, ∑ Z' ∈ S,
          if Z = Z' ∧ appendedFrequencyPart Z = 0 then
            (fourierCoeff F Z) ^ 2 else 0) =
        ∑ Z ∈ S,
          if appendedFrequencyPart Z = 0 then
            (fourierCoeff F Z) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro Z hZ
    by_cases hW : appendedFrequencyPart Z = 0
    · simp [hW, hZ]
    · simp [hW]
  calc
    uniformMean (fun M : BinaryMatrix n c =>
        (appendAverage (rankProjection i F) M) ^ 2) =
      uniformMean (fun M => ∑ Z ∈ S, ∑ Z' ∈ S, term Z M * term Z' M) := by
        apply congrArg uniformMean
        funext M
        rw [hexp M, hsquare M]
    _ = ∑ Z ∈ S, ∑ Z' ∈ S,
          uniformMean (fun M : BinaryMatrix n c => term Z M * term Z' M) := by
        simp_rw [uniformMean_sum]
    _ = ∑ Z ∈ S, ∑ Z' ∈ S,
          if Z = Z' ∧ appendedFrequencyPart Z = 0 then
            (fourierCoeff F Z) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro Z hZ
        apply Finset.sum_congr rfl
        intro Z' hZ'
        exact hcross Z Z'
    _ = ∑ Z ∈ S,
          if appendedFrequencyPart Z = 0 then
            (fourierCoeff F Z) ^ 2 else 0 := hcollapse

end
end PvNP.RealizableHardness.ActualFiniteAppendSpectral47
