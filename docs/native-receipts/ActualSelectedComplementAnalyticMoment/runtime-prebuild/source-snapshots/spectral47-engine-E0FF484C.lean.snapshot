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
  simp [BinaryMatrixFourier.pairing, Matrix.trace, Matrix.mul_apply,
    Finset.sum_comm, mul_comm]

theorem pairing_mul_right_transpose {n d : Nat}
    (Y M : BinaryMatrix n d) (U : BinaryMatrix d d) :
    pairing (Y * U.transpose) M = pairing Y (M * U) := by
  rw [pairing_eq_trace_transpose_mul, pairing_eq_trace_transpose_mul]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]

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
    simp [BinaryMatrixFourier.character, pairing_mul_right_transpose]
  let e : BinaryMatrix n d ≃ BinaryMatrix n d where
    toFun M := M * U
    invFun M := M * V
    left_inv M := by
      dsimp
      rw [← Matrix.mul_assoc, hUV, Matrix.mul_one]
    right_inv M := by
      dsimp
      rw [← Matrix.mul_assoc, hVU, Matrix.mul_one]
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
    (Matrix.isUnit_det_transpose (Matrix.isUnit_det_of_right_inverse hUV))

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
  let e : BinaryMatrix n d ≃ BinaryMatrix n d where
    toFun Z := Z * U.transpose
    invFun Z := Z * V.transpose
    left_inv Z := by
      dsimp
      rw [Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mul_assoc, hVU, Matrix.mul_one]
    right_inv Z := by
      dsimp
      rw [Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mul_assoc, hUV, Matrix.mul_one]
  have hrank (Z : BinaryMatrix n d) : (e Z).rank = Z.rank := by
    exact rank_mul_right_transpose_eq Z U V hUV
  have hchar (Z : BinaryMatrix n d) :
      BinaryMatrixFourier.character Z (M * U) =
        BinaryMatrixFourier.character (e Z) M := by
    simpa [e] using (pairing_mul_right_transpose Z M U)
  unfold rankProjection
  simp_rw [hchar]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  have hpoint (Z : BinaryMatrix n d) :
      (if Z.rank = i then
        fourierCoeff F Z * BinaryMatrixFourier.character (e Z) M else 0) =
      (if (e Z).rank = i then
        fourierCoeff F (e Z) * BinaryMatrixFourier.character (e Z) M else 0) := by
    rw [hrank Z,
      fourierCoeff_mul_right_transpose_eq F basisInv Z U V hUV hVU]
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
  simp [appendedFrequencyPart, baseFrequencyPart,
    appendAverage_character]

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
  rw [appendAverage_character, appendAverage_character]
  by_cases hW : W = 0 <;> by_cases hW' : W' = 0
  · have hEq : Z = Z' ↔ Y = Y' := by
      constructor
      · intro h
        have hh := congrArg (fun Q => (e.symm Q).1) h
        simpa [Y, Y'] using hh
      · intro h
        calc
          Z = appendBinaryMatrix Y W := hZ.symm
          _ = appendBinaryMatrix Y' W' := by simp [hW, hW', h]
          _ = Z' := hZ'
    simp [appendedFrequencyPart, e, Y, W, Y', W', hW, hEq,
      BinaryMatrixFourier.character_orthogonality]
  all_goals simp [appendedFrequencyPart, e, Y, W, Y', W', hW, hW']

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
    apply Finset.sum_congr rfl
    intro Z' hZ'
    rfl
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
    · simp [hW, Finset.sum_ite_eq', hZ]
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
