import PvNP.RealizableHardness.BinaryMatrixActualAffine

namespace PvNP.RealizableHardness.BinaryMatrixCodomainA15

open BinaryMatrixFourier BinaryMatrixLineA15 BinaryMatrixActualAffine
  BinaryMatrixFirstDerivative BinaryMatrixHybridSelector BinaryMatrixLineTranslation
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Swap the raw domain and codomain equations. This preserves the nominal
order and sends each affine fibre bijectively to its transpose. -/
def transposeRaw {n d : ℕ} (R : AffineRestriction n d) :
    AffineRestriction d n where
  columns := R.rows
  rows := R.columns
  rightDirections := R.leftDirections.transpose
  rightValues := R.leftValues.transpose
  leftDirections := R.rightDirections.transpose
  leftValues := R.rightValues.transpose

@[simp] theorem transposeRaw_budget {n d : ℕ} (R : AffineRestriction n d) :
    (transposeRaw R).budget = R.budget := by
  simp [transposeRaw, AffineRestriction.budget, Nat.add_comm]

theorem transposeRaw_fibre {n d : ℕ} (R : AffineRestriction n d) :
    (transposeRaw R).fibre = R.fibre.image Matrix.transpose := by
  ext X
  simp only [AffineRestriction.fibre, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨hr, hl⟩
    refine ⟨X.transpose, ?_, by simp⟩
    constructor
    · have h := congrArg Matrix.transpose hl
      rw [Matrix.transpose_mul] at h
      exact h
    · have h := congrArg Matrix.transpose hr
      rw [Matrix.transpose_mul] at h
      exact h
  · rintro ⟨M, ⟨hr, hl⟩, rfl⟩
    constructor
    · have h := congrArg Matrix.transpose hl
      rw [Matrix.transpose_mul] at h
      exact h
    · have h := congrArg Matrix.transpose hr
      rw [Matrix.transpose_mul] at h
      exact h

def transposeFunction {n d : ℕ} (f : BinaryMatrix n d → ℝ) :
    BinaryMatrix d n → ℝ := fun M => f M.transpose

theorem upToRawSquareGlobal_transpose {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℝ)
    (hf : UpToRawSquareGlobal r ε f) :
    UpToRawSquareGlobal r ε (transposeFunction f) := by
  intro R hR
  let Q : AffineRestriction n d := transposeRaw R
  have hQ : Q.budget ≤ r := by simpa [Q] using hR
  have h := hf Q hQ
  have heq : R.fibre = Q.fibre.image Matrix.transpose := by
    simpa [Q, transposeRaw, Matrix.transpose_transpose] using
      (transposeRaw_fibre Q)
  rw [heq]
  have hi : Set.InjOn (Matrix.transpose : BinaryMatrix n d → BinaryMatrix d n) Q.fibre :=
    Matrix.transpose_injective.injOn
  simpa only [transposeFunction, Finset.sum_image hi, Finset.card_image_iff.mpr hi,
    Matrix.transpose_transpose] using h

/-- A fixed codomain hyperplane in coordinates: the last output row is
prescribed by the base `t`; the other rows vary. -/
def rawLastRow {n d : ℕ} (M : BinaryMatrix n d)
    (t : Fin d → ZMod 2) : BinaryMatrix (n + 1) d :=
  (rawLastColumn M.transpose t).transpose

def rawLastRowRestrict {n d : ℕ} (t : Fin d → ZMod 2)
    (f : BinaryMatrix (n + 1) d → ℝ) : BinaryMatrix n d → ℝ :=
  fun M => f (rawLastRow M t)

/-- The actual codomain-hyperplane polynomial is the conjugate of the
actual line translation polynomial under matrix transpose. -/
def hyperplaneP (j : ℕ) {n d : ℕ}
    (f : BinaryMatrix (n + 1) d → ℝ) : BinaryMatrix (n + 1) d → ℝ :=
  transposeFunction (lineP j (transposeFunction f))

theorem actualGlobal_A15_fixedCodomainHyperplane {n d k : ℕ}
    {ε : ℝ} (t : Fin d → ZMod 2)
    (f : BinaryMatrix (n + 1) d → ℝ)
    (hε : 0 ≤ ε)
    (hf : UpToActualSquareGlobal (k + 1) ε f) :
    UpToActualSquareGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (rawLastRowRestrict t (hyperplaneP k f)) := by
  have hraw := upToActual_implies_upToRaw f hε hf
  have htr := upToRawSquareGlobal_transpose f hraw
  have hp := upToRawSquareGlobal_A15_fixedBase t (transposeFunction f) hε htr
  apply upToRaw_implies_upToActual _
  convert (upToRawSquareGlobal_transpose _ hp) using 1
  funext M
  simp [rawLastRowRestrict, hyperplaneP, transposeFunction,
    rawLastRow, rawLastColumnRestrict]

end
end PvNP.RealizableHardness.BinaryMatrixCodomainA15
