import PvNP.RealizableHardness.BinaryMatrixCodomainA15
import PvNP.RealizableHardness.BinaryMatrixLineA14

namespace PvNP.RealizableHardness.BinaryMatrixCodomainA14

open BinaryMatrixFourier BinaryMatrixFirstDerivative BinaryMatrixHybridSelector
  BinaryMatrixLineA14 BinaryMatrixCodomainA15 BinaryMatrixLineTranslation
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private def transposeEquiv (n d : ℕ) : BinaryMatrix n d ≃ BinaryMatrix d n where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose

theorem pairing_transpose {n d : ℕ} (Y M : BinaryMatrix n d) :
    pairing Y.transpose M.transpose = pairing Y M := by
  simp only [pairing, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem character_transpose {n d : ℕ} (Y M : BinaryMatrix n d) :
    character Y.transpose M.transpose = character Y M := by
  simp [character, pairing_transpose]

theorem fourierCoeff_transpose {n d : ℕ}
    (f : BinaryMatrix n d → ℝ) (Y : BinaryMatrix n d) :
    fourierCoeff (transposeFunction f) Y.transpose = fourierCoeff f Y := by
  have hs : (∑ M : BinaryMatrix d n,
      f M.transpose * character Y.transpose M) =
      ∑ M : BinaryMatrix n d, f M * character Y M := by
    rw [← Equiv.sum_comp (transposeEquiv n d)
      (fun M : BinaryMatrix d n => f M.transpose * character Y.transpose M)]
    change (∑ M : BinaryMatrix n d,
      f M.transpose.transpose * character Y.transpose M.transpose) = _
    simp only [Matrix.transpose_transpose, character_transpose]
  simp only [fourierCoeff, uniformMean, transposeFunction, hs]
  congr 1
  simp [Fintype.card_congr (transposeEquiv n d)]

theorem rankProjection_transpose {n d j : ℕ}
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) :
    rankProjection j (transposeFunction f) M.transpose =
      rankProjection j f M := by
  simp only [rankProjection]
  have hs : (∑ Y ∈ (Finset.univ : Finset (BinaryMatrix d n)).filter
      (fun Y => Y.rank = j),
      fourierCoeff (transposeFunction f) Y * character Y M.transpose) =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
        (fun Y => Y.rank = j), fourierCoeff f Y * character Y M := by
    simp only [Finset.sum_filter]
    rw [← Equiv.sum_comp (transposeEquiv n d)
      (fun Y : BinaryMatrix d n =>
        if Y.rank = j then
          fourierCoeff (transposeFunction f) Y * character Y M.transpose else 0)]
    apply Finset.sum_congr rfl
    intro Y _
    simp [transposeEquiv, Matrix.rank_transpose,
      fourierCoeff_transpose, character_transpose]
  exact hs

/-- Codomain-hyperplane A14 in the actual transpose-coordinate carrier.
The derivative uses the full hybrid selector of the transposed source. -/
def hyperplaneDerivative {n d : ℕ} (t : Fin d → ZMod 2)
    (f : BinaryMatrix (n + 1) d → ℝ) : BinaryMatrix n d → ℝ :=
  transposeFunction (hybridLineDerivative t (transposeFunction f))

theorem rankProjection_rawRestrict_hyperplaneP_eq_hyperplaneDerivative
    {n d j : ℕ} (t : Fin d → ZMod 2)
    (f : BinaryMatrix (n + 1) d → ℝ) (M : BinaryMatrix n d) :
    rankProjection j (rawLastRowRestrict t (hyperplaneP j f)) M =
      hyperplaneDerivative t (rankProjection (j + 1) f) M := by
  have h := rankProjection_rawRestrict_lineP_eq_hybridDerivative
    (j := j) t (transposeFunction f) M.transpose
  have hproj : rankProjection (j + 1) (transposeFunction f) =
      transposeFunction (rankProjection (j + 1) f) := by
    funext N
    simpa only [transposeFunction, Matrix.transpose_transpose] using
      rankProjection_transpose f N.transpose
  rw [hproj] at h
  have htr : transposeFunction (rawLastRowRestrict t (hyperplaneP j f)) =
      rawLastColumnRestrict t (lineP j (transposeFunction f)) := by
    funext N
    simp [transposeFunction, rawLastRowRestrict, hyperplaneP,
      rawLastRow, rawLastColumnRestrict]
  rw [← htr] at h
  exact (rankProjection_transpose _ M).symm.trans
    (by simpa only [hyperplaneDerivative, transposeFunction] using h)

end
end PvNP.RealizableHardness.BinaryMatrixCodomainA14
