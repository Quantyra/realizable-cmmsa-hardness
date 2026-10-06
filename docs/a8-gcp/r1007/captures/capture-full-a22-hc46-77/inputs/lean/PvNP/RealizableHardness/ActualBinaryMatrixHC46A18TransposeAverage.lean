import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalEnergy

/-! The exact transpose of the ambient A18 draw.

The averaging law is retained pointwise: transposition sends each sampled
rank-one update to its transpose and preserves its finite uniform index set.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeAverage

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalBridge
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalEnergy
open BinaryMatrixComplexA15 BinaryMatrixFourier
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

/-- The exact pushforward of the manuscript's ambient `(psi,w)` draw through
matrix transposition. No conditional distribution is changed. -/
def actualA18TransposeAverage {n d : ℕ}
    (v : Fin d → ZMod 2)
    (f : BinaryMatrix d n → ℂ) (N : BinaryMatrix d n) : ℂ :=
  (∑ p : FunctionalsAt v × (Fin n → ZMod 2),
    f (N + (actualA18RankOne p.1.1 p.2).transpose)) /
      (Fintype.card (FunctionalsAt v × (Fin n → ZMod 2)) : ℂ)

/-- Pointwise operator identity: transposing the actual A18 average is exactly
the same finite uniform draw with each rank-one increment transposed. -/
theorem complexTranspose_actualA18Average {n d : ℕ}
    (v : Fin d → ZMod 2)
    (f : BinaryMatrix n d → ℂ) (N : BinaryMatrix d n) :
    complexTranspose (fun M => actualA18Average v f M) N =
      actualA18TransposeAverage v (complexTranspose f) N := by
  classical
  simp [actualA18TransposeAverage, actualA18Average, complexTranspose,
    Matrix.transpose_add, Matrix.transpose_transpose]

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeAverage
