import PvNP.RealizableHardness.ActualFiniteFrameProductDuality
import PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality

/-!
Successor source-shaped contracts for the original real
G/Phi/eigenrelation/restricted-adjoint obligations. This file intentionally
contains operator definitions and exact goal propositions, not proofs of the
goals. It is an uncompiled candidate. The definitions average over every
full-column/full-row frame, while append remains unrestricted. Phi's spectral
target is for arbitrary real F; invariance is reserved for G/Phi and the
restricted adjoint. No conditional theorem or new axiom is introduced.
-/

namespace PvNP.RealizableHardness.ExactAppendOperatorContracts

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFiniteFrameProductDuality

set_option autoImplicit false
noncomputable section

/-- A full-column-rank rectangular matrix, represented by injectivity of its
actual linear map. -/
abbrev FullColumnFrame (d c : Nat) :=
  {R : BinaryMatrix d c // Function.Injective (Matrix.toLin' R)}

/-- A full-row-rank rectangular matrix, represented by surjectivity of its
actual linear map. -/
abbrev FullRowFrame (s d : Nat) :=
  {C : BinaryMatrix s d // Function.Surjective (Matrix.toLin' C)}

/-- The manuscript's G operator: average over all full-column-rank right
embeddings. The normalization is by the exact finite frame carrier. -/
noncomputable def gAverage {n c d : Nat} (H : BinaryMatrix n c → Real)
    (M : BinaryMatrix n d) : Real := by
  classical
  exact (∑ R : FullColumnFrame d c, H (M * R.1)) /
    (Fintype.card (FullColumnFrame d c) : Real)

/-- The manuscript's Phi operator: B is uniform over every n-by-s matrix,
and C is independently uniform over every full-row-rank s-by-d matrix. -/
noncomputable def phiAverage {n d s : Nat} (F : BinaryMatrix n d → Real)
    (M : BinaryMatrix n d) : Real := by
  classical
  exact (∑ p : BinaryMatrix n s × FullRowFrame s d,
      F (M + p.1 * p.2.1)) /
    (Fintype.card (BinaryMatrix n s × FullRowFrame s d) : Real)

/-- Exact paired-inverse right invariance, retaining every square change of
basis and every matrix, including deficient and zero matrices. -/
def RightInvariant {n d : Nat} (F : BinaryMatrix n d → Real) : Prop :=
  ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
    U * V = 1 → V * U = 1 → F (M * U) = F M

/-- Exact manuscript G-after-unconditional-append equals Phi. This is the
complete target with the original invariant real F and no oracle premise. -/
def GPhiEquation {n c s : Nat} (F : BinaryMatrix n (c + s) → Real) : Prop :=
  RightInvariant F →
    ∀ M : BinaryMatrix n (c + s),
      gAverage (fun X : BinaryMatrix n c => appendAverage F X) M =
        phiAverage (s := s) F M

/-- Exact restricted-adjoint law: the first argument K is right-invariant on
the full carrier; the second argument H is arbitrary on the base carrier. -/
def RestrictedAdjointEquation {n c s : Nat}
    (K : BinaryMatrix n (c + s) → Real)
    (H : BinaryMatrix n c → Real) : Prop :=
  RightInvariant K →
    uniformMean (fun M : BinaryMatrix n c => appendAverage K M * H M) =
      uniformMean (fun W : BinaryMatrix n (c + s) => K W * gAverage H W)

/-- Exact eigenrelation for the actual Phi operator on every Fourier rank
projection of every real F, with no invariance premise. The manuscript's
d=c+s specialization makes the full-row-frame carrier nonempty. The product
coefficient is its s-factor lambda_i, including exact zero-factor cases. -/
def PhiRankEigenEquation {n c s i : Nat}
    (F : BinaryMatrix n (c + s) → Real) : Prop :=
  ∀ M : BinaryMatrix n (c + s),
      phiAverage (s := s) (rankProjection i F) M =
        (∏ k : Fin s,
          (((2 : Real) ^ (c + s - i) - (2 : Real) ^ k.val) /
            ((2 : Real) ^ (c + s) - (2 : Real) ^ k.val))) *
          rankProjection i F M

end
end PvNP.RealizableHardness.ExactAppendOperatorContracts
