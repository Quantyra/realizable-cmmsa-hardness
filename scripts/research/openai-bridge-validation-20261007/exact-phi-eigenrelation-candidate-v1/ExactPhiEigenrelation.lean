import PvNP.RealizableHardness.ActualFiniteAppendSpectral47
import PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
import PvNP.RealizableHardness.ActualFiniteFrameProductDuality
import PvNP.RealizableHardness.ExactAppendOperatorContracts

/-!
Uncompiled author continuation for the exact Phi rank-character eigenrelation.
The target is the unconditional B average and the independent uniform
full-row-frame C average from ExactAppendOperatorContracts.  In particular,
the result below has no right-invariance hypothesis on F.

The key finite identity is separated as a reusable lemma: B kills a
character exactly when every row of C lies in ker(Y.mulVecLin).  The remaining
count is the independent-frame count in that kernel, whose dimension is
d - Y.rank.  This candidate has not been run through the GCP compiler.
-/

namespace PvNP.RealizableHardness.ExactPhiEigenrelation

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47
open PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ExactAppendOperatorContracts

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem pairing_mul_right_rect {n d s : Nat}
    (Y : BinaryMatrix n d) (B : BinaryMatrix n s) (C : BinaryMatrix s d) :
    pairing Y (B * C) = pairing (Y * C.transpose) B := by
  classical
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc
    (∑ j : Fin d, (∑ k : Fin s, B i k * C k j) * Y i j) =
        ∑ j : Fin d, ∑ k : Fin s, (B i k * C k j) * Y i j := by
      simp_rw [Finset.sum_mul]
    _ = ∑ k : Fin s, ∑ j : Fin d, (B i k * C k j) * Y i j :=
      Finset.sum_comm
    _ = ∑ k : Fin s, (∑ j : Fin d, Y i j * C k j) * B i k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Exact unrestricted-B character cancellation for a fixed C. -/
theorem unrestricted_B_character_mean {n d s : Nat}
    (Y : BinaryMatrix n d) (C : BinaryMatrix s d) :
    uniformMean (fun B : BinaryMatrix n s =>
      BinaryMatrixFourier.character Y (B * C)) =
        if Y * C.transpose = 0 then 1 else 0 := by
  have hpoint (B : BinaryMatrix n s) :
      BinaryMatrixFourier.character Y (B * C) =
        BinaryMatrixFourier.character (Y * C.transpose) B := by
    change (if pairing Y (B * C) = 0 then 1 else -1) =
      (if pairing (Y * C.transpose) B = 0 then 1 else -1)
    rw [pairing_mul_right_rect]
  rw [show (fun B : BinaryMatrix n s =>
      BinaryMatrixFourier.character Y (B * C)) =
      (fun B => BinaryMatrixFourier.character (Y * C.transpose) B) from by
        funext B
        exact hpoint B]
  by_cases h : Y * C.transpose = 0
  · rw [show Y * C.transpose = 0 from h]
    simp [BinaryMatrixFourier.character_zero_left, uniformMean_const]
  · have hne : (Y * C.transpose : BinaryMatrix n s) ≠ 0 := h
    simpa [hne] using
      BinaryMatrixFourier.character_orthogonality
        (Y * C.transpose) (0 : BinaryMatrix n s)

/-!
The outstanding bridge for the eigenrelation is the concrete equivalence
between the subtype of `FullRowFrame s d` satisfying `Y * Cᵀ = 0` and
`Frame (LinearMap.ker Y.mulVecLin) s`.  Its forward map sends row j to the
subtype vector given by that row; its inverse forgets the subtype proofs and
reassembles the matrix.  Row independence is exactly surjectivity by
`matrix_surjective_iff_rows_independent`.  The dimension is obtained from
`Y.mulVecLin.finrank_range_add_finrank_ker` and the pinned rank/range identity.

After this equivalence, `card_frame` gives the survivor count
`frameProduct (d - Y.rank) s`, including s = 0 and d - rank < s.  Dividing by
`card_surjective_coordinate_maps d s = frameProduct d s` gives the exact
character eigenvalue.  The pointwise character result above already handles
n = 0 and s = 0 through the actual unrestricted carrier.

The authoring boundary is explicit: the two displayed lemmas are source
proofs; the frame equivalence/count and the final finite-sum interchange into
`phiAverage (rankProjection i F)` are still to be supplied and GCP-checked.
No theorem name below is presented as certified evidence.
-/

end
end PvNP.RealizableHardness.ExactPhiEigenrelation
