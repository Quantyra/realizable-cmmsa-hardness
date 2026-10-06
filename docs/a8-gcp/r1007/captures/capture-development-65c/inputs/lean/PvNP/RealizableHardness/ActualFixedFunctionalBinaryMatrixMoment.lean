import PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
import PvNP.RealizableHardness.BinaryMatrixFourier

/-! Exact coordinate transport for the fixed-functional star moment.
Coordinate arrays are transposed into `BinaryMatrix` entries. Every appended
matrix is averaged unconditionally; the accepted `rawF` assigns zero to
rank-deficient concatenations, and one common base matrix is shared across
all independent appended-column draws in the kth moment. -/

namespace PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment

open scoped BigOperators
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.MatrixGrassmannIdentity
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section

abbrev CoordinateAmbient (n : Nat) := Fin n → ZMod 2

/-- A coordinate array stores coordinates by column while a matrix stores
them by row. -/
def coordinateArrayBinaryMatrixEquiv (n d : Nat) :
    (Fin d → CoordinateAmbient n) ≃ BinaryMatrix n d where
  toFun A := fun i j => A j i
  invFun M := fun j i => M i j
  left_inv A := by
    funext j i
    rfl
  right_inv M := by
    ext i j
    rfl

theorem coordinateArrayBinaryMatrixEquiv_apply {n d : Nat}
    (A : Fin d → CoordinateAmbient n) (i : Fin n) (j : Fin d) :
    coordinateArrayBinaryMatrixEquiv n d A i j = A j i := rfl

/-- The accepted raw appended-column average, expressed over all binary
matrices with no rank condition in the sampling law. -/
theorem rawTF_eq_unconditional_binaryMatrix_mean {n d w : Nat}
    (Lset : Grass (CoordinateAmbient n) (d + w) → Bool)
    (M : Fin d → CoordinateAmbient n) :
    rawTF Lset M = uniformMean (fun B : BinaryMatrix n w =>
      rawF Lset M ((coordinateArrayBinaryMatrixEquiv n w).symm B)) := by
  unfold MatrixGrassmannIdentity.rawTF BinaryMatrixFourier.uniformMean
  have hsum :
      (∑ B : BinaryMatrix n w,
        rawF Lset M ((coordinateArrayBinaryMatrixEquiv n w).symm B)) =
      ∑ B : Fin w → CoordinateAmbient n, rawF Lset M B := by
    exact Equiv.sum_comp (coordinateArrayBinaryMatrixEquiv n w).symm
      (fun B : Fin w → CoordinateAmbient n => rawF Lset M B)
  have hcard : Fintype.card (BinaryMatrix n w) =
      Fintype.card (Fin w → CoordinateAmbient n) := by
    exact Fintype.card_congr (coordinateArrayBinaryMatrixEquiv n w).symm
  rw [hsum, hcard]

/-- The exact array form of the accepted `matrixMoment`, transported to one
uniform base binary matrix and independent unconditional appended matrices. -/
def actualBinaryMatrixMoment {n d w : Nat}
    (Rset : Grass (CoordinateAmbient n) d → Bool)
    (Lset : Grass (CoordinateAmbient n) (d + w) → Bool) (k : Nat) : Real :=
  uniformMean (fun M : BinaryMatrix n d =>
    rawG Rset ((coordinateArrayBinaryMatrixEquiv n d).symm M) *
      (uniformMean (fun B : BinaryMatrix n w =>
        rawF Lset ((coordinateArrayBinaryMatrixEquiv n d).symm M)
          ((coordinateArrayBinaryMatrixEquiv n w).symm B))) ^ k)

theorem matrixMoment_eq_actualBinaryMatrixMoment {n d w : Nat}
    (Rset : Grass (CoordinateAmbient n) d → Bool)
    (Lset : Grass (CoordinateAmbient n) (d + w) → Bool) (k : Nat) :
    matrixMoment Rset Lset k = actualBinaryMatrixMoment Rset Lset k := by
  change (∑ M : Fin d → CoordinateAmbient n,
      rawG Rset M * (rawTF Lset M) ^ k) /
      (Fintype.card (Fin d → CoordinateAmbient n) : Real) =
    (∑ M : BinaryMatrix n d,
      rawG Rset ((coordinateArrayBinaryMatrixEquiv n d).symm M) *
        (uniformMean (fun B : BinaryMatrix n w =>
          rawF Lset ((coordinateArrayBinaryMatrixEquiv n d).symm M)
            ((coordinateArrayBinaryMatrixEquiv n w).symm B))) ^ k) /
      (Fintype.card (BinaryMatrix n d) : Real)
  have hsum :
      (∑ M : BinaryMatrix n d,
        rawG Rset ((coordinateArrayBinaryMatrixEquiv n d).symm M) *
          (uniformMean (fun B : BinaryMatrix n w =>
            rawF Lset ((coordinateArrayBinaryMatrixEquiv n d).symm M)
              ((coordinateArrayBinaryMatrixEquiv n w).symm B))) ^ k) =
      ∑ M : Fin d → CoordinateAmbient n,
        rawG Rset M * (rawTF Lset M) ^ k := by
    calc
      _ = ∑ M : BinaryMatrix n d,
          rawG Rset ((coordinateArrayBinaryMatrixEquiv n d).symm M) *
            (rawTF Lset ((coordinateArrayBinaryMatrixEquiv n d).symm M)) ^ k := by
              apply Finset.sum_congr rfl
              intro M _
              rw [rawTF_eq_unconditional_binaryMatrix_mean]
      _ = ∑ M : Fin d → CoordinateAmbient n,
          rawG Rset M * (rawTF Lset M) ^ k :=
        (coordinateArrayBinaryMatrixEquiv n d).symm.sum_comp
          (fun M => rawG Rset M * (rawTF Lset M) ^ k)
  have hcard : Fintype.card (BinaryMatrix n d) =
      Fintype.card (Fin d → CoordinateAmbient n) := by
    exact Fintype.card_congr (coordinateArrayBinaryMatrixEquiv n d).symm
  rw [hsum, hcard]

/-- The actual same-functional common-center star mass is bounded by the
accepted fixed-functional matrix moment, with no assumed moment certificate.
All centers and leaves are tested by the same fixed tables and functional. -/
theorem matchingStarMass_cast_le_twice_actualBinaryMatrixMoment
    {n c s k : Nat} (hdV : c + s ≤ Module.finrank (ZMod 2) (CoordinateAmbient n))
    (hD : 0 < c + s)
    (hsmall : ((c + k * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
      (2 : Real) ^ Module.finrank (ZMod 2) (CoordinateAmbient n) ≤ 1 / 2)
    (C : CenterTable (V := CoordinateAmbient n) c)
    (T : LeafTable (V := CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2) (CoordinateAmbient n)) :
    (matchingStarMass (m := k) (Nat.le_add_right c s) hdV C T f : Real) ≤
      2 * actualBinaryMatrixMoment
        (fun R => centerMatchBit C f R)
        (fun W => leafMatchBit T f W) k := by
  have htransport := matchingStarMass_cast_eq_grassmannExperiment (k := k) hdV C T f
  have hmatrix := MatrixGrassmannIdentity.grassmann_le_twice_moment
    hdV hD k (fun R => centerMatchBit C f R)
      (fun W => leafMatchBit T f W) hsmall
  rw [matrixMoment_eq_actualBinaryMatrixMoment] at hmatrix
  rw [htransport]
  exact hmatrix

end
end PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
