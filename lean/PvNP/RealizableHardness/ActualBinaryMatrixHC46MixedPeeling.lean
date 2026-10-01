import PvNP.RealizableHardness.ActualBinaryMatrixHC46FinitePeeling

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46MixedPeeling

open BinaryMatrixComplexA15
open ActualBinaryMatrixHC46FinitePeeling

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact A15 loss for removing `k` domain coordinates and then `l`
codomain coordinates from a matrix-valued function. -/
def mixedCoordinatePeelLoss (r k l : Nat) : Real :=
  hyperplanePeelLoss r l * linePeelLoss (r + l) k

/-- Apply prescribed domain-line peels first and codomain-hyperplane peels
second. The order fixes the rank parameter used by each A15 step. -/
def mixedCoordinatePeel {n d : Nat} (r k l : Nat)
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2) :
    BinaryMatrix n d -> Complex :=
  coordinateHyperplanePeel (n := n) (d := d) r l
    (coordinateLinePeel (n := n + l) (d := d) (r + l) k f tLine)
    tHyp

theorem mixedCoordinatePeel_global {n d r k l : Nat} {eps : Real}
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2)
    (heps : 0 <= eps)
    (hf : UpToActualNormSqGlobal (r + (k + l)) eps f) :
    UpToActualNormSqGlobal r (mixedCoordinatePeelLoss r k l * eps)
      (mixedCoordinatePeel r k l f tLine tHyp) := by
  have hline := coordinateLinePeel_global
    (n := n + l) (d := d) (r := r + l) (k := k)
    f tLine heps (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
  have hline0 : 0 <= linePeelLoss (r + l) k * eps := by
    have hloss : 0 <= linePeelLoss (r + l) k := by
      induction k with
      | zero => simp [linePeelLoss]
      | succ k ih =>
          simp only [linePeelLoss]
          positivity
    exact mul_nonneg hloss heps
  have hhyper := coordinateHyperplanePeel_global
    (n := n) (d := d) (r := r) (k := l)
    (coordinateLinePeel (n := n + l) (d := d) (r + l) k f tLine)
    tHyp hline0 hline
  simpa [mixedCoordinatePeel, mixedCoordinatePeelLoss,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    mul_assoc, mul_comm, mul_left_comm] using hhyper

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46MixedPeeling
