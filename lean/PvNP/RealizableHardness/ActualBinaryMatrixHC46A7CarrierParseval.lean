import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A12FourthMoment
import PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport

/-! Parseval for the actual typed carrier supporting a W6 predecessor
derivative. The carrier is transported through its accepted matrix
coordinate equivalence; no collision-fiber cardinality is assumed here. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A7CarrierParseval

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A12FourthMoment
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Complex Parseval on every actual typed Hom carrier, obtained by the
accepted matrix-coordinate equivalence and its transpose-aware frequency map. -/
theorem complex_carrier_parseval {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → Complex) :
    carrierMean A B (fun M => Complex.normSq (g M)) =
      ∑ Z : B →ₗ[F] (V d ⧸ A),
        Complex.normSq (complexCarrierFourierCoeff A B g Z) := by
  calc
    carrierMean A B (fun M => Complex.normSq (g M)) =
        uniformMean (fun X => Complex.normSq
          (g ((carrierMatrixEquiv A B).symm X))) :=
      carrierComplexEnergy_coordinate A B g
    _ = ∑ Y : BinaryMatrix (Module.finrank F B)
        (Module.finrank F (V d ⧸ A)),
          Complex.normSq (complexFourierCoeff
            (fun X => g ((carrierMatrixEquiv A B).symm X)) Y) :=
      complex_fourier_parseval _
    _ = ∑ Z : B →ₗ[F] (V d ⧸ A),
          Complex.normSq (complexCarrierFourierCoeff A B g Z) := by
      apply Fintype.sum_equiv (carrierFrequencyEquiv A B).symm.toEquiv
      intro Y
      rw [carrierFourierCoeff_coordinate]
      simp only [LinearEquiv.apply_symm_apply]

/-- Parseval for the actual W6 derivative at a fixed affine base. -/
theorem actualW6Derivative_energy_parseval {n d : Nat}
    (X : BinaryMatrix n d) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    carrierMean (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin')
        (fun M => Complex.normSq (actualW6Derivative X T f M)) =
      ∑ Z : LinearMap.ker X.transpose.toLin' →ₗ[F]
          (V d ⧸ LinearMap.range X.transpose.toLin'),
        Complex.normSq (complexCarrierFourierCoeff
          (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')
          (actualW6Derivative X T f) Z) := by
  exact complex_carrier_parseval
    (LinearMap.range X.transpose.toLin')
    (LinearMap.ker X.transpose.toLin') (actualW6Derivative X T f)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7CarrierParseval
