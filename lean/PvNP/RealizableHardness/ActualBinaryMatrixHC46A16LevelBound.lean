import PvNP.RealizableHardness.ActualBinaryMatrixHC46MixedPeeling

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A16LevelBound

open BinaryMatrixFourier BinaryMatrixComplexA14 BinaryMatrixComplexA15
open ActualBinaryMatrixHC46MixedPeeling

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual accumulated A15 loss at one residual input rank is bounded by
the manuscript's per-level dyadic envelope whenever the residual rank and
the total number of peeled coordinates fit below D. -/
theorem mixedCoordinatePeelLoss_le_A16_level_envelope
    {r k l D : Nat} (hrank : r + (k + l) <= D) :
    mixedCoordinatePeelLoss r k l <= (2 : Real) ^ (10 * D ^ 2) := by
  have ht : k + l <= D := by omega
  have hr : r <= D := by omega
  have hrt : r * (k + l) <= D * D := Nat.mul_le_mul hr ht
  have htt : (k + l) * (k + l) <= D * D := Nat.mul_le_mul ht ht
  have hDsq : D <= D * D := le_mul_self D
  have hrt4 : 4 * (r * (k + l)) <= 4 * (D * D) :=
    Nat.mul_le_mul_left 4 hrt
  have htt2 : 2 * ((k + l) * (k + l)) <= 2 * (D * D) :=
    Nat.mul_le_mul_left 2 htt
  have ht4 : 4 * (k + l) <= 4 * (D * D) :=
    Nat.mul_le_mul_left 4 (ht.trans hDsq)
  have hexp :
      4 * r * (k + l) + 2 * (k + l) ^ 2 + 4 * (k + l) <= 10 * D ^ 2 := by
    calc
      4 * r * (k + l) + 2 * (k + l) ^ 2 + 4 * (k + l)
          = 4 * (r * (k + l)) + 2 * ((k + l) * (k + l)) + 4 * (k + l) := by ring
      _ <= 4 * (D * D) + 2 * (D * D) + 4 * (D * D) :=
        by simpa only [Nat.add_assoc] using
          (Nat.add_le_add hrt4 (Nat.add_le_add htt2 ht4))
      _ = 10 * D ^ 2 := by ring
  rw [mixedCoordinatePeelLoss_eq_pow]
  exact pow_le_pow_right₀ (by norm_num) hexp

/-- One actual coordinate A16 level estimate. The source-globalness premise
is on the original function through rank `r+k+l`; the existing A15 energy
theorem handles the corresponding Fourier projection. -/
theorem mixedCoordinateDerivativeChain_energy_bound_le_A16_level_envelope
    {n d r k l D : Nat} {eps : Real}
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2)
    (hrank : r + (k + l) <= D)
    (heps : 0 <= eps)
    (hf : UpToActualNormSqGlobal (r + (k + l)) eps
      f) :
    fibreEnergy Finset.univ
      (mixedCoordinateDerivativeChain r k l
        (complexRankProjection (r + (k + l)) f) tLine tHyp) <=
      (2 : Real) ^ (10 * D ^ 2) * eps := by
  have hbase := mixedCoordinateDerivativeChain_energy_bound
    f tLine tHyp heps hf
  have hloss := mixedCoordinatePeelLoss_le_A16_level_envelope hrank
  exact hbase.trans (mul_le_mul_of_nonneg_right hloss heps)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A16LevelBound
