import PvNP.RealizableHardness.MatrixLiftLeftRowFactorTwo

/-! Transport the factor-two estimate at the finite-fibre boundary, without
unfolding the normalized subtype inside the binary bridge proof. -/
namespace PvNP.RealizableHardness.MatrixLiftLeftRowDirectTransport
open scoped BigOperators
open GrassmannCounting MatrixGrassmannFibre MatrixLiftAffineTarget
open MatrixLiftLeftRowNormalForm MatrixLiftLeftRowFactorTwo

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {b k a : ℕ}

/-- A score mean over the explicit residual row fibre transfers exactly to
the original, arbitrary fixed row target. -/
theorem raw_mean_le_of_explicit_target_bound
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b)
    (M : ℝ)
    (hbound :
      (∑ N : {N : FreeColumns (zeroKernel X B) k //
          rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B},
          liftScore f g (zeroKernel X B) N.val) /
        (Fintype.card {N : FreeColumns (zeroKernel X B) k //
          rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} : ℝ)
          ≤ M) :
    (∑ N : rawTargetFibre X B, extensionTest f g N.val) /
        (Fintype.card (rawTargetFibre X B) : ℝ) ≤ M := by
  calc
    _ = (∑ N : normalizedTargetFibre X B,
          liftScore f g (zeroKernel X B) N.val) /
        (Fintype.card (normalizedTargetFibre X B) : ℝ) :=
          raw_mean_eq_normalized f g X B
    _ = (∑ N : {N : FreeColumns (zeroKernel X B) k //
            rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B},
            liftScore f g (zeroKernel X B) N.val) /
        (Fintype.card {N : FreeColumns (zeroKernel X B) k //
            rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} : ℝ) := by
          rw [normalized_score_sum_eq_explicit, normalized_card_eq_explicit]
    _ ≤ M := hbound

end
end PvNP.RealizableHardness.MatrixLiftLeftRowDirectTransport
