import PvNP.RealizableHardness.MatrixLiftLeftRowNormalForm

namespace PvNP.RealizableHardness.MatrixLiftLeftRowFactorTwo
open scoped BigOperators
open GrassmannCounting MatrixGrassmannFibre MatrixLiftAffineTarget
open MatrixLiftLeftRowNormalForm
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {b k a : ℕ}

/-- The binary comparison at the concrete residual target type. -/
def normalized_target_mean_le_twice
    (f : Frame V a) (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X : V →ₗ[ZMod 2] Rows b) (hX : Function.Surjective X)
    (B : Fin k → Rows b) (hbk : b < k) :=
  MatrixLiftFullRowRankBridge.binary_affine_target_mean_le_twice
    (targetRank_lt B hbk) (zeroKernel X B) f g hg
    (residualRowsFin X B) (residualRowsFin_surjective X B hX)
    (residualTargetFin B) (residualTargetFin_full_rank B)

def normalizedFibreEquiv
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    normalizedTargetFibre X B ≃
      {N : FreeColumns (zeroKernel X B) k //
        rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} :=
  Equiv.refl _

theorem normalized_card_eq_explicit
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    Fintype.card (normalizedTargetFibre X B) =
      Fintype.card {N : FreeColumns (zeroKernel X B) k //
        rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} :=
  Fintype.card_congr (normalizedFibreEquiv X B)

theorem normalized_score_sum_eq_explicit
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    (∑ N : normalizedTargetFibre X B,
      liftScore f g (zeroKernel X B) N.val) =
      ∑ N : {N : FreeColumns (zeroKernel X B) k //
        rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B},
        liftScore f g (zeroKernel X B) N.val := by
  apply Fintype.sum_equiv (normalizedFibreEquiv X B)
  intro N
  rfl

theorem raw_mean_eq_normalized
    (f : Frame V a) (g : Grass V (a+k) → ℝ)
    (X : V →ₗ[ZMod 2] Rows b) (B : Fin k → Rows b) :
    (∑ N : rawTargetFibre X B, extensionTest f g N.val) /
        (Fintype.card (rawTargetFibre X B) : ℝ) =
      (∑ N : normalizedTargetFibre X B,
        liftScore f g (zeroKernel X B) N.val) /
        (Fintype.card (normalizedTargetFibre X B) : ℝ) := by
  rw [rawNormalized_score_sum_eq, rawNormalized_card_eq]


end
end PvNP.RealizableHardness.MatrixLiftLeftRowFactorTwo
