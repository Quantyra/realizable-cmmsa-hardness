import PvNP.RealizableHardness.MatrixLiftLeftRowDirectTransport

namespace PvNP.RealizableHardness.MatrixLiftRowDiagnostic
open scoped BigOperators
open GrassmannCounting MatrixGrassmannFibre MatrixLiftAffineTarget
open MatrixLiftLeftRowNormalForm MatrixLiftLeftRowFactorTwo MatrixLiftLeftRowDirectTransport
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] zeroKernel residualRowsFin residualTargetFin targetCoordinates

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {b k a : ℕ}

theorem generic_factor_two {c : ℕ} (hck : c < k)
    (H : Submodule (ZMod 2) V) (f : Frame V a)
    (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X₁ : H →ₗ[ZMod 2] (Fin c → ZMod 2))
    (hX₁ : Function.Surjective X₁)
    (B : Fin k → (Fin c → ZMod 2))
    (hB : Function.Surjective (columnLinear B)) :
    (∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B},
      liftScore f g H N.val) /
        (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) ≤
      2 * ((∑ N : FreeColumns H k, liftScore f g H N) /
        (Fintype.card (FreeColumns H k) : ℝ)) := by
  simpa only [targetScoreSum] using
    (MatrixLiftFullRowRankBridge.binary_affine_target_mean_le_twice
      hck H f g hg X₁ hX₁ B hB)

theorem raw_factor_two
    (f : Frame V a) (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X : V →ₗ[ZMod 2] Rows b) (hX : Function.Surjective X)
    (B : Fin k → Rows b) (hbk : b < k) :
    (∑ N : rawTargetFibre X B, extensionTest f g N.val) /
        (Fintype.card (rawTargetFibre X B) : ℝ) ≤
      2 * ((∑ N : FreeColumns (zeroKernel X B) k,
        liftScore f g (zeroKernel X B) N) /
        (Fintype.card (FreeColumns (zeroKernel X B) k) : ℝ)) := by
  have hnorm := generic_factor_two (targetRank_lt B hbk)
      (zeroKernel X B) f g hg (residualRowsFin X B)
      (residualRowsFin_surjective X B hX) (residualTargetFin B)
      (residualTargetFin_full_rank B)
  have hbound :
      (∑ N : {N : FreeColumns (zeroKernel X B) k //
          rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B},
          liftScore f g (zeroKernel X B) N.val) /
        (Fintype.card {N : FreeColumns (zeroKernel X B) k //
          rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} : ℝ)
          ≤ 2 * ((∑ N : FreeColumns (zeroKernel X B) k,
          liftScore f g (zeroKernel X B) N) /
          (Fintype.card (FreeColumns (zeroKernel X B) k) : ℝ)) := by
    simpa only [targetScoreSum] using hnorm
  exact raw_mean_le_of_explicit_target_bound f g X B _ hbound


end
end PvNP.RealizableHardness.MatrixLiftRowDiagnostic
