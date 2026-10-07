import PvNP.RealizableHardness.MatrixLiftNominalDomain
import PvNP.RealizableHardness.MatrixLiftLeftRowFactorTwo
import PvNP.RealizableHardness.MatrixLiftExactBudgetZoom
import PvNP.RealizableHardness.MatrixLiftRawDirectComparison

/-! The nominal matrix-lift comparison used by the changed-ambient inverse. -/
namespace PvNP.RealizableHardness.MatrixLiftNominalExactComparison

open scoped BigOperators
open GrassmannCounting MatrixGrassmannFibre MatrixLiftAffineTarget
open MatrixLiftLeftRowNormalForm MatrixLiftLeftRowFactorTwo
open MatrixLiftExactBudgetZoom

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The exact-budget zoom bound controls a fibre with an arbitrary fixed
row target. Zero-target rows are put into `H`; the remaining target has full
rank, so the sole loss is the binary factor two. -/
theorem fixed_row_target_mean_le_two_e {a b k r z w : Nat}
    (f : Frame V a) (g : Grass V (a + k) → ℝ) (hg : ∀ L, 0 ≤ g L)
    (e : ℝ) (he : 0 ≤ e)
    (X : V →ₗ[ZMod 2] Rows b) (hX : Function.Surjective X)
    (B : Fin k → Rows b) (hbk : b < k)
    (Q : Grass V a) (W : Grass V w) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q.val)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) =
      Q.val ⊓ zeroKernel X B)
    (hW : W.val = Q.val ⊔ zeroKernel X B)
    (hrd : r < a + k)
    (hbudget : a + (Module.finrank (ZMod 2) V - w) ≤ r)
    (hexact : ExactBudgetZoomBound r (a + k) g e) :
    (∑ N : rawTargetFibre X B, extensionTest f g N.val) /
      (Fintype.card (rawTargetFibre X B) : ℝ) ≤ 2 * e := by
  let H := zeroKernel X B
  have htarget :
      (∑ N : {N : FreeColumns (zeroKernel X B) k //
          rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B},
          liftScore f g (zeroKernel X B) N.val) /
        (Fintype.card {N : FreeColumns (zeroKernel X B) k //
          rowTarget (zeroKernel X B) (residualRowsFin X B) N = residualTargetFin B} : ℝ) ≤
      2 * ((∑ N : FreeColumns (zeroKernel X B) k,
          liftScore f g (zeroKernel X B) N) /
        (Fintype.card (FreeColumns (zeroKernel X B) k) : ℝ)) := by
    apply MatrixLiftRawDirectComparison.explicit_mean_le_twice
      (C := Fin (targetRank B) → ZMod 2) f g hg
      (zeroKernel X B) (residualRowsFin X B)
      (residualRowsFin_surjective X B hX) (residualTargetFin B)
      (residualTargetFin_full_rank B)
    exact MatrixLiftFullRowRankBridge.binary_target_half (targetRank B) k
      (targetRank_lt B hbk)
  have hhom := homogeneous_lift_density_of_exact_r Q W H f s
    hfQ hsQH hW hrd hbudget g e he hexact
  have hhomMean :
      (∑ N : FreeColumns H k, liftScore f g H N) /
        (Fintype.card (FreeColumns H k) : ℝ) ≤ e := by
    have hcard : (0 : ℝ) < (Fintype.card (FreeColumns H k) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := FreeColumns H k)
    apply (div_le_iff₀ hcard).2
    simpa only [H, liftScore_eq_homLiftTest] using hhom
  apply MatrixLiftLeftRowDirectTransport.raw_mean_le_of_explicit_target_bound
    f g X B (2 * e)
  exact htarget.trans (mul_le_mul_of_nonneg_left hhomMean (by norm_num))

end
end PvNP.RealizableHardness.MatrixLiftNominalExactComparison
