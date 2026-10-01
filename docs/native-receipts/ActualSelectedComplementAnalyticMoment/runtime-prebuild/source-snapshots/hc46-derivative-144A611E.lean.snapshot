import PvNP.RealizableHardness.BinaryMatrixA1Composition
import PvNP.RealizableHardness.BinaryMatrixLineA14
import PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase
import PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobal

/-!
The first positive-rank HC46 engine bridge.  This file keeps the manuscript's
actual affine restriction, hybrid Fourier filter, and line derivative
operators together at the boundary where the rank loss is used by (A14).
The component proofs remain in their focused operator files; this module
exports their source-shaped composition for the HC46 chain.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46Derivative

open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixA1Composition
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open PvNP.RealizableHardness.BinaryMatrixHybridSelector
open PvNP.RealizableHardness.BinaryMatrixLineTranslation
open PvNP.RealizableHardness.BinaryMatrixLineA14
open PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase
open PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobal
open PvNP.RealizableHardness.BinaryMatrixTypedA14Line
open PvNP.RealizableHardness.BinaryMatrixTypedA14Reduced
open PvNP.RealizableHardness.BinaryMatrixTypedA15OneStep
open PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixFirstDerivative
open PvNP.RealizableHardness.BinaryMatrixLineA15

set_option autoImplicit false
noncomputable section

/-- Actual affine restriction after the hybrid Fourier filter, composed
through nested left/right constraints, equals the single restriction/filter
at the composed affine base.  This is the manuscript's (A1) operator
identity used to iterate the derivative argument. -/
theorem actual_affine_hybrid_composition {n d : ℕ}
    (A₂ A₁ : Submodule (ZMod 2) (Fin d → ZMod 2))
    (B₁ B₂ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (S : ((Fin d → ZMod 2) ⧸ A₂) →ₗ[ZMod 2] B₂)
    (f : BinaryMatrix n d → ℝ)
    (N : (((Fin d → ZMod 2) ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[ZMod 2]
      B₁.comap B₂.subtype) :
    carrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
      (carrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
        (fun M => ambientAffineRestrict A₂ B₂ T
          (ambientHybridFilter A₂ B₂ f) M)) N =
      ambientAffineRestrict A₁ B₁
        (T + B₂.subtype.comp (S.comp A₂.mkQ))
        (ambientHybridFilter A₁ B₁ f)
        (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) := by
  exact manuscript_A1_restrict_filter A₂ A₁ B₁ B₂ hA hB T S f N

/-- The line restriction/rank-projection identity (A14), with the actual
line-averaging polynomial and actual hybrid derivative.  The selector's
rank-loss equation ensures precisely the selected rank-`j+1` frequencies
contribute to output rank `j`; equal induced frequencies are summed before
projection. -/
theorem actual_line_rank_projection_derivative_A14 {n d j : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n d) :
    rankProjection j (rawLastColumnRestrict t (lineP j f)) M =
      hybridLineDerivative t (rankProjection (j + 1) f) M := by
  exact rankProjection_rawRestrict_lineP_eq_hybridDerivative t f M

/-- Same-line positive-rank bridge for the next HC46 step: the actual
one-step A15 globalness witness and the actual typed A14 rank-`j` derivative
identity hold together for the same source function, fixed affine base, and
line. This keeps the operator identity available at every subsequent base
while the A15 bound is applied to the line witness. -/
theorem actual_typed_line_A14_A15_step {n d k : ℕ} {ε : ℝ}
    (A : Submodule (ZMod 2) (Fin d → ZMod 2))
    (B : Submodule (ZMod 2) (Fin n → ZMod 2))
    (L : Submodule (ZMod 2) ((Fin d → ZMod 2) ⧸ A))
    (hL : Module.finrank (ZMod 2) L = 1)
    (T : ((Fin d → ZMod 2) ⧸ A) →ₗ[ZMod 2] B)
    (f : (((Fin d → ZMod 2) ⧸ A) →ₗ[ZMod 2] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A B (k + 1) ε f) :
    UpToActualNormSqGlobal k (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun X => typedLineP B L hL k f
        ((lineMatrixEquiv B L hL).symm
          (rawLastColumn X (lineBaseColumn B L hL T)))) ∧
    (∀ N : (((Fin d → ZMod 2) ⧸ A) ⧸ L) →ₗ[ZMod 2] B,
      reducedComplexRankProjection B L k (typedLineReducedWitness (k := k) B L hL T f) N =
        typedComplexLineFilter B L hL
          (typedComplexRankProjection A B (k + 1) f)
          (T + N.comp L.mkQ)) := by
  constructor
  · exact typed_line_coordinate_witness_global A B L hL T f hε hf
  · intro N
    exact typed_A14_fixedLine A B L hL T f N

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46Derivative
