import PvNP.RealizableHardness.BinaryMatrixTypedA14Reduced

namespace PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase

open BinaryMatrixFourier BinaryMatrixA1Complex BinaryMatrixComplexA14
open BinaryMatrixFirstDerivative BinaryMatrixLineA15
open BinaryMatrixTypedA14Line BinaryMatrixTypedA14Reduced
open BinaryMatrixTypedA15OneStep BinaryMatrixTypedA15Reduced
open BinaryMatrixTypedA15ReducedGlobal BinaryMatrixTypedA15Transport
open BinaryMatrixTypedA15AdaptedGlobal BinaryMatrixComplexA15
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

theorem complexFourierCoeff_translate {n d : ℕ}
    (f : BinaryMatrix n d → ℂ) (Y C : BinaryMatrix n d) :
    complexFourierCoeff (fun X => f (X + C)) Y =
      complexFourierCoeff f Y * (character Y C : ℂ) := by
  unfold complexFourierCoeff
  have hs :
      (∑ X : BinaryMatrix n d, f (X + C) * (character Y X : ℂ)) =
      ∑ Z : BinaryMatrix n d, f Z * (character Y (Z - C) : ℂ) := by
    apply Fintype.sum_equiv (Equiv.addRight C)
    intro X
    simp
  rw [hs]
  simp_rw [ZModModule.sub_eq_add, character_add_right]
  simp_rw [Complex.ofReal_mul, ← mul_assoc]
  rw [← Finset.sum_mul]
  ring

theorem complexRankProjection_translate {n d j : ℕ}
    (f : BinaryMatrix n d → ℂ) (C M : BinaryMatrix n d) :
    complexRankProjection j (fun X => f (X + C)) M =
      complexRankProjection j f (M + C) := by
  unfold complexRankProjection
  apply Finset.sum_congr rfl
  intro Y _
  rw [complexFourierCoeff_translate, character_add_right, Complex.ofReal_mul]
  ring

/-- The intrinsic complex A14 line identity at an arbitrary fixed affine
base, with full rank projection on the reduced typed carrier. -/
theorem typed_A14_fixedLine {n d j : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (N : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    reducedComplexRankProjection B L j
        (typedLineReducedWitness (k := j) B L hL T f) N =
      typedComplexLineFilter B L hL
        (typedComplexRankProjection A B (j + 1) f)
        (T + N.comp L.mkQ) := by
  let e := lineMatrixEquiv B L hL
  let r := reducedMatrixEquiv B L
  let t := lineBaseColumn B L hL T
  let c := dropLastMatrix (e T)
  let fcoord : BinaryMatrix (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) → ℂ :=
    fun X => f (e.symm X)
  let G : BinaryMatrix (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L)) → ℂ :=
    fun X => complexLineP j fcoord (rawLastColumn X t)
  have hG (X : BinaryMatrix (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L))) :
      typedLineReducedWitness (k := j) B L hL T f (r.symm X) = G (X + c) := by
    have hw := typed_line_coordinate_witness_fixed_base (k := j)
      B L hL T (r.symm X) f
    rw [dropLast_lineMatrix_fixed_base] at hw
    rw [r.apply_symm_apply] at hw
    rw [add_comm c X] at hw
    rw [typedLineP_coordinate B L hL j f
      ((lineMatrixEquiv B L hL).symm
        (rawLastColumn (X + c) t))] at hw
    rw [(lineMatrixEquiv B L hL).apply_symm_apply] at hw
    change typedLineP B L hL j f (T + (r.symm X).comp L.mkQ) =
      complexLineP j fcoord (rawLastColumn (X + c) t)
    exact hw
  have hfull : e (T + N.comp L.mkQ) = rawLastColumn (r N + c) t := by
    rw [lineMatrix_rawLastColumn, dropLast_lineMatrix_fixed_base]
    rw [add_comm (dropLastMatrix (lineMatrixEquiv B L hL T)) (reducedMatrixEquiv B L N)]
  have hinput : (fun X => typedComplexRankProjection A B (j + 1) f (e.symm X)) =
      complexRankProjection (j + 1) fcoord := by
    funext X
    simpa [fcoord, e] using
      typedRankProjection_lineCoordinate A B L hL f (e.symm X)
  rw [reducedRankProjection_coordinate]
  change complexRankProjection j
      (fun X => typedLineReducedWitness (k := j) B L hL T f (r.symm X))
      (r N) = _
  simp_rw [hG]
  rw [complexRankProjection_translate, complex_A14_fixedLine]
  unfold complexHybridLineDerivative
  rw [← hinput]
  rw [← hfull]
  exact (typedLineFilter_coordinate A B L hL
    (typedComplexRankProjection A B (j + 1) f) (T + N.comp L.mkQ)).symm

end
end PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase
