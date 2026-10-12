import PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneReduced
import PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase

namespace PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneFixedBase

open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15Hyperplane
open BinaryMatrixTypedA15HyperplaneGlobal BinaryMatrixTypedA15HyperplaneReduced
open BinaryMatrixTypedA15HyperplaneReducedGlobal
open BinaryMatrixTypedA14Hyperplane BinaryMatrixTypedA14HyperplaneReduced
open BinaryMatrixTypedA14Line BinaryMatrixTypedA14FixedBase
open BinaryMatrixComplexA14 BinaryMatrixComplexA15 BinaryMatrixCodomainA15
open BinaryMatrixFourier
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

set_option maxHeartbeats 800000 in
theorem typed_A14_fixedHyperplane {n d j : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (N : (V d ⧸ A) →ₗ[F] H) :
    hyperplaneReducedComplexRankProjection B H hH j
        (typedHyperplaneReducedWitness (k := j) B H hH T f) N =
      typedComplexHyperplaneFilter B H hH
        (typedComplexRankProjection A B (j + 1) f)
        (T + H.subtype.comp N) := by
  let e : ((V d ⧸ A) →ₗ[F] B) ≃ₗ[F]
      BinaryMatrix (Module.finrank F H + 1) (Module.finrank F (V d ⧸ A)) :=
    hyperplaneMatrixEquiv B H hH
  let r : ((V d ⧸ A) →ₗ[F] H) ≃ₗ[F]
      BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ A)) :=
    hyperplaneReducedMatrixEquiv H
  let t := hyperplaneBaseRow B H hH T
  let c := dropLastRow (e T)
  let fcoord : BinaryMatrix (Module.finrank F H + 1)
      (Module.finrank F (V d ⧸ A)) → ℂ := fun X => f (e.symm X)
  have hfull : e (T + H.subtype.comp N) = rawLastRow (r N + c) t := by
    rw [hyperplaneMatrix_rawLastRow, dropLastRow_hyperplaneMatrix_fixed_base]
    rw [add_comm (dropLastRow (hyperplaneMatrixEquiv B H hH T))
      (hyperplaneReducedMatrixEquiv H N)]
  have hinput : (fun X => typedComplexRankProjection A B (j + 1) f (e.symm X)) =
      complexRankProjection (j + 1) fcoord := by
    funext X
    simpa [fcoord, e] using
      typedRankProjection_hyperplaneCoordinate A B H hH f (e.symm X)
  rw [hyperplaneReducedRankProjection_coordinate]
  change complexRankProjection j
      (fun X => typedHyperplaneReducedWitness (k := j) B H hH T f
        ((hyperplaneReducedMatrixEquiv H).symm X))
      (r N) = _
  simp_rw [hyperplane_witness_coordinate_shift_complex (k := j) B H hH T f]
  let G : BinaryMatrix (Module.finrank F H)
      (Module.finrank F (V d ⧸ A)) → ℂ :=
    fun X => complexHyperplaneP j fcoord (rawLastRow X t)
  change complexRankProjection j (fun X => G (X + c)) (r N) = _
  rw [complexRankProjection_translate, complex_A14_fixedHyperplane]
  unfold complexHyperplaneDerivative complexHybridLineDerivative
  rw [← hinput]
  change complexHybridLineFilter
    (complexTranspose (fun X => typedComplexRankProjection A B (j + 1) f (e.symm X)))
    (rawLastRow (r N + c) t).transpose = _
  rw [← hfull]
  exact (typedHyperplaneFilter_coordinate A B H hH
    (typedComplexRankProjection A B (j + 1) f) (T + H.subtype.comp N)).symm

end
end PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneFixedBase
