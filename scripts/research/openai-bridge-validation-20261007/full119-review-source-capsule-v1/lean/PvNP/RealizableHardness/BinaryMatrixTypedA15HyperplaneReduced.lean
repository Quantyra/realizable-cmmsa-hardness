import PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneGlobal

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReduced

open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15Hyperplane
open BinaryMatrixTypedA15HyperplaneGlobal BinaryMatrixFourier
open BinaryMatrixLineA15
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

def hyperplaneReducedMatrixEquiv {n d : ℕ} {A : Submodule F (V d)}
    {B : Submodule F (Fin n → F)} (H : Submodule F B) :
    ((V d ⧸ A) →ₗ[F] H) ≃ₗ[F]
      BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ A)) :=
  LinearMap.toMatrix (domainBasis A) (Module.finBasis F H)

theorem hyperplaneMatrix_subtype_firstRows {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (N : (V d ⧸ A) →ₗ[F] H)
    (i : Fin (Module.finrank F H))
    (j : Fin (Module.finrank F (V d ⧸ A))) :
    hyperplaneMatrixEquiv B H hH (H.subtype.comp N) i.castSucc j =
      hyperplaneReducedMatrixEquiv H N i j := by
  simp only [hyperplaneMatrixEquiv, hyperplaneReducedMatrixEquiv,
    LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, LinearMap.comp_apply,
    LinearMap.toMatrix_apply]
  simp only [Basis.equivFun_symm_single]
  simp only [Submodule.subtype_apply]
  rw [hyperplaneAdapted_apply_H]
  simp

theorem dropLastRow_hyperplaneMatrix_fixed_base {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B) (N : (V d ⧸ A) →ₗ[F] H) :
    dropLastRow (hyperplaneMatrixEquiv B H hH (T + H.subtype.comp N)) =
      dropLastRow (hyperplaneMatrixEquiv B H hH T) +
        hyperplaneReducedMatrixEquiv H N := by
  ext i j
  simp only [map_add, Matrix.add_apply]
  simpa [dropLastRow, dropLastMatrix] using
    hyperplaneMatrix_subtype_firstRows B H hH N i j

end
end PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReduced
