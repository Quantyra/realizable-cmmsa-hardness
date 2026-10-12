import PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobal

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15Reduced

open BinaryMatrixTypedA15OneStep BinaryMatrixTypedA15AdaptedGlobal
open BinaryMatrixTypedA15Transport BinaryMatrixFirstDerivative BinaryMatrixLineA15
open BinaryMatrixFourier BinaryMatrixComplexA15
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

def reducedMatrixEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A)) :
    (((V d ⧸ A) ⧸ L) →ₗ[F] B) ≃ₗ[F]
      BinaryMatrix (Module.finrank F B)
        (Module.finrank F ((V d ⧸ A) ⧸ L)) :=
  LinearMap.toMatrix (Module.finBasis F ((V d ⧸ A) ⧸ L))
    (codomainBasis B)

theorem lineSplit_mkQ_first {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (q : (V d ⧸ A) ⧸ L) :
    L.mkQ ((lineSplit L) (q, 0)) = q := by
  simp [lineSplit, Submodule.coe_prodEquivOfIsCompl',
    Submodule.mk_quotientEquivOfIsCompl_apply]

theorem lineAdapted_symm_cast_mkQ {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (j : Fin (Module.finrank F ((V d ⧸ A) ⧸ L))) :
    L.mkQ ((lineAdaptedEquiv L hL).symm (Pi.single j.castSucc 1)) =
      (Module.finBasis F ((V d ⧸ A) ⧸ L)) j := by
  have he : (lineAdaptedEquiv L hL).symm (Pi.single j.castSucc 1) =
      (lineSplit L) ((Module.finBasis F ((V d ⧸ A) ⧸ L)) j, 0) := by
    apply (lineAdaptedEquiv L hL).injective
    simp [lineAdaptedEquiv, finLastEquiv, Pi.single_apply,
      Finset.sum_ite_eq']
  rw [he, lineSplit_mkQ_first]

theorem dropLast_lineMatrix_comp_mkQ {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (N : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    dropLastMatrix (lineMatrixEquiv B L hL (N.comp L.mkQ)) =
      reducedMatrixEquiv B L N := by
  ext i j
  simp only [dropLastMatrix, lineMatrixEquiv, reducedMatrixEquiv,
    LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, LinearMap.comp_apply,
    LinearMap.toMatrix_apply]
  rw [lineAdapted_symm_cast_mkQ]
  rfl

theorem dropLast_lineMatrix_fixed_base {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (N : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    dropLastMatrix (lineMatrixEquiv B L hL (T + N.comp L.mkQ)) =
      dropLastMatrix (lineMatrixEquiv B L hL T) +
        reducedMatrixEquiv B L N := by
  ext i j
  simp only [map_add, Matrix.add_apply, dropLastMatrix]
  exact congrArg (fun x => lineMatrixEquiv B L hL T i j.castSucc + x)
    (congrFun (congrFun (dropLast_lineMatrix_comp_mkQ B L hL N) i) j)

def reducedAffineEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B) :
    (((V d ⧸ A) ⧸ L) →ₗ[F] B) ≃
      BinaryMatrix (Module.finrank F B)
        (Module.finrank F ((V d ⧸ A) ⧸ L)) where
  toFun N := dropLastMatrix (lineMatrixEquiv B L hL (T + N.comp L.mkQ))
  invFun X := (reducedMatrixEquiv B L).symm
    (X - dropLastMatrix (lineMatrixEquiv B L hL T))
  left_inv N := by
    change (reducedMatrixEquiv B L).symm
      (dropLastMatrix (lineMatrixEquiv B L hL (T + N.comp L.mkQ)) -
        dropLastMatrix (lineMatrixEquiv B L hL T)) = N
    rw [dropLast_lineMatrix_fixed_base]
    simp
  right_inv X := by
    change dropLastMatrix (lineMatrixEquiv B L hL
      (T + ((reducedMatrixEquiv B L).symm
        (X - dropLastMatrix (lineMatrixEquiv B L hL T))).comp L.mkQ)) = X
    rw [dropLast_lineMatrix_fixed_base]
    simp

end
end PvNP.RealizableHardness.BinaryMatrixTypedA15Reduced
