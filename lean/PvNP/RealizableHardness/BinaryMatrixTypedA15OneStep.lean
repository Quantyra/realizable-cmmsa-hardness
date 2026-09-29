import PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15OneStep

open BinaryMatrixTypedA15Transport
open BinaryMatrixFourier BinaryMatrixFirstDerivative
open BinaryMatrixLineA15
open BinaryMatrixLineTranslation
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

/-- Put the one-dimensional constraint in the final coordinate. The
coordinate map is used below to compare the actual typed line average
with the fixed-final-column complex A14/A15 operators. -/
def finLastEquiv (q : ℕ) :
    ((Fin q → F) × F) ≃ₗ[F] (Fin (q + 1) → F) where
  toFun p := Fin.lastCases p.2 p.1
  invFun v := (fun i => v i.castSucc, v (Fin.last q))
  left_inv p := by
    cases p with
    | mk a b =>
      simp only [Prod.mk.injEq]
      constructor
      · funext i
        simp
      · simp
  right_inv v := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  map_add' p r := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  map_smul' a p := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp

def lineScalarEquiv {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1) :
    L ≃ₗ[F] F := by
  haveI : Nontrivial L := Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank F L)
  let v : L := Classical.choose (exists_ne (0 : L))
  have hv : v ≠ 0 := Classical.choose_spec (exists_ne (0 : L))
  let b := FiniteDimensional.basisSingleton Unit hL v hv
  exact b.equivFun.trans (LinearEquiv.funUnique Unit F F)

def lineComplement {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) : Submodule F (V d ⧸ A) :=
  Classical.choose L.exists_isCompl

theorem lineComplement_isCompl {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) : IsCompl L (lineComplement L) :=
  Classical.choose_spec L.exists_isCompl

def lineSplit {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) :
    (((V d ⧸ A) ⧸ L) × L) ≃ₗ[F] (V d ⧸ A) :=
  ((Submodule.quotientEquivOfIsCompl L (lineComplement L)
      (lineComplement_isCompl L)).prodCongr (LinearEquiv.refl F L)).trans
    (Submodule.prodEquivOfIsCompl (lineComplement L) L
      (lineComplement_isCompl L).symm)

def lineAdaptedEquiv {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1) :
    (V d ⧸ A) ≃ₗ[F]
      (Fin (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) → F) :=
  ((lineSplit L).symm.trans
    ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.prodCongr
      (lineScalarEquiv L hL))).trans
        (finLastEquiv (Module.finrank F ((V d ⧸ A) ⧸ L)))

theorem lineSplit_symm_apply_line {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (u : L) :
    (lineSplit L).symm u = (0, u) := by
  simp [lineSplit]

theorem lineAdapted_apply_line {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (u : L) :
    lineAdaptedEquiv L hL u =
      Fin.lastCases (lineScalarEquiv L hL u)
        (fun _ : Fin (Module.finrank F ((V d ⧸ A) ⧸ L)) => 0) := by
  simp [lineAdaptedEquiv, lineSplit_symm_apply_line,
    finLastEquiv]
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

def lineMatrixEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1) :
    ((V d ⧸ A) →ₗ[F] B) ≃ₗ[F]
      BinaryMatrix (Module.finrank F B)
        (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) :=
  (LinearEquiv.arrowCongr (lineAdaptedEquiv L hL)
    (codomainBasis B).equivFun).trans LinearMap.toMatrix'

def lineBaseColumn {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B) : Fin (Module.finrank F B) → F :=
  fun i => lineMatrixEquiv B L hL T i
    (Fin.last (Module.finrank F ((V d ⧸ A) ⧸ L)))

theorem lineAdapted_symm_last {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1) :
    (lineAdaptedEquiv L hL).symm
      (Pi.single (Fin.last (Module.finrank F ((V d ⧸ A) ⧸ L))) 1) =
        ((lineScalarEquiv L hL).symm 1 : L) := by
  apply (lineAdaptedEquiv L hL).injective
  rw [LinearEquiv.apply_symm_apply, lineAdapted_apply_line]
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

/-- The arbitrary typed line constraint fixes exactly the final source
column at the prescribed base under its adapted coordinate map. -/
theorem lineMatrix_finalColumn_fixed {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (N : ((V d ⧸ A) ⧸ L) →ₗ[F] B)
    (i : Fin (Module.finrank F B)) :
    lineMatrixEquiv B L hL (T + N.comp L.mkQ) i
        (Fin.last (Module.finrank F ((V d ⧸ A) ⧸ L))) =
      lineBaseColumn B L hL T i := by
  simp only [lineBaseColumn, lineMatrixEquiv,
    LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  rw [lineAdapted_symm_last L hL]
  have hq : L.mkQ (↑((lineScalarEquiv L hL).symm 1) : V d ⧸ A) = 0 := by
    simp
  simp [hq]

/-- Exact fixed-base one-step restriction diagram: the full typed source
matrix has its last column prescribed by T and its other columns free. -/
theorem lineMatrix_rawLastColumn {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (N : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    lineMatrixEquiv B L hL (T + N.comp L.mkQ) =
      rawLastColumn
        (dropLastMatrix (lineMatrixEquiv B L hL (T + N.comp L.mkQ)))
        (lineBaseColumn B L hL T) := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
      simpa [rawLastColumn] using
        lineMatrix_finalColumn_fixed B L hL T N i
  | cast j =>
      simp [rawLastColumn, dropLastMatrix]

def adaptedFunctional {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (φ : (V d ⧸ A) →ₗ[F] F) :
    Fin (Module.finrank F ((V d ⧸ A) ⧸ L)) → F :=
  fun j => φ ((lineAdaptedEquiv L hL).symm (Pi.single j.castSucc 1))

def inverseAdaptedFunctional {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (c : Fin (Module.finrank F ((V d ⧸ A) ⧸ L)) → F) :
    (V d ⧸ A) →ₗ[F] F :=
  ((∑ j : Fin (Module.finrank F ((V d ⧸ A) ⧸ L)),
      c j • (LinearMap.proj j.castSucc :
        (Fin (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) → F) →ₗ[F] F)) +
      (LinearMap.proj (Fin.last (Module.finrank F ((V d ⧸ A) ⧸ L))) :
        (Fin (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) → F) →ₗ[F] F)).comp
    (lineAdaptedEquiv L hL).toLinearMap

theorem inverseAdaptedFunctional_last {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (c : Fin (Module.finrank F ((V d ⧸ A) ⧸ L)) → F) :
    inverseAdaptedFunctional L hL c
      ((lineScalarEquiv L hL).symm 1 : L) = 1 := by
  simp [inverseAdaptedFunctional, lineAdapted_apply_line]

theorem adaptedFunctional_inverse {d : ℕ} {A : Submodule F (V d)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (c : Fin (Module.finrank F ((V d ⧸ A) ⧸ L)) → F) :
    adaptedFunctional L hL (inverseAdaptedFunctional L hL c) = c := by
  funext j
  simp [adaptedFunctional, inverseAdaptedFunctional, Pi.single_apply,
    Finset.sum_ite_eq']

theorem lineMatrix_rankOne_shift {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (M : (V d ⧸ A) →ₗ[F] B) (w : B)
    (φ : (V d ⧸ A) →ₗ[F] F)
    (hφ : φ ((lineScalarEquiv L hL).symm 1 : L) = 1) :
    lineMatrixEquiv B L hL (M + φ.smulRight w) =
      lineMatrixEquiv B L hL M +
        lineShift ((codomainBasis B).equivFun w)
          (adaptedFunctional L hL φ) := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
      have hlast := lineAdapted_symm_last L hL
      simp only [lineMatrixEquiv, LinearEquiv.trans_apply,
        LinearMap.toMatrix'_apply, LinearEquiv.arrowCongr_apply,
        LinearMap.add_apply, LinearMap.smulRight_apply]
      simp [lineShift, lineFunctional, hφ, hlast]
  | cast j =>
      simp only [lineMatrixEquiv, LinearEquiv.trans_apply,
        LinearMap.toMatrix'_apply, LinearEquiv.arrowCongr_apply,
        LinearMap.add_apply, LinearMap.smulRight_apply]
      simp [lineShift, lineFunctional, adaptedFunctional, mul_comm]

end
end PvNP.RealizableHardness.BinaryMatrixTypedA15OneStep
