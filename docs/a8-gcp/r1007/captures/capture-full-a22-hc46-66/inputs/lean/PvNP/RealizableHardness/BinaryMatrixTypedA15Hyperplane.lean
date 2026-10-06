import PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15Hyperplane

open BinaryMatrixFourier BinaryMatrixCodomainA15 BinaryMatrixLineA15
  BinaryMatrixFirstDerivative
open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15OneStep
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

def hyperplaneComplement {n : ℕ} (B : Submodule F (Fin n → F))
    (H : Submodule F B) : Submodule F B :=
  Classical.choose H.exists_isCompl

theorem hyperplaneComplement_isCompl {n : ℕ} (B : Submodule F (Fin n → F))
    (H : Submodule F B) : IsCompl H (hyperplaneComplement B H) :=
  Classical.choose_spec H.exists_isCompl

def hyperplaneScalarEquiv {n : ℕ} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    hyperplaneComplement B H ≃ₗ[F] F := by
  have hr : Module.finrank F (hyperplaneComplement B H) = 1 := by
    simpa using (Submodule.quotientEquivOfIsCompl H (hyperplaneComplement B H)
      (hyperplaneComplement_isCompl B H)).finrank_eq.symm.trans hH
  haveI : Nontrivial (hyperplaneComplement B H) :=
    Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank F (hyperplaneComplement B H))
  let v : hyperplaneComplement B H := Classical.choose (exists_ne (0 : hyperplaneComplement B H))
  have hv : v ≠ 0 := Classical.choose_spec (exists_ne (0 : hyperplaneComplement B H))
  let b := FiniteDimensional.basisSingleton Unit hr v hv
  exact b.equivFun.trans (LinearEquiv.funUnique Unit F F)

def hyperplaneAdaptedEquiv {n : ℕ} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    B ≃ₗ[F] (Fin (Module.finrank F H + 1) → F) :=
  ((Submodule.prodEquivOfIsCompl H (hyperplaneComplement B H)
      (hyperplaneComplement_isCompl B H)).symm.trans
    ((Module.finBasis F H).equivFun.prodCongr
      (hyperplaneScalarEquiv B H hH))).trans
        (finLastEquiv (Module.finrank F H))

theorem hyperplaneAdapted_apply_H {n : ℕ} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (u : H) :
    hyperplaneAdaptedEquiv B H hH u =
      Fin.lastCases 0 ((Module.finBasis F H).equivFun u) := by
  simp [hyperplaneAdaptedEquiv, finLastEquiv]

def hyperplaneMatrixEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    ((V d ⧸ A) →ₗ[F] B) ≃ₗ[F]
      BinaryMatrix (Module.finrank F H + 1) (Module.finrank F (V d ⧸ A)) :=
  (LinearEquiv.arrowCongr (domainBasis A).equivFun
    (hyperplaneAdaptedEquiv B H hH)).trans LinearMap.toMatrix'

def hyperplaneBaseRow {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B) : Fin (Module.finrank F (V d ⧸ A)) → F :=
  fun j => hyperplaneMatrixEquiv B H hH T (Fin.last (Module.finrank F H)) j

theorem hyperplaneMatrix_finalRow_fixed {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B) (N : (V d ⧸ A) →ₗ[F] H)
    (j : Fin (Module.finrank F (V d ⧸ A))) :
    hyperplaneMatrixEquiv B H hH (T + H.subtype.comp N)
      (Fin.last (Module.finrank F H)) j =
      hyperplaneBaseRow B H hH T j := by
  simp only [hyperplaneBaseRow, hyperplaneMatrixEquiv,
    LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, LinearMap.add_apply, LinearMap.comp_apply]
  rw [map_add]
  have hz : hyperplaneAdaptedEquiv B H hH (N ((domainBasis A) j))
      (Fin.last (Module.finrank F H)) = 0 := by
    rw [hyperplaneAdapted_apply_H]
    simp
  simp [hz]

def dropLastRow {p q : ℕ} (M : BinaryMatrix (p + 1) q) :
    BinaryMatrix p q :=
  (dropLastMatrix M.transpose).transpose

theorem hyperplaneMatrix_rawLastRow {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B) (N : (V d ⧸ A) →ₗ[F] H) :
    hyperplaneMatrixEquiv B H hH (T + H.subtype.comp N) =
      rawLastRow
        (dropLastRow (hyperplaneMatrixEquiv B H hH (T + H.subtype.comp N)))
        (hyperplaneBaseRow B H hH T) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
      simpa [rawLastRow, rawLastColumn] using
        hyperplaneMatrix_finalRow_fixed B H hH T N j
  | cast i =>
      simp [rawLastRow, rawLastColumn, dropLastRow, dropLastMatrix]

end
end BinaryMatrixTypedA15Hyperplane
