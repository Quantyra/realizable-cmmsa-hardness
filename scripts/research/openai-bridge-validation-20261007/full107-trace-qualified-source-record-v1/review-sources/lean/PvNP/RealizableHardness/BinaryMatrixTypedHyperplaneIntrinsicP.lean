import PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneGlobal
import Mathlib.LinearAlgebra.Dual.Basis

/-! Identify the adapted final coordinate with the intrinsic defining
functional of a codimension-one hyperplane. This is the first step toward
the manuscript's basis-independent hyperplane translation average. -/

namespace PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneIntrinsicP

open BinaryMatrixTypedA15Hyperplane BinaryMatrixTypedA15Transport
open BinaryMatrixTypedA15OneStep
open BinaryMatrixLineTranslation
open BinaryMatrixComplexA15
open BinaryMatrixFourier
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

private noncomputable instance {d : ℕ} {A : Submodule F (V d)} :
    Fintype ((V d ⧸ A) →ₗ[F] F) := by
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofFinite _

private noncomputable instance {n : ℕ} (B : Submodule F (Fin n → F)) :
    Fintype B := Fintype.ofFinite _

private noncomputable instance {n : ℕ} (B : Submodule F (Fin n → F))
    (ψ : B →ₗ[F] F) : Fintype {w : B // ψ w = 1} := Fintype.ofFinite _

/-- The manuscript's codomain-hyperplane translation average. The two
indices are independent and uniform on their finite fibres. -/
def intrinsicHyperplaneAverage {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (ψ : B →ₗ[F] F)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) : ℂ :=
  (∑ p : ((V d ⧸ A) →ₗ[F] F) × {w : B // ψ w = 1},
    f (M + p.1.smulRight p.2.1)) /
      Fintype.card (((V d ⧸ A) →ₗ[F] F) × {w : B // ψ w = 1})

def intrinsicHyperplaneP {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (ψ : B →ₗ[F] F) (j : ℕ)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    ((V d ⧸ A) →ₗ[F] B) → ℂ :=
  fun M =>
    (f M - ((2 ^ j : ℝ) : ℂ) * intrinsicHyperplaneAverage B ψ f M) -
      ((2 ^ (j + 1) : ℝ) : ℂ) *
        intrinsicHyperplaneAverage B ψ
          (fun X => f X - ((2 ^ j : ℝ) : ℂ) * intrinsicHyperplaneAverage B ψ f X) M

def hyperplaneDefiningFunctional {n : ℕ}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    B →ₗ[F] F :=
  (LinearMap.proj (Fin.last (Module.finrank F H))).comp
    (hyperplaneAdaptedEquiv B H hH).toLinearMap

theorem hyperplaneDefiningFunctional_ker {n : ℕ}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    LinearMap.ker (hyperplaneDefiningFunctional B H hH) = H := by
  apply le_antisymm
  · intro w hw
    let e := hyperplaneAdaptedEquiv B H hH
    let u : H := (Module.finBasis F H).equivFun.symm
      (fun i => e w i.castSucc)
    have he : e w = e (u : B) := by
      funext i
      induction i using Fin.lastCases with
      | last =>
          have hz : e w (Fin.last (Module.finrank F H)) = 0 := hw
          simpa [e, hyperplaneDefiningFunctional,
            hyperplaneAdapted_apply_H] using hz
      | cast i =>
          rw [hyperplaneAdapted_apply_H]
          simp only [Fin.lastCases_castSucc]
          simp only [u, LinearEquiv.apply_symm_apply]
    have hwu : w = (u : B) := e.injective he
    rw [hwu]
    exact u.property
  · intro w hw
    let u : H := ⟨w, hw⟩
    change hyperplaneDefiningFunctional B H hH (u : B) = 0
    simp [hyperplaneDefiningFunctional, hyperplaneAdapted_apply_H]

/-- The `ψ(w)=1` fibre is the full affine complement of H; the adapted
coordinates merely enumerate it by its first coordinates. -/
def hyperplaneShiftVectorIndex {n : ℕ}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    {w : B // hyperplaneDefiningFunctional B H hH w = 1} ≃
      (Fin (Module.finrank F H) → F) where
  toFun w i := hyperplaneAdaptedEquiv B H hH w.1 i.castSucc
  invFun c := ⟨(hyperplaneAdaptedEquiv B H hH).symm (Fin.lastCases 1 c), by
    simp [hyperplaneDefiningFunctional]⟩
  left_inv w := by
    apply Subtype.ext
    apply (hyperplaneAdaptedEquiv B H hH).injective
    funext i
    induction i using Fin.lastCases with
    | last => simpa [hyperplaneDefiningFunctional] using w.2.symm
    | cast i => simp
  right_inv c := by
    funext i
    simp

def hyperplaneShiftIndex {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    (((V d ⧸ A) →ₗ[F] F) ×
      {w : B // hyperplaneDefiningFunctional B H hH w = 1}) ≃
      ((Fin (Module.finrank F (V d ⧸ A)) → F) ×
        (Fin (Module.finrank F H) → F)) :=
  (domainBasis A).dualBasis.equivFun.toEquiv.prodCongr
    (hyperplaneShiftVectorIndex B H hH)

theorem hyperplaneMatrix_rankOne_shift {n d : ℕ}
    {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M : (V d ⧸ A) →ₗ[F] B)
    (φ : (V d ⧸ A) →ₗ[F] F)
    (w : {w : B // hyperplaneDefiningFunctional B H hH w = 1}) :
    hyperplaneMatrixEquiv B H hH (M + φ.smulRight w.1) =
      hyperplaneMatrixEquiv B H hH M +
        (lineShift ((domainBasis A).dualBasis.equivFun φ)
          (hyperplaneShiftVectorIndex B H hH w)).transpose := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
      have hwlast : hyperplaneAdaptedEquiv B H hH w.1
          (Fin.last (Module.finrank F H)) = 1 := w.property
      simp [hyperplaneMatrixEquiv, hyperplaneShiftVectorIndex,
        lineShift, lineFunctional, hwlast]
  | cast i =>
      simp [hyperplaneMatrixEquiv, hyperplaneShiftVectorIndex,
        lineShift, lineFunctional, Module.Basis.dualBasis_equivFun]

theorem intrinsicHyperplaneAverage_coordinate {n d : ℕ}
    {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    intrinsicHyperplaneAverage B (hyperplaneDefiningFunctional B H hH) f M =
      complexLineAverage
        (complexTranspose (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X)))
        (hyperplaneMatrixEquiv B H hH M).transpose := by
  unfold intrinsicHyperplaneAverage complexLineAverage
  let e := hyperplaneShiftIndex (A := A) B H hH
  let s := e.trans (Equiv.prodComm _ _)
  have hsum :
      (∑ p : ((V d ⧸ A) →ₗ[F] F) ×
          {w : B // hyperplaneDefiningFunctional B H hH w = 1},
        f (M + p.1.smulRight p.2.1)) =
      ∑ p : (Fin (Module.finrank F H) → F) ×
          (Fin (Module.finrank F (V d ⧸ A)) → F),
        f ((hyperplaneMatrixEquiv B H hH).symm
          ((hyperplaneMatrixEquiv B H hH M).transpose +
            lineShift p.2 p.1).transpose) := by
    apply Fintype.sum_equiv s
    intro p
    apply congrArg f
    apply (hyperplaneMatrixEquiv B H hH).injective
    have hs := hyperplaneMatrix_rankOne_shift B H hH M p.1 p.2
    simp only [s, e, Equiv.trans_apply, Equiv.prodComm_apply,
      hyperplaneShiftIndex] at hs ⊢
    rw [LinearEquiv.apply_symm_apply]
    simpa [Matrix.transpose_add] using hs
  rw [hsum]
  congr 1
  exact_mod_cast Fintype.card_congr s

/-- The manuscript hyperplane polynomial is exactly the coordinate
polynomial used by the typed A14/A15 proofs, at every input matrix. -/
theorem intrinsicHyperplaneP_eq_typed {n d : ℕ}
    {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (j : ℕ) (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    intrinsicHyperplaneP B (hyperplaneDefiningFunctional B H hH) j f =
      BinaryMatrixTypedA15HyperplaneGlobal.typedHyperplaneP B H hH j f := by
  funext M
  let e := hyperplaneMatrixEquiv (A := A) B H hH
  let g : BinaryMatrix (Module.finrank F H + 1)
      (Module.finrank F (V d ⧸ A)) → ℂ := fun X => f (e.symm X)
  let a : ℂ := ((2 ^ j : ℝ) : ℂ)
  let b : ℂ := ((2 ^ (j + 1) : ℝ) : ℂ)
  have hE (N : (V d ⧸ A) →ₗ[F] B) :
      intrinsicHyperplaneAverage B (hyperplaneDefiningFunctional B H hH) f N =
        complexLineAverage (complexTranspose g) (e N).transpose := by
    exact intrinsicHyperplaneAverage_coordinate B H hH f N
  have hE2 :
      intrinsicHyperplaneAverage B (hyperplaneDefiningFunctional B H hH)
        (fun X => f X - a *
          intrinsicHyperplaneAverage B (hyperplaneDefiningFunctional B H hH) f X) M =
      complexLineAverage
        (complexTranspose (fun X => g X - a *
          complexLineAverage (complexTranspose g) X.transpose))
        (e M).transpose := by
    rw [intrinsicHyperplaneAverage_coordinate]
    congr 1
    funext X
    simp only [complexTranspose]
    change f (e.symm X.transpose) - a *
      intrinsicHyperplaneAverage B (hyperplaneDefiningFunctional B H hH) f
        (e.symm X.transpose) = _
    rw [hE]
    simp [g]
  change f M - a * intrinsicHyperplaneAverage B
      (hyperplaneDefiningFunctional B H hH) f M -
      b * intrinsicHyperplaneAverage B
        (hyperplaneDefiningFunctional B H hH)
        (fun X => f X - a *
          intrinsicHyperplaneAverage B (hyperplaneDefiningFunctional B H hH) f X) M = _
  rw [hE, hE2]
  simp [BinaryMatrixTypedA15HyperplaneGlobal.typedHyperplaneP,
    complexHyperplaneP, complexLineP, complexLineIminusE,
    complexTranspose, g, e, a, b]
  congr 1
  funext X
  simp [complexTranspose, complexLineIminusE]

end
end PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneIntrinsicP
