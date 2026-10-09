import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

/-!
Finite image fibres for binary matrices.  The important count is kept
conditional on a fixed image subspace: right basis changes do not identify
different image subspaces.
-/

namespace PvNP.RealizableHardness.ActualFiniteBinaryImageFibres

open PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Coord (n : Nat) := Fin n → ZMod 2
abbrev BMat (n d : Nat) := Matrix (Fin n) (Fin d) (ZMod 2)

/-- Rank-`i` matrices with a specified linear-map image `E`. -/
def MatrixImageFibre (n d i : Nat) (E : Submodule (ZMod 2) (Coord n)) :=
  {A : BMat n d // A.rank = i ∧ LinearMap.range A.mulVecLin = E}

/-- Surjections from the domain coordinate space onto the fixed image. -/
def SurjectionImageFibre {n : Nat} (d : Nat) (E : Submodule (ZMod 2) (Coord n)) :=
  {f : Coord d →ₗ[ZMod 2] E // Function.Surjective f}

private def restrictMatrixToImage {n d i : Nat}
    {E : Submodule (ZMod 2) (Coord n)}
    (A : MatrixImageFibre n d i E) : Coord d →ₗ[ZMod 2] E :=
  A.val.mulVecLin.codRestrict E (fun x => by
    have hle : LinearMap.range A.val.mulVecLin ≤ E := le_of_eq A.property.2
    exact hle (LinearMap.mem_range_self _ x))

private theorem restrictMatrixToImage_surjective {n d i : Nat}
    {E : Submodule (ZMod 2) (Coord n)} (A : MatrixImageFibre n d i E) :
    Function.Surjective (restrictMatrixToImage A) := by
  intro y
  have hy : y.val ∈ LinearMap.range A.val.mulVecLin :=
    A.property.2.symm ▸ y.property
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simpa [restrictMatrixToImage, LinearMap.codRestrict_apply] using hx

private def imageSurjectionMatrix {n d : Nat}
    {E : Submodule (ZMod 2) (Coord n)}
    (f : SurjectionImageFibre d E) : BMat n d :=
  Matrix.toLin'.symm (E.subtype.comp f.val)

private theorem subtype_comp_surjection_range {n d : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (f : Coord d →ₗ[ZMod 2] E) (hf : Function.Surjective f) :
    LinearMap.range (E.subtype.comp f) = E := by
  rw [LinearMap.range_comp_of_range_eq_top E.subtype
    (LinearMap.range_eq_top.mpr hf), Submodule.range_subtype]

private theorem imageSurjectionMatrix_spec {n d i : Nat}
    {E : Submodule (ZMod 2) (Coord n)} (hE : Module.finrank (ZMod 2) E = i)
    (f : SurjectionImageFibre d E) :
    (imageSurjectionMatrix f).rank = i ∧
      LinearMap.range (imageSurjectionMatrix f).mulVecLin = E := by
  have hlin : (imageSurjectionMatrix f).mulVecLin = E.subtype.comp f.val := by
    change Matrix.toLin' (Matrix.toLin'.symm (E.subtype.comp f.val)) = _
    exact Matrix.toLin'.apply_symm_apply _
  constructor
  · change (imageSurjectionMatrix f).rank = i
    change Module.finrank (ZMod 2)
      (LinearMap.range (imageSurjectionMatrix f).mulVecLin) = i
    rw [hlin, subtype_comp_surjection_range E f.val f.property, hE]
  · change LinearMap.range (imageSurjectionMatrix f).mulVecLin = E
    rw [hlin, subtype_comp_surjection_range E f.val f.property]

private theorem imageSurjectionMatrix_linearMap {n d : Nat}
    {E : Submodule (ZMod 2) (Coord n)} (f : SurjectionImageFibre d E) :
    (imageSurjectionMatrix f).mulVecLin = E.subtype.comp f.val := by
  change Matrix.toLin' (Matrix.toLin'.symm (E.subtype.comp f.val)) = _
  exact Matrix.toLin'.apply_symm_apply _

/-- A fixed-image matrix fibre is equivalent to actual surjections onto `E`.
The only dimensional input is the actual finrank of `E`. -/
def matrixImageFibreEquivSurjections {n d i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i) :
    MatrixImageFibre n d i E ≃ SurjectionImageFibre d E where
  toFun A := ⟨restrictMatrixToImage A, restrictMatrixToImage_surjective A⟩
  invFun f := ⟨imageSurjectionMatrix f, imageSurjectionMatrix_spec hE f⟩
  left_inv A := by
    apply Subtype.ext
    apply Matrix.toLin'.injective
    change Matrix.toLin' (Matrix.toLin'.symm
      (E.subtype.comp (restrictMatrixToImage A))) = Matrix.toLin' A.val
    rw [Matrix.toLin'.apply_symm_apply, Matrix.toLin'_apply']
    ext x
    simp [restrictMatrixToImage, LinearMap.codRestrict_apply]
  right_inv f := by
    let A : MatrixImageFibre n d i E :=
      ⟨imageSurjectionMatrix f, imageSurjectionMatrix_spec hE f⟩
    have hlin := imageSurjectionMatrix_linearMap f
    have hm : restrictMatrixToImage A = f.val := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change A.val.mulVecLin x = E.subtype (f.val x)
      rw [show A.val = imageSurjectionMatrix f from rfl, hlin]
      rfl
    exact Subtype.ext hm

/-- The fixed-image fibre count is the finite surjection count, with no
global averaging over distinct image subspaces. -/
theorem card_matrixImageFibre {n d i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i) :
    Nat.card (MatrixImageFibre n d i E) = frameProduct d i := by
  rw [Nat.card_congr (matrixImageFibreEquivSurjections E hE)]
  change Nat.card {f : Coord d →ₗ[ZMod 2] E // Function.Surjective f} =
    frameProduct d i
  rw [card_surjective_linear_maps (V := Coord d) (W := E)]
  simp [Coord, hE]

/-! ### Appending zero columns

The next equivalence is the fixed-image version of retaining just the
zero-appended matrices.  It is stated first for linear maps: a map on the
larger coordinate domain is retained exactly when it kills the appended
coordinate summand.  The equivalence identifies that retained fibre with
surjections from the base coordinate space onto the *same* image `E`.
-/

abbrev LinearMapImageFibre {n : Nat} (d : Nat) (E : Submodule (ZMod 2) (Coord n)) :=
  {f : Coord d →ₗ[ZMod 2] E // Function.Surjective f}

def appendDomainEquiv (c s : Nat) :
    (Coord c × Coord s) ≃ₗ[ZMod 2] Coord (c + s) where
  toFun p j := Sum.elim p.1 p.2 (finSumFinEquiv.symm j)
  invFun x :=
    (fun j => x (finSumFinEquiv (Sum.inl j)),
      fun j => x (finSumFinEquiv (Sum.inr j)))
  map_add' x y := by
    ext j
    rcases h : finSumFinEquiv.symm j with k | k <;> simp [h]
  map_smul' a x := by
    ext j
    rcases h : finSumFinEquiv.symm j with k | k <;> simp [h]
  left_inv := by
    rintro ⟨x, y⟩
    simp
  right_inv := by
    intro x
    funext j
    rcases h : finSumFinEquiv.symm j with k | k
    · have hj : j = finSumFinEquiv (Sum.inl k) := by
        have he := congrArg finSumFinEquiv h
        simpa using he
      simp [hj]
    · have hj : j = finSumFinEquiv (Sum.inr k) := by
        have he := congrArg finSumFinEquiv h
        simpa using he
      simp [hj]

def appendLeftProjection (c s : Nat) :
    Coord (c + s) →ₗ[ZMod 2] Coord c :=
  (LinearMap.fst (ZMod 2) (Coord c) (Coord s)).comp
    (appendDomainEquiv c s).symm.toLinearMap

def appendRightInjection (c s : Nat) :
    Coord s →ₗ[ZMod 2] Coord (c + s) :=
  (appendDomainEquiv c s).toLinearMap.comp
    (LinearMap.inr (ZMod 2) (Coord c) (Coord s))

def appendLeftInjection (c s : Nat) :
    Coord c →ₗ[ZMod 2] Coord (c + s) :=
  (appendDomainEquiv c s).toLinearMap.comp
    (LinearMap.inl (ZMod 2) (Coord c) (Coord s))

theorem appendLeftProjection_surjective (c s : Nat) :
    Function.Surjective (appendLeftProjection c s) := by
  intro x
  refine ⟨appendLeftInjection c s x, ?_⟩
  simp [appendLeftProjection, appendLeftInjection]

theorem appendDomain_decomposition (c s : Nat) (x : Coord (c + s)) :
    appendLeftInjection c s (appendLeftProjection c s x) +
      appendRightInjection c s ((appendDomainEquiv c s).symm x).2 = x := by
  apply (appendDomainEquiv c s).symm.injective
  simp [appendLeftInjection, appendRightInjection, appendLeftProjection]

def AppendedZeroSurjectionFibre {n : Nat} (c s : Nat)
    (E : Submodule (ZMod 2) (Coord n)) :=
  {f : Coord (c + s) →ₗ[ZMod 2] E //
    Function.Surjective f ∧ f.comp (appendRightInjection c s) = 0}

def appendedZeroSurjectionEquiv {n c s : Nat}
    (E : Submodule (ZMod 2) (Coord n)) :
    AppendedZeroSurjectionFibre c s E ≃ LinearMapImageFibre c E where
  toFun f := ⟨f.val.comp (appendLeftInjection c s), by
    intro y
    obtain ⟨x, hx⟩ := f.property.1 y
    refine ⟨appendLeftProjection c s x, ?_⟩
    have hdecomp := appendDomain_decomposition c s x
    have hkill' : f.val (appendRightInjection c s ((appendDomainEquiv c s).symm x).2) = 0 := by
      simpa [LinearMap.comp_apply] using
        (LinearMap.ext_iff.mp f.property.2) ((appendDomainEquiv c s).symm x).2
    have := congrArg f.val hdecomp
    simp only [map_add, LinearMap.comp_apply] at this
    rw [hkill'] at this
    simpa [LinearMap.comp_apply] using this.trans hx⟩
  invFun g := ⟨g.val.comp (appendLeftProjection c s), by
    constructor
    · intro y
      obtain ⟨x, hx⟩ := g.property y
      refine ⟨appendLeftInjection c s x, ?_⟩
      simpa [appendLeftProjection, appendLeftInjection] using hx
    · apply LinearMap.ext
      intro x
      have hproj : appendLeftProjection c s (appendRightInjection c s x) = 0 := by
        simp [appendLeftProjection, appendRightInjection, appendDomainEquiv] <;>
          funext j <;> rfl
      change g.val (appendLeftProjection c s (appendRightInjection c s x)) = 0
      rw [hproj]
      simp⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hdecomp := appendDomain_decomposition c s x
    have hkill := (LinearMap.ext_iff.mp f.property.2)
      ((appendDomainEquiv c s).symm x).2
    have hkill' : f.val (appendRightInjection c s ((appendDomainEquiv c s).symm x).2) = 0 := by
      simpa [LinearMap.comp_apply] using hkill
    have := congrArg f.val hdecomp
    simp only [map_add, LinearMap.comp_apply] at this
    rw [hkill'] at this
    simpa [LinearMap.comp_apply] using this
  right_inv g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [appendLeftProjection, appendLeftInjection, appendDomainEquiv]

theorem card_appendedZeroSurjectionFibre {n c s : Nat}
    (E : Submodule (ZMod 2) (Coord n)) :
    Nat.card (AppendedZeroSurjectionFibre c s E) =
      frameProduct c (Module.finrank (ZMod 2) E) := by
  rw [Nat.card_congr (appendedZeroSurjectionEquiv E)]
  change Nat.card {f : Coord c →ₗ[ZMod 2] E // Function.Surjective f} =
    frameProduct c (Module.finrank (ZMod 2) E)
  simpa [Coord, Module.finrank_fintype_fun_eq_card] using
    (card_surjective_linear_maps (V := Coord c) (W := E))

end
end PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
