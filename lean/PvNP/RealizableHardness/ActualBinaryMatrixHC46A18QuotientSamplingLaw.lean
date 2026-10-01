import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
The section-coordinate law behind the quotient-conditioned A18 step.

For fixed quotients `q : X' → X` and a section `s`, the unrestricted
functional coordinates are the linear functional `lambda` on `X`.  The
source sample consists of a map `R : X → B`, the reference functional on
`X'`, and the new vector `w`.  This file records the exact resulting map and
its section and distinguished-vector columns, plus its stable/expanded
codomain range.  It does not identify a globalness bound until the source
random choices are proved to be uniform in these coordinates.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18QuotientSamplingLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K X X' W : Type*} [Field K]
variable [AddCommGroup X] [Module K X]
variable [AddCommGroup X'] [Module K X']
variable [AddCommGroup W] [Module K W]

/-- The map on the enlarged quotient: the old random map factors through
`q`, while the functional coordinate contributes the new column. -/
def quotientSampleOutput (B : Submodule K W)
    (q : X' →ₗ[K] X) (phi₀ : X' →ₗ[K] K)
    (R : X →ₗ[K] B) (lambda : X →ₗ[K] K) (w : W) : X' →ₗ[K] W :=
  B.subtype.comp (R.comp q) + (phi₀ + lambda.comp q).smulRight w

/-- On the chosen section, the resulting column is exactly the old uniform
`B`-column plus the independent `lambda` bit times `w`. -/
theorem quotientSampleOutput_section (B : Submodule K W)
    (q : X' →ₗ[K] X) (s : X →ₗ[K] X') (phi₀ : X' →ₗ[K] K)
    (R : X →ₗ[K] B) (lambda : X →ₗ[K] K) (w : W)
    (hqs : q.comp s = LinearMap.id) (hphiS : phi₀.comp s = 0)
    (x : X) :
    quotientSampleOutput B q phi₀ R lambda w (s x) =
      (R x : W) + lambda x • w := by
  have hq : q (s x) = x := by
    have h := congrArg (fun f : X →ₗ[K] X => f x) hqs
    simpa using h
  have hphi : phi₀ (s x) = 0 := by
    have h := congrArg (fun f : X →ₗ[K] K => f x) hphiS
    simpa using h
  simp [quotientSampleOutput, hq, hphi]

/-- The distinguished new column is exactly `w`, independent of both old
map and quotient-functional coordinates. -/
theorem quotientSampleOutput_newColumn (B : Submodule K W)
    (q : X' →ₗ[K] X) (phi₀ : X' →ₗ[K] K)
    (R : X →ₗ[K] B) (lambda : X →ₗ[K] K) (w : W) (v : X')
    (hqv : q v = 0) (hphiV : phi₀ v = 1) :
    quotientSampleOutput B q phi₀ R lambda w v = w := by
  simp [quotientSampleOutput, hqv, hphiV]

/-- In the stable branch, where the new vector already lies in `B`, the
sampled map still has range in `B`. -/
theorem quotientSampleOutput_range_stable (B : Submodule K W)
    (q : X' →ₗ[K] X) (phi₀ : X' →ₗ[K] K)
    (R : X →ₗ[K] B) (lambda : X →ₗ[K] K) (w : W) (hw : w ∈ B) :
    LinearMap.range (quotientSampleOutput B q phi₀ R lambda w) ≤ B := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  change ((R (q x) : W) + (phi₀ x + lambda (q x)) • w) ∈ B
  exact B.add_mem (R (q x)).property (B.smul_mem _ hw)

/-- In the expanded branch, the sampled map has range in the actual enlarged
codomain subspace. -/
theorem quotientSampleOutput_range_expanded (B B' : Submodule K W)
    (hBB' : B ≤ B') (q : X' →ₗ[K] X) (phi₀ : X' →ₗ[K] K)
    (R : X →ₗ[K] B) (lambda : X →ₗ[K] K) (w : W) (hw : w ∈ B') :
    LinearMap.range (quotientSampleOutput B q phi₀ R lambda w) ≤ B' := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  change ((R (q x) : W) + (phi₀ x + lambda (q x)) • w) ∈ B'
  exact B'.add_mem (hBB' (R (q x)).property) (B'.smul_mem _ hw)

/-- In product coordinates, every linear map whose distinguished column is
w is uniquely a pair of an old-map coordinate and an independent
functional coordinate. This is the finite fibre bijection used after fixing
the parent subspace and the expanded codomain branch. -/
def productMapFromCoordinates (p : (X →ₗ[K] B) × (X →ₗ[K] K)) :
    X × K →ₗ[K] B × K :=
  LinearMap.prod
    (p.1.comp (LinearMap.fst K X K))
    (p.2.comp (LinearMap.fst K X K) + LinearMap.snd K X K)

def coordinatesOfMap (eD : X' ≃ₗ[K] X × K) (eC : W ≃ₗ[K] B × K)
    (N : X' →ₗ[K] W) : (X →ₗ[K] B) × (X →ₗ[K] K) :=
  let T := eC.toLinearMap.comp (N.comp eD.symm.toLinearMap)
  ( (LinearMap.fst K B K).comp
      (T.comp (LinearMap.inl K X K)),
    (LinearMap.snd K B K).comp
      (T.comp (LinearMap.inl K X K)) )

noncomputable def fixedColumnCoordinateEquiv
    (eD : X' ≃ₗ[K] X × K) (eC : W ≃ₗ[K] (B × K))
    (v : X') (w : W) (hDv : eD v = (0, 1)) (hCw : eC w = (0, 1)) :
    {N : X' →ₗ[K] W // N v = w} ≃
      (X →ₗ[K] B) × (X →ₗ[K] K) where
  toFun N := coordinatesOfMap eD eC N.1
  invFun p := by
    let T := productMapFromCoordinates p
    refine ⟨eC.symm.toLinearMap.comp (T.comp eD.toLinearMap), ?_⟩
    have hT : T (0, 1) = (0, 1) := by
      simp [T]
    have hsymm : eC.symm (0, 1) = w := by
      apply eC.injective
      simpa using hCw.symm
    change eC.symm (T (eD v)) = w
    rw [hDv, hT, hsymm]
  left_inv N := by
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    let T := eC.toLinearMap.comp (N.1.comp eD.symm.toLinearMap)
    let P := coordinatesOfMap eD eC N.1
    have hT : T (0, 1) = (0, 1) := by
      have h := congrArg eC.toLinearMap N.2
      change T (eD v) = eC w at h
      rw [hDv, hCw] at h
      exact h
    change eC.symm (T (eD z)) =
      eC.symm (productMapFromCoordinates P (eD z))
    apply congrArg eC.symm
    have hdecomp : eD z = ( (eD z).1, 0) + (0, (eD z).2) := by
      ext <;> simp
    rw [hdecomp, map_add]
    have hsecond :
        T (0, (eD z).2) = (eD z).2 • (0, 1) := by
      rw [show (0, (eD z).2) = (eD z).2 • (0, 1) by ext <;> simp]
      rw [map_smul, hT]
    rw [hsecond]
    have hfirst : T ((eD z).1, 0) = P.1 (eD z).1 := by
      rfl
    rw [hfirst]
    simp [P, coordinatesOfMap, productMapFromCoordinates]
  right_inv p := by
    apply Prod.ext
    · apply LinearMap.ext
      intro x
      simp [fixedColumnCoordinateEquiv]
    · apply LinearMap.ext
      intro x
      simp [fixedColumnCoordinateEquiv]

end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18QuotientSamplingLaw
