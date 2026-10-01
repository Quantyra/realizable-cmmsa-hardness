import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualFiniteBinaryImageFibres

/-!
Transitivity of the right general-linear action on surjections with a fixed
image.  The statement is deliberately about a fixed codomain: it is the
orbit fact needed to make Fourier coefficients constant separately on each
image fibre, and does not identify different image subspaces.
-/

namespace PvNP.RealizableHardness.ActualFiniteBinaryImageOrbit

open PvNP.RealizableHardness.ActualFiniteBinaryImageFibres

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {K V E : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private def surjectionSplit (f : V →ₗ[K] E) (hf : Function.Surjective f) :
    V ≃ₗ[K] (LinearMap.ker f × E) := by
  let r : E →ₗ[K] V := Classical.choose
    (f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf))
  have hr : f.comp r = LinearMap.id := Classical.choose_spec
    (f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf))
  refine
    { toFun := fun x => (⟨x - r (f x), ?_⟩, f x)
      invFun := fun p => p.1.1 + r p.2
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · change f (x - r (f x)) = 0
    have hrx : f (r (f x)) = f x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun q : E →ₗ[K] E => q (f x)) hr
    exact sub_eq_zero.mpr hrx
  · intro x y
    apply Prod.ext
    · apply Subtype.ext
      simp [map_add, LinearMap.comp_apply, sub_add_sub_comm]
    · simp
  · intro a x
    apply Prod.ext
    · apply Subtype.ext
      simp [map_smul, LinearMap.comp_apply, smul_sub]
    · simp
  · intro x
    simp [LinearMap.comp_apply, hr]
  · rintro ⟨k, y⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [LinearMap.comp_apply, hr, k.property]
    · simp [LinearMap.comp_apply, hr]

/-- Any two surjective linear maps from the same finite-dimensional domain
onto the same finite-dimensional codomain differ by a domain automorphism. -/
theorem exists_domain_equiv_of_surjective
    (f g : V →ₗ[K] E) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ U : V ≃ₗ[K] V, g.comp U.toLinearMap = f := by
  let ef := surjectionSplit f hf
  let eg := surjectionSplit g hg
  have hdim : Module.finrank K (LinearMap.ker f) = Module.finrank K (LinearMap.ker g) := by
    have hf' : Module.finrank K (LinearMap.ker f) + Module.finrank K E =
        Module.finrank K V := by simpa using ef.finrank_eq.symm
    have hg' : Module.finrank K (LinearMap.ker g) + Module.finrank K E =
        Module.finrank K V := by simpa using eg.finrank_eq.symm
    omega
  let eK : LinearMap.ker f ≃ₗ[K] LinearMap.ker g :=
    LinearEquiv.ofFinrankEq _ _ hdim
  let U : V ≃ₗ[K] V := ef.trans ((LinearEquiv.prodCongr eK (LinearEquiv.refl K E)).trans eg.symm)
  refine ⟨U, ?_⟩
  ext x
  have hsecond : (eg (U x)).2 = (ef x).2 := by
    simp [U]
  simpa [surjectionSplit] using hsecond

end
end PvNP.RealizableHardness.ActualFiniteBinaryImageOrbit
