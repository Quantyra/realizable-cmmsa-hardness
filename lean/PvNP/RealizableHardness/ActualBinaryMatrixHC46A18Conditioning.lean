import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
Finite linear-functional disintegration used by the A18 conditional
restriction calculation.  This module isolates the exact uniform-extension
count: once a functional is fixed on a subspace, all of its extensions form
an affine copy of the kernel of restriction.  It does not assume any
globalness estimate or final A18 bound.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18Conditioning

noncomputable section

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V]

/-- Restriction of linear functionals from the ambient space to a subspace. -/
def dualRestriction (A : Submodule K V) :
    (V →ₗ[K] K) →ₗ[K] (A →ₗ[K] K) where
  toFun φ := φ.comp A.subtype
  map_add' φ ψ := by
    ext x
    rfl
  map_smul' c φ := by
    ext x
    rfl

@[simp] theorem dualRestriction_apply (A : Submodule K V)
    (φ : V →ₗ[K] K) (x : A) :
    dualRestriction A φ x = φ x := rfl

/-- Every extension of a fixed functional on A is in bijection with the
kernel of restriction, by subtracting one chosen extension.  In particular,
the number of extensions does not depend on the prescribed restriction. -/
def dualRestrictionFiberEquivKernel (A : Submodule K V)
    (ψ : A →ₗ[K] K) (φ₀ : V →ₗ[K] K)
    (hφ₀ : dualRestriction A φ₀ = ψ) :
    {φ : V →ₗ[K] K // dualRestriction A φ = ψ} ≃
      {δ : V →ₗ[K] K // dualRestriction A δ = 0} where
  toFun φ := ⟨φ.1 - φ₀, by
    change dualRestriction A (φ.1 - φ₀) = 0
    rw [map_sub, φ.2, hφ₀, sub_self]⟩
  invFun δ := ⟨δ.1 + φ₀, by
    change dualRestriction A (δ.1 + φ₀) = ψ
    rw [map_add, δ.2, hφ₀, zero_add]⟩
  left_inv φ := by
    apply Subtype.ext
    exact sub_add_cancel _ _
  right_inv δ := by
    apply Subtype.ext
    exact add_sub_cancel_right _ _

/-- The fibre cardinality of dual restriction is constant on every attainable
target.  This is the finite counting statement needed to keep the ambient
functional coordinates outside A independent after conditioning on φ|A. -/
theorem dualRestrictionFiber_card_eq_kernel [Fintype K] [Fintype V]
    (A : Submodule K V)
    (ψ : A →ₗ[K] K) (φ₀ : V →ₗ[K] K)
    (hφ₀ : dualRestriction A φ₀ = ψ) :
    Fintype.card {φ : V →ₗ[K] K // dualRestriction A φ = ψ} =
      Fintype.card {δ : V →ₗ[K] K // dualRestriction A δ = 0} :=
  Fintype.card_congr (dualRestrictionFiberEquivKernel A ψ φ₀ hφ₀)

/-- A prescribed value on a vector in A is already determined by the
restriction fibre; no extra ambient functional condition is introduced. -/
theorem dualRestriction_preserves_value {A : Submodule K V}
    (ψ : A →ₗ[K] K) (φ : V →ₗ[K] K)
    (hφ : dualRestriction A φ = ψ) {v : V} (hv : v ∈ A) :
    φ v = ψ ⟨v, hv⟩ := by
  have h := congrArg (fun g : A →ₗ[K] K => g ⟨v, hv⟩) hφ
  simpa [dualRestriction] using h

/-- Restriction together with the value on one new vector. -/
def dualRestrictionAt (A : Submodule K V) (w : V) :
    (V →ₗ[K] K) →ₗ[K] ((A →ₗ[K] K) × K) where
  toFun φ := (dualRestriction A φ, φ w)
  map_add' φ ψ := by
    ext <;> simp
  map_smul' c φ := by
    ext <;> simp

@[simp] theorem dualRestrictionAt_apply (A : Submodule K V) (w : V)
    (φ : V →ₗ[K] K) :
    dualRestrictionAt A w φ = (dualRestriction A φ, φ w) := rfl

/-- A fibre of restriction-plus-one-coordinate is an affine translate of its
kernel. -/
def dualRestrictionAtFiberEquivKernel (A : Submodule K V) (w : V)
    (z : (A →ₗ[K] K) × K) (φ₀ : V →ₗ[K] K)
    (hφ₀ : dualRestrictionAt A w φ₀ = z) :
    {φ : V →ₗ[K] K // dualRestrictionAt A w φ = z} ≃
      {δ : V →ₗ[K] K // dualRestrictionAt A w δ = 0} where
  toFun φ := ⟨φ.1 - φ₀, by
    change dualRestrictionAt A w (φ.1 - φ₀) = 0
    rw [map_sub, φ.2, hφ₀, sub_self]⟩
  invFun δ := ⟨δ.1 + φ₀, by
    change dualRestrictionAt A w (δ.1 + φ₀) = z
    rw [map_add, δ.2, hφ₀, zero_add]⟩
  left_inv φ := by
    apply Subtype.ext
    exact sub_add_cancel _ _
  right_inv δ := by
    apply Subtype.ext
    exact add_sub_cancel_right _ _

/-- All attainable pairs (restriction to A, value at w) have equally sized
fibres. -/
theorem dualRestrictionAtFiber_card_eq_kernel [Fintype K] [Fintype V]
    (A : Submodule K V) (w : V)
    (z : (A →ₗ[K] K) × K) (φ₀ : V →ₗ[K] K)
    (hφ₀ : dualRestrictionAt A w φ₀ = z) :
    Fintype.card {φ : V →ₗ[K] K // dualRestrictionAt A w φ = z} =
      Fintype.card {δ : V →ₗ[K] K // dualRestrictionAt A w δ = 0} :=
  Fintype.card_congr (dualRestrictionAtFiberEquivKernel A w z φ₀ hφ₀)

/-- When w is outside A, every prescribed restriction and value at w is
attainable. This is the columnwise extension step used in the conditional
pushforward count. -/
theorem dualRestrictionAt_surjective_of_notMem (A : Submodule K V)
    {w : V} (hw : w ∉ A) (ψ : A →ₗ[K] K) (y : K) :
    ∃ φ : V →ₗ[K] K, dualRestrictionAt A w φ = (ψ, y) := by
  obtain ⟨φ, hψ, hy⟩ := LinearMap.exists_extend_of_notMem ψ hw y
  refine ⟨φ, ?_⟩
  ext
  · exact hψ
  · exact hy

/-- The conditional pushforward on the new column is uniform: for fixed
restriction ψ, the number of ambient functionals taking any prescribed value
at w is independent of that value. -/
theorem dualRestrictionAtFiber_card_eq_of_notMem [Fintype K] [Fintype V]
    (A : Submodule K V) {w : V} (hw : w ∉ A) (ψ : A →ₗ[K] K)
    (y₁ y₂ : K) :
    Fintype.card {φ : V →ₗ[K] K // dualRestrictionAt A w φ = (ψ, y₁)} =
      Fintype.card {φ : V →ₗ[K] K // dualRestrictionAt A w φ = (ψ, y₂)} := by
  obtain ⟨φ₁, hφ₁⟩ := dualRestrictionAt_surjective_of_notMem A hw ψ y₁
  obtain ⟨φ₂, hφ₂⟩ := dualRestrictionAt_surjective_of_notMem A hw ψ y₂
  rw [dualRestrictionAtFiber_card_eq_kernel A w (ψ, y₁) φ₁ hφ₁,
      dualRestrictionAtFiber_card_eq_kernel A w (ψ, y₂) φ₂ hφ₂]

/-- If the queried vector already lies in A, its value is fixed by the
restriction. This is the zero-new-coordinate/unavailable-branch companion to
the uniform outside-A pushforward theorem. -/
theorem dualRestrictionAt_impossible_of_mem (A : Submodule K V)
    {w : V} (hw : w ∈ A) (ψ : A →ₗ[K] K) (y : K)
    (hy : y ≠ ψ ⟨w, hw⟩) :
    ¬ ∃ φ : V →ₗ[K] K, dualRestrictionAt A w φ = (ψ, y) := by
  rintro ⟨φ, hφ⟩
  have hres : dualRestriction A φ = ψ := congrArg Prod.fst hφ
  have hvalue : φ w = y := congrArg Prod.snd hφ
  exact hy ((dualRestriction_preserves_value ψ φ hres hw).symm.trans hvalue)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18Conditioning
