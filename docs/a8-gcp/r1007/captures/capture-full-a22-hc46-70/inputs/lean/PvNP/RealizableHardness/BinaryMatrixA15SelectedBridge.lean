import PvNP.RealizableHardness.BinaryMatrixA15CanonicalLineRank
import PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneSelector
import PvNP.RealizableHardness.BinaryMatrixA1Complex
import PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBase
import PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneFixedBase

namespace PvNP.RealizableHardness.BinaryMatrixA15SelectedBridge

open BinaryMatrixNestedSelectorA1 BinaryMatrixTypedA14Line
open BinaryMatrixTypedA14Hyperplane BinaryMatrixTypedA15OneStep
open BinaryMatrixTypedHyperplaneSelector BinaryMatrixA1Complex
open BinaryMatrixA15CanonicalLineRank BinaryMatrixA15CanonicalRank
open BinaryMatrixA15NestedLine BinaryMatrixA15NestedHyperplane
open BinaryMatrixTypedA15ReducedGlobal BinaryMatrixTypedA15HyperplaneReducedGlobal
open BinaryMatrixTypedA14FixedBase BinaryMatrixTypedA14HyperplaneFixedBase
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

private theorem zmod_two_cases (z : F) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem typedLineSelected_iff_Selected {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    typedLineSelected B L hL Y ↔ Selected L ⊤ Y := by
  unfold typedLineSelected Selected
  constructor
  · intro hg
    constructor
    · intro x hx
      let y : L := ⟨x, hx⟩
      let e := lineScalarEquiv L hL
      rcases zmod_two_cases (e y) with h0 | h1
      · have hy : y = 0 := by
          apply e.injective
          simpa [h0]
        change (y : V d ⧸ A) ∈ LinearMap.range Y
        rw [hy]
        exact Submodule.zero_mem _
      · have hy : y = e.symm 1 := by
          apply e.injective
          simpa [h1]
        have hx' : x = (↑(e.symm 1) : V d ⧸ A) :=
          congrArg Subtype.val hy
        rw [hx']
        exact hg
    · intro w _
      trivial
  · rintro ⟨hLrange, _⟩
    exact hLrange ((lineScalarEquiv L hL).symm 1).property

theorem typedHyperplaneSelected_iff_Selected {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    typedHyperplaneSelected B H hH Y ↔ Selected ⊥ H Y := by
  rw [typedHyperplaneSelected_iff_ker_le]
  constructor
  · intro hk
    constructor
    · intro x hx
      rw [hx]
      exact Submodule.zero_mem _
    · intro w hw
      exact hk (by simpa using hw)
  · rintro ⟨_, h⟩ w hw
    exact h w (by simpa using hw)

theorem typedLineFilter_eq_carrierHybrid {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedComplexLineFilter B L hL f M =
      complexCarrierHybridFilter A B L ⊤ f M := by
  unfold typedComplexLineFilter complexCarrierHybridFilter
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [typedLineSelected_iff_Selected]

theorem typedHyperplaneFilter_eq_carrierHybrid {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedComplexHyperplaneFilter B H hH f M =
      complexCarrierHybridFilter A B ⊥ H f M := by
  unfold typedComplexHyperplaneFilter complexCarrierHybridFilter
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [typedHyperplaneSelected_iff_Selected]

theorem canonical_line_A14_selected {n d j : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (hL : Module.finrank F (A₁.map A₂.mkQ) = 1)
    (T : (V d ⧸ A₂) →ₗ[F] B)
    (f : ((V d ⧸ A₂) →ₗ[F] B) → ℂ)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    typedComplexRankProjection A₁ B j
        (fun X => typedLineReducedWitness (k := j) B
          (A₁.map A₂.mkQ) hL T f
          ((lineCanonicalEquiv A₂ A₁ B hA).symm X))
        (lineCanonicalEquiv A₂ A₁ B hA N) =
      complexCarrierHybridFilter A₂ B (A₁.map A₂.mkQ) ⊤
        (typedComplexRankProjection A₂ B (j + 1) f)
        (T + N.comp (A₁.map A₂.mkQ).mkQ) := by
  rw [lineCanonical_rankProjection A₂ A₁ B hA]
  rw [typed_A14_fixedLine A₂ B (A₁.map A₂.mkQ) hL T f N]
  exact typedLineFilter_eq_carrierHybrid A₂ B (A₁.map A₂.mkQ) hL _ _

theorem canonical_hyperplane_A14_selected {n d j : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (N : (V d ⧸ A) →ₗ[F] H) :
    typedComplexRankProjection A (hyperplaneCanonicalCodomain B H) j
        (fun X => typedHyperplaneReducedWitness (k := j) B H hH T f
          ((hyperplaneCanonicalEquiv B H).symm X))
        (hyperplaneCanonicalEquiv B H N) =
      complexCarrierHybridFilter A B ⊥ H
        (typedComplexRankProjection A B (j + 1) f)
        (T + H.subtype.comp N) := by
  rw [hyperplaneCanonical_rankProjection B H hH]
  rw [typed_A14_fixedHyperplane A B H hH T f N]
  exact typedHyperplaneFilter_eq_carrierHybrid A B H hH _ _

end
end PvNP.RealizableHardness.BinaryMatrixA15SelectedBridge
