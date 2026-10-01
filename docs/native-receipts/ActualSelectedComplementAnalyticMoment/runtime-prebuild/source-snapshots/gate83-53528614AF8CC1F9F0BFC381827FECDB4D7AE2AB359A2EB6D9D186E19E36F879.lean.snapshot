import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18SourceConditioning
import PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel
import PvNP.RealizableHardness.BinaryMatrixActualAffine
import PvNP.RealizableHardness.BinaryMatrixComplexA15
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
The source-defined expanded A18 branch on the actual affine matrix fibre.
The restricted-functional outside-column event is measured using the actual
quotient-Hom representation of the affine fibre. The order drop is derived
from the kernel of the restricted functional and the one-dimensional
codomain extension; no conditional-energy or event-density premise is
introduced.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18SourceGlobal

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18Conditioning
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18QuotientSamplingLaw
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18SourceConditioning
open PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel
open BinaryMatrixActualAffine BinaryMatrixComplexA15
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The actual restricted-functional kernel loses one dimension. -/
theorem restrictedFunctionalKernel_finrank_drop
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [Module.Finite (ZMod 2) X]
    (A : Submodule (ZMod 2) X) (phi : A →ₗ[ZMod 2] ZMod 2)
    (v : A) (hv : phi v = 1) :
    Module.finrank (ZMod 2) (functionalKernelInAmbient A phi) + 1 =
      Module.finrank (ZMod 2) A := by
  have hsurj : Function.Surjective phi := by
    intro y
    refine ⟨y • v, ?_⟩
    simp [map_smul, hv]
  have hrange : LinearMap.range phi = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker phi
  rw [hrange] at hrank
  have hker : Module.finrank (ZMod 2) (LinearMap.ker phi) + 1 =
      Module.finrank (ZMod 2) A := by
    simpa [Nat.add_comm] using hrank
  change Module.finrank (ZMod 2) ((LinearMap.ker phi).map A.subtype) + 1 = _
  rw [Submodule.finrank_map_subtype_eq]
  exact hker

/-- Enlarging the binary codomain by one dimension lowers its quotient
codimension by one. -/
theorem codimension_drop_of_one_dim_extension
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    (B B' : Submodule (ZMod 2) W)
    (hdim : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B + 1) :
    Module.finrank (ZMod 2) (W ⧸ B') + 1 =
      Module.finrank (ZMod 2) (W ⧸ B) := by
  have hB := B.finrank_quotient_add_finrank
  have hB' := B'.finrank_quotient_add_finrank
  omega

/-- On the actual affine fibre with the functional-kernel domain and
one-dimensional expanded codomain, the source globalness hypothesis at
order `s+1` gives a conditional outside-column energy bound `2η`. The
statistic is the actual squared output of the matrix in the affine fibre,
transported through the accepted quotient-Hom equivalence. -/
theorem actual_expanded_outside_column_energy_le_two
    {n d s : ℕ} {η : ℝ}
    (f : BinaryMatrix n d → ℂ)
    (hf : UpToActualNormSqGlobal (s + 1) η f)
    (Q : ActualAffineRestriction n d)
    (hQ : Q.order ≤ s + 1)
    (phi : Q.domainFixed →ₗ[ZMod 2] ZMod 2)
    (v : Q.domainFixed) (hv : phi v = 1)
    (B' : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hB : Q.codomainVariation ≤ B')
    (hdim : Module.finrank (ZMod 2) B' =
      Module.finrank (ZMod 2) Q.codomainVariation + 1) :
    (∑ N ∈ (Finset.univ : Finset
      ((Fin d → ZMod 2) ⧸ functionalKernelInAmbient Q.domainFixed phi →ₗ[ZMod 2] B')).filter
        (fun N =>
          (N (Submodule.mkQ (functionalKernelInAmbient Q.domainFixed phi) (v : Fin d → ZMod 2)) :
            Fin n → ZMod 2) ∉ Q.codomainVariation),
        Complex.normSq (f ((actualFibreQuotientHomEquiv
          ({ domainFixed := functionalKernelInAmbient Q.domainFixed phi
             codomainVariation := B'
             base := Q.base })).symm N))) /
      ((Finset.univ : Finset
        ((Fin d → ZMod 2) ⧸ functionalKernelInAmbient Q.domainFixed phi →ₗ[ZMod 2] B')).filter
          (fun N =>
            (N (Submodule.mkQ (functionalKernelInAmbient Q.domainFixed phi) (v : Fin d → ZMod 2)) :
              Fin n → ZMod 2) ∉ Q.codomainVariation)).card
      ≤ 2 * η := by
  classical
  let A' := functionalKernelInAmbient Q.domainFixed phi
  let Q' : ActualAffineRestriction n d :=
    { domainFixed := A', codomainVariation := B', base := Q.base }
  have hAdim : Module.finrank (ZMod 2) A' + 1 =
      Module.finrank (ZMod 2) Q.domainFixed := by
    simpa [A'] using restrictedFunctionalKernel_finrank_drop
      Q.domainFixed phi v hv
  have hBcodim : Module.finrank (ZMod 2)
      ((Fin n → ZMod 2) ⧸ B') + 1 =
      Module.finrank (ZMod 2)
        ((Fin n → ZMod 2) ⧸ Q.codomainVariation) :=
    codimension_drop_of_one_dim_extension Q.codomainVariation B' hdim
  have hQorder :
      Module.finrank (ZMod 2) Q.domainFixed +
        Module.finrank (ZMod 2)
          ((Fin n → ZMod 2) ⧸ Q.codomainVariation) ≤ s + 1 := by
    simpa [ActualAffineRestriction.order] using hQ
  have horderdrop : Q'.order + 2 = Q.order := by
    dsimp [Q', A', ActualAffineRestriction.order]
    omega
  have hsmall : Q'.order ≤ s - 1 := by
    dsimp [Q', A', ActualAffineRestriction.order] at horderdrop ⊢
    omega
  let e := actualFibreQuotientHomEquiv Q'
  let g : (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B') → ℝ :=
    fun N => Complex.normSq (f (e.symm N))
  have hg : ∀ N, 0 ≤ g N := fun N => Complex.normSq_nonneg _
  have hconditional := restrictedFunctional_outsideColumn_mean_le_two
    Q.domainFixed phi v hv Q.codomainVariation B' hB hdim g hg
  have hglobalSmall : fibreEnergy Q'.fibre f ≤ η := hf Q' (by omega)
  have henergy :
      (∑ N : ((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B', g N) /
        (Fintype.card (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B') : ℝ) ≤ η := by
    rw [← actualFibreQuotientHomEquiv_energy Q' f]
    exact hglobalSmall
  have hconditional' :
      (∑ N ∈ (Finset.univ : Finset
        (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B')).filter
          (fun N => (N (Submodule.mkQ A' (v : Fin d → ZMod 2)) :
            Fin n → ZMod 2) ∉ Q.codomainVariation), g N) /
        ((Finset.univ : Finset
          (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B')).filter
            (fun N => (N (Submodule.mkQ A' (v : Fin d → ZMod 2)) :
              Fin n → ZMod 2) ∉ Q.codomainVariation)).card ≤
      2 * ((∑ N : ((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B', g N) /
        (Fintype.card (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B') : ℝ)) := by
    simpa [A', g, e] using hconditional
  calc
    _ = (∑ N ∈ (Finset.univ : Finset
        (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B')).filter
          (fun N => (N (Submodule.mkQ A' (v : Fin d → ZMod 2)) :
            Fin n → ZMod 2) ∉ Q.codomainVariation), g N) /
        ((Finset.univ : Finset
          (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B')).filter
            (fun N => (N (Submodule.mkQ A' (v : Fin d → ZMod 2)) :
              Fin n → ZMod 2) ∉ Q.codomainVariation)).card := by
          rfl
    _ ≤ 2 * ((∑ N : ((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B', g N) /
          (Fintype.card (((Fin d → ZMod 2) ⧸ A') →ₗ[ZMod 2] B') : ℝ)) :=
      hconditional'
    _ ≤ 2 * η :=
      mul_le_mul_of_nonneg_left henergy (by norm_num)

end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18SourceGlobal
