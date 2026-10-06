import PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneFixedBase

namespace PvNP.RealizableHardness.BinaryMatrixA15BaseCase

open BinaryMatrixFourier BinaryMatrixActualAffine BinaryMatrixComplexA15
open BinaryMatrixComplexA14
open BinaryMatrixLineA15 BinaryMatrixCodomainA15
open BinaryMatrixFirstDerivative
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Complex rank-level Bessel bound at the terminal carrier of A15. -/
theorem complexRankProjection_energy_le {n d j : ℕ}
    (f : BinaryMatrix n d → ℂ) :
    fibreEnergy Finset.univ (complexRankProjection j f) ≤
      fibreEnergy Finset.univ f := by
  have hr := rankProjection_energy_le (fun M => (f M).re) (i := j)
  have hi := rankProjection_energy_le (fun M => (f M).im) (i := j)
  simpa [fibreEnergy, Complex.normSq_apply, ← pow_two,
    complexRankProjection_re, complexRankProjection_im,
    Finset.sum_add_distrib, add_div, uniformMean] using add_le_add hr hi

theorem actualGlobal_zero_energy_le {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℂ)
    (hf : UpToActualNormSqGlobal r ε f) :
    fibreEnergy Finset.univ f ≤ ε := by
  let Q : ActualAffineRestriction n d :=
    { domainFixed := ⊥, codomainVariation := ⊤, base := 0 }
  have horder : Q.order ≤ r := by
    haveI : Subsingleton ((Fin n → ZMod 2) ⧸
        (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2))) := inferInstance
    simp [Q, ActualAffineRestriction.order, Module.finrank_zero_of_subsingleton]
  have hfibre : Q.fibre = Finset.univ := by
    ext M
    simp [Q, ActualAffineRestriction.fibre]
  simpa [hfibre] using hf Q horder

/-- The k=0 Parseval/Bessel endpoint, with no degree or dimension premise. -/
theorem A15_coordinate_order_zero {n d j r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℂ)
    (hf : UpToActualNormSqGlobal r ε f) :
    fibreEnergy Finset.univ (complexRankProjection j f) ≤ ε :=
  (complexRankProjection_energy_le f).trans (actualGlobal_zero_energy_le f hf)

/-- Exact one-step influence bound for a coordinate domain line. -/
theorem A15_coordinate_line_oneStep_influence {n d k : ℕ} {ε : ℝ}
    (t : Fin n → ZMod 2)
    (f : BinaryMatrix n (d + 1) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal (k + 1) ε f) :
    fibreEnergy Finset.univ
      (complexHybridLineDerivative t (complexRankProjection (k + 1) f)) ≤
        4 * (2 : ℝ) ^ (4 * (k + 1)) * ε := by
  have hw := actualGlobal_A15_complex_fixedLine t f hε hf
  have he := A15_coordinate_order_zero (j := k) (r := k)
    (fun M => complexLineP k f (rawLastColumn M t)) hw
  have heq : complexRankProjection k
      (fun M => complexLineP k f (rawLastColumn M t)) =
      complexHybridLineDerivative t (complexRankProjection (k + 1) f) := by
    funext M
    exact complex_A14_fixedLine t f M
  simpa only [heq] using he

/-- Exact one-step influence bound for a coordinate codomain hyperplane. -/
theorem A15_coordinate_hyperplane_oneStep_influence {n d k : ℕ} {ε : ℝ}
    (t : Fin d → ZMod 2)
    (f : BinaryMatrix (n + 1) d → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToActualNormSqGlobal (k + 1) ε f) :
    fibreEnergy Finset.univ
      (complexHyperplaneDerivative t (complexRankProjection (k + 1) f)) ≤
        4 * (2 : ℝ) ^ (4 * (k + 1)) * ε := by
  have hw := actualGlobal_A15_complex_fixedHyperplane t f hε hf
  have he := A15_coordinate_order_zero (j := k) (r := k)
    (fun M => complexHyperplaneP k f (rawLastRow M t)) hw
  have heq : complexRankProjection k
      (fun M => complexHyperplaneP k f (rawLastRow M t)) =
      complexHyperplaneDerivative t (complexRankProjection (k + 1) f) := by
    funext M
    exact complex_A14_fixedHyperplane t f M
  simpa only [heq] using he

end
end PvNP.RealizableHardness.BinaryMatrixA15BaseCase
