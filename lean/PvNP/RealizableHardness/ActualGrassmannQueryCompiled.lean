import PvNP.RealizableHardness.ActualGrassmannQueryBound
import PvNP.RealizableHardness.ActualModifiedPcpCompiled

/-!
A star family whose score is at most `RBlock^{-certifiedM}` falls under
`certifiedGamma` after the shipped compiler.

`rBlock_inv_pow_le_modified_pcp` puts that score under the modified-PCP
reciprocal, so `uniform_compiled_product_of_modified_pcp` applies.
The family, its compile proof, and its score bound are arguments.
This file does not read a 3CNF, does not build a `SeededMap`, and does
not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannQueryCompiled

open ActualGrassmannQueryBound
open ActualModifiedPcpCompiled
open ActualModifiedPcpCeiling
open ActualCompiledProduct
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open ActualFormulaProduct
open scoped BigOperators

set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
  {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]

theorem rBlock_inv_pow_le_modified_pcp_real :
    ∃ L0, ∀ L, L0 ≤ L →
      ((RBlock L (certifiedM L) : ℝ) ^ (certifiedM L))⁻¹ ≤
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ := by
  obtain ⟨L0, hL0⟩ := rBlock_pow_eq_modifiedPcpDenom_mul
  refine ⟨L0, ?_⟩
  intro L hL
  have heq := hL0 L hL
  have hcast :
      (RBlock L (certifiedM L) : ℝ) ^ (certifiedM L) =
        (modifiedPcpDenom L (certifiedM L) : ℝ) *
          (2 : ℝ) ^ (2 * (hBlock L (certifiedM L) / certifiedM L)) := by
    exact_mod_cast heq
  have hposD : (0 : ℝ) < (modifiedPcpDenom L (certifiedM L) : ℝ) := by
    exact_mod_cast
      (Nat.lt_of_lt_of_le (by decide : 0 < 1)
        (one_le_modifiedPcpDenom L (certifiedM L)) :
          0 < modifiedPcpDenom L (certifiedM L))
  have hposR : (0 : ℝ) < (RBlock L (certifiedM L) : ℝ) ^ (certifiedM L) := by
    exact pow_pos (by exact_mod_cast (Nat.two_pow_pos (2 * hBlock L (certifiedM L)) :
      0 < RBlock L (certifiedM L))) _
  have hge : (modifiedPcpDenom L (certifiedM L) : ℝ) ≤
      (RBlock L (certifiedM L) : ℝ) ^ (certifiedM L) := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * (hBlock L (certifiedM L) / certifiedM L)) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hmul := mul_le_mul_of_nonneg_left hone hposD.le
    --  denom * 1 ≤ denom * 2^k
    simpa [one_mul, hcast] using hmul
  exact (inv_le_inv₀ hposR hposD).mpr hge

theorem uniform_compiled_product_of_rBlock_query
    {L : Nat}
    (hm : 256 ≤ certifiedM L)
    (hsig : 1 ≤ manuscriptSigma L)
    (hhn : ((8 : ℝ) * (manuscriptSigma L : ℝ)) ^ (certifiedM L + 1) *
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ ≤ (5 : ℝ) / 8)
    (hinv : ((RBlock L (certifiedM L) : ℝ) ^ (certifiedM L))⁻¹ ≤
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹)
    (edges : E → Star V Sigma (certifiedM L))
    (hcompile : ∀ e, (compile (edges e)).isSome = true)
    (hvalue : ∀ l : Labeling Sigma,
      score uniformEdge edges l ≤
        ((RBlock L (certifiedM L) : ℝ) ^ (certifiedM L))⁻¹)
    (Z : (Σ v, Sigma v) → Bool)
    (hcost : assignmentCost uniformEdge edges Z ≤
      (manuscriptSigma L : ℝ) * starBudget uniformEdge edges) :
    average (fun ι : Fin (q (certifiedM L)) → E =>
        Formula.eval Z
          (andAll (fun j => compiledFormula edges hcompile (ι j))
            (q_pos_of_certifiedM hm))) <
      certifiedGamma L := by
  apply uniform_compiled_product_of_modified_pcp hm hsig hhn edges hcompile
  · intro l
    exact (hvalue l).trans hinv
  · exact hcost

/-- For every large `L`, a family with score at most `RBlock^{-certifiedM}`
has q-fold satisfaction below `certifiedGamma` inside the manuscript ball. -/
theorem rBlock_query_product_lt_gamma_large :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hm : 256 ≤ certifiedM L) (hsig : 1 ≤ manuscriptSigma L)
        (hhn : ((8 : ℝ) * (manuscriptSigma L : ℝ)) ^ (certifiedM L + 1) *
            ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ ≤ (5 : ℝ) / 8)
        (hinv : ((RBlock L (certifiedM L) : ℝ) ^ (certifiedM L))⁻¹ ≤
            ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹),
        ∀ {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
          {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]
          (edges : E → Star V Sigma (certifiedM L))
          (hcompile : ∀ e, (compile (edges e)).isSome = true)
          (hvalue : ∀ l : Labeling Sigma,
            score uniformEdge edges l ≤
              ((RBlock L (certifiedM L) : ℝ) ^ (certifiedM L))⁻¹)
          (Z : (Σ v, Sigma v) → Bool)
          (hcost : assignmentCost uniformEdge edges Z ≤
            (manuscriptSigma L : ℝ) * starBudget uniformEdge edges),
          average (fun ι : Fin (q (certifiedM L)) → E =>
              Formula.eval Z
                (andAll (fun j => compiledFormula edges hcompile (ι j))
                  (q_pos_of_certifiedM hm))) <
            certifiedGamma L := by
  obtain ⟨Lhyp, hhyp⟩ := modified_pcp_compiler_hypotheses_large
  obtain ⟨Linv, hinv⟩ := rBlock_inv_pow_le_modified_pcp_real
  refine ⟨max Lhyp Linv, ?_⟩
  intro L hL
  have hLhyp := hhyp L (le_trans (Nat.le_max_left _ _) hL)
  refine ⟨hLhyp.1, hLhyp.2.1, hLhyp.2.2, hinv L (le_trans (Nat.le_max_right _ _) hL), ?_⟩
  intro V E _ _ _ Sigma _ _ edges hcompile hvalue Z hcost
  exact uniform_compiled_product_of_rBlock_query (V := V) (E := E) (Sigma := Sigma)
    hLhyp.1 hLhyp.2.1 hLhyp.2.2
    (hinv L (le_trans (Nat.le_max_right _ _) hL))
    edges hcompile hvalue Z hcost

end

end PvNP.RealizableHardness.ActualGrassmannQueryCompiled
