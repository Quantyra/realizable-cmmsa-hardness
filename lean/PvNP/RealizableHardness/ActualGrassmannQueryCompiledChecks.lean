import PvNP.RealizableHardness.ActualGrassmannQueryCompiled

/-!
Checks for the Grassmann query compiler glue. The examples call the
shipped theorems. Axioms print after. This file does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannQueryCompiledChecks

open ActualGrassmannQueryCompiled
open ActualModifiedPcpCompiled
open ActualModifiedPcpCeiling
open ActualCompiledProduct
open ActualFormulaProduct
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics

#check rBlock_inv_pow_le_modified_pcp_real
#check uniform_compiled_product_of_rBlock_query
#check rBlock_query_product_lt_gamma_large

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ((RBlock L (certifiedM L) : ℝ) ^ (certifiedM L))⁻¹ ≤
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ :=
  rBlock_inv_pow_le_modified_pcp_real

set_option maxHeartbeats 800000 in
example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hm : 256 ≤ certifiedM L),
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
  obtain ⟨L0, hL0⟩ := rBlock_query_product_lt_gamma_large
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨hm, _, _, _, hprod⟩ := hL0 L hL
  exact ⟨hm, hprod⟩

#print axioms uniform_compiled_product_of_rBlock_query
#print axioms rBlock_inv_pow_le_modified_pcp_real
#print axioms rBlock_query_product_lt_gamma_large

end PvNP.RealizableHardness.ActualGrassmannQueryCompiledChecks
