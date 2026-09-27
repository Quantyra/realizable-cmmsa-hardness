import PvNP.RealizableHardness.ActualCompiledProduct
import PvNP.RealizableHardness.ActualModifiedPcpCeiling

/-!
An arity-`certifiedM` star family whose labeling score is at most the
modified-PCP reciprocal falls under `certifiedGamma` after the shipped
compiler.

The family, its compile proof, and its score bound are arguments. This
file does not read a 3CNF, does not build the family, does not build a
`SeededMap`, and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpCompiled

set_option autoImplicit false
set_option maxHeartbeats 400000

open ActualCompiledProduct
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open ActualCmmsaAdmissibilitySelector
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open ActualFormulaProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem q_pos_of_certifiedM {L : Nat} (hm : 256 ≤ certifiedM L) :
    0 < q (certifiedM L) := by
  have hsq : 16 * 16 ≤ certifiedM L := by simpa using hm
  have h16 : 16 ≤ Nat.sqrt (certifiedM L) := Nat.le_sqrt.mpr hsq
  exact lt_of_lt_of_le (by decide : 0 < 16) h16

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
  {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]

theorem uniform_compiled_product_of_modified_pcp
    {L : Nat}
    (hm : 256 ≤ certifiedM L)
    (hsig : 1 ≤ manuscriptSigma L)
    (hhn : ((8 : ℝ) * (manuscriptSigma L : ℝ)) ^ (certifiedM L + 1) *
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ ≤ (5 : ℝ) / 8)
    (edges : E → Star V Sigma (certifiedM L))
    (hcompile : ∀ e, (compile (edges e)).isSome = true)
    (hvalue : ∀ l : Labeling Sigma,
      score uniformEdge edges l ≤ ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹)
    (Z : (Σ v, Sigma v) → Bool)
    (hcost : assignmentCost uniformEdge edges Z ≤
      (manuscriptSigma L : ℝ) * starBudget uniformEdge edges) :
    average (fun ι : Fin (q (certifiedM L)) → E =>
        Formula.eval Z
          (andAll (fun j => compiledFormula edges hcompile (ι j))
            (q_pos_of_certifiedM hm))) <
      certifiedGamma L := by
  have hrho : (0 : ℝ) < (manuscriptSigma L : ℝ) := by
    exact_mod_cast hsig
  exact uniform_compiled_product_lt_certifiedGamma (m := certifiedM L) edges hcompile
    (manuscriptSigma L : ℝ) ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹
    hrho hvalue hhn (q_pos_of_certifiedM hm) Z hcost

/-- For every large `L` the numeric hypotheses of the compiler glue hold. -/
theorem modified_pcp_compiler_hypotheses_large :
    ∃ L0, ∀ L, L0 ≤ L →
      256 ≤ certifiedM L ∧
      1 ≤ manuscriptSigma L ∧
      ((8 : ℝ) * (manuscriptSigma L : ℝ)) ^ (certifiedM L + 1) *
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ ≤ (5 : ℝ) / 8 := by
  obtain ⟨Lhn, hhn⟩ := modified_pcp_ceiling_meets_hn_endpoint_real
  obtain ⟨Lp, hp⟩ := certified_parameters_eventually 256
  refine ⟨max Lhn Lp, ?_⟩
  intro L hL
  obtain ⟨m, _, hm256, hAd, hM, hσ⟩ := hp L (le_trans (Nat.le_max_right _ _) hL)
  have h8 : 8 ≤ sigmaBase L m := hAd.2.2.2.2.2.2.2.2
  have hσfin : 1 ≤ sigmaFinal L m := by
    have h4 : 2 ≤ sigmaBase L m / 4 := by
      have : 8 / 4 ≤ sigmaBase L m / 4 := Nat.div_le_div_right h8
      simpa using this
    have : 1 ≤ (sigmaBase L m / 4) / 2 := by
      have hone : 2 / 2 ≤ (sigmaBase L m / 4) / 2 := Nat.div_le_div_right h4
      simpa using hone
    simpa [sigmaFinal, sigmaRepair] using this
  refine ⟨?_, ?_, hhn L (le_trans (Nat.le_max_left _ _) hL)⟩
  · simpa [hM] using hm256
  · rw [show manuscriptSigma L = certifiedSigma L from rfl, hσ]
    exact hσfin

end

end PvNP.RealizableHardness.ActualModifiedPcpCompiled
