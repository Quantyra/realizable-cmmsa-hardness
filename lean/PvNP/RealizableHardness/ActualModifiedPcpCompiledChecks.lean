import PvNP.RealizableHardness.ActualModifiedPcpCompiled
import PvNP.RealizableHardness.ActualModifiedPcpEdge
import PvNP.RealizableHardness.ActualModifiedPcpCeilingChecks

/-!
Checks for the modified-PCP compiler glue and the edge-test ceiling.
The examples call the shipped theorems. Axioms print after. This file
does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpCompiledChecks

open ActualModifiedPcpCompiled
open ActualModifiedPcpEdge
open ActualModifiedPcpCeiling
open ActualDinurShrinkingCeiling
open ActualCertifiedManuscriptParameters
open Complexity.SAT

#check q_pos_of_certifiedM
#check uniform_compiled_product_of_modified_pcp
#check modified_pcp_compiler_hypotheses_large
#check every_unsat_threeCnf_modified_pcp_score

example (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (manuscriptGap φ).Assignment) :
    gapRootZeta φ L a ≤ ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ :=
  every_unsat_threeCnf_modified_pcp_score φ h3 hunsat L a

example :
    ∃ L0, ∀ L, L0 ≤ L →
      256 ≤ certifiedM L ∧
      1 ≤ ActualHeadlineParameters.manuscriptSigma L ∧
      ((8 : ℝ) * (ActualHeadlineParameters.manuscriptSigma L : ℝ)) ^
          (certifiedM L + 1) *
        ((modifiedPcpDenom L (certifiedM L) : ℝ))⁻¹ ≤ (5 : ℝ) / 8 :=
  modified_pcp_compiler_hypotheses_large

#print axioms uniform_compiled_product_of_modified_pcp
#print axioms modified_pcp_compiler_hypotheses_large
#print axioms every_unsat_threeCnf_modified_pcp_score

end PvNP.RealizableHardness.ActualModifiedPcpCompiledChecks
