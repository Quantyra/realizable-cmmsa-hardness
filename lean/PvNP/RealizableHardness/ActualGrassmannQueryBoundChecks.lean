import PvNP.RealizableHardness.ActualGrassmannQueryBound

/-!
Checks for the Grassmann per-leaf reciprocal. The examples call the
shipped theorems. Axioms print after. This file does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannQueryBoundChecks

open ActualGrassmannQueryBound
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters

#check rBlock_pow_eq_modifiedPcpDenom_mul
#check rBlock_inv_pow_le_modified_pcp
#check rBlock_query_meets_hn_endpoint

example :
    ∃ L0, ∀ L, L0 ≤ L →
      RBlock L (certifiedM L) ^ (certifiedM L) =
        modifiedPcpDenom L (certifiedM L) *
          2 ^ (2 * (hBlock L (certifiedM L) / certifiedM L)) :=
  rBlock_pow_eq_modifiedPcpDenom_mul

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
        ((RBlock L (certifiedM L) : Rat) ^ (certifiedM L))⁻¹ ≤
          (5 : Rat) / 8 :=
  rBlock_query_meets_hn_endpoint

#print axioms rBlock_pow_eq_modifiedPcpDenom_mul
#print axioms rBlock_inv_pow_le_modified_pcp
#print axioms rBlock_query_meets_hn_endpoint

end PvNP.RealizableHardness.ActualGrassmannQueryBoundChecks
