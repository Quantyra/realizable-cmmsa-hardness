import PvNP.RealizableHardness.ActualModifiedPcpCeiling

/-!
Checks for the modified-PCP ceiling identity.
The concrete power is the shipped identity at `m = 3`, `q = 5`, not a
recomputed exponent. Axioms print after the checks. This file does not
inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpCeilingChecks

open ActualModifiedPcpCeiling
open ActualCmmsaParameterReconciliation
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters

#check sub_one_mul_add_one
#check pow_gap_identity
#check modifiedPcpDenom_eq_gapRoot_pow
#check modifiedPcp_exponent_eq
#check modifiedPcpDenom_rblock_pow
#check modified_pcp_ceiling_meets_hn_endpoint
#check modified_pcp_ceiling_meets_hn_endpoint_real

example : 2 ^ (2 * 5 * (3 ^ 2 - 1)) = (2 ^ (2 * 5 * (3 - 1))) ^ (3 + 1) :=
  pow_gap_identity 3 5

example (L m : Nat) : modifiedPcpDenom L m = gapRoot L m ^ (m + 1) :=
  modifiedPcpDenom_eq_gapRoot_pow L m

example :
    ∃ L0, ∀ L, L0 ≤ L → ∀ zeta : Rat,
      zeta ≤ ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ →
      ((8 : Rat) * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) * zeta ≤
        (5 : Rat) / 8 :=
  modified_pcp_ceiling_meets_hn_endpoint

#print axioms pow_gap_identity
#print axioms modifiedPcpDenom_eq_gapRoot_pow
#print axioms modifiedPcp_exponent_eq
#print axioms modified_pcp_ceiling_meets_hn_endpoint
#print axioms modified_pcp_ceiling_meets_hn_endpoint_real

end PvNP.RealizableHardness.ActualModifiedPcpCeilingChecks
