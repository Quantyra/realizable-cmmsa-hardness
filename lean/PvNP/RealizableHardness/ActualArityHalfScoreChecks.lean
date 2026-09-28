import PvNP.RealizableHardness.ActualArityHalfScore

/-!
Checks for the arity-`certifiedM` half-base versus the modified-PCP
reciprocal. The examples call the shipped theorems on an arbitrary
expander family. Axioms print after. This file does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualArityHalfScoreChecks

open ActualArityHalfScore
open ActualModifiedPcpCeiling
open ActualCertifiedManuscriptParameters
open Complexity
open Dinur

#check half_pow_exceeds_modified_pcp
#check dinur_arity_pow_exceeds_modified_pcp

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ <
        ((1 : Rat) / 2) ^ (certifiedM L) :=
  half_pow_exceeds_modified_pcp

example (E : ExpanderFamily) :
    ∃ L0, ∀ L, L0 ≤ L →
      ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹ <
        (1 - (amplifier E).gap) ^ (certifiedM L) :=
  dinur_arity_pow_exceeds_modified_pcp E

#print axioms half_pow_exceeds_modified_pcp
#print axioms dinur_arity_pow_exceeds_modified_pcp

end PvNP.RealizableHardness.ActualArityHalfScoreChecks
