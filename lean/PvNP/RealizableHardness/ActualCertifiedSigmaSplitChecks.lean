import PvNP.RealizableHardness.ActualCertifiedSigmaSplit

/-!
Checks call the shipped split. They do not rewrite `rofSigma` and do not
prove Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualCertifiedSigmaSplitChecks

open PvNP.RealizableHardness.ActualCertifiedSigmaSplit
open PvNP.RealizableHardness.ActualCertifiedManuscriptParameters

example : ActualHeadlineParameters.rofSigma (2 ^ 20) = 32768 :=
  rofSigma_two_pow_twenty

example : certifiedSigma (2 ^ 20) = 0 :=
  certifiedSigma_two_pow_twenty

example : ActualHeadlineParameters.rofSigma (2 ^ 20) ≠ certifiedSigma (2 ^ 20) :=
  rofSigma_ne_certifiedSigma

example : ∃ L0, ∀ L, L0 ≤ L → 2 ≤ certifiedSigma L ∧ certifiedGamma L < 3 / 4 :=
  certified_family_still_large_gap

end PvNP.RealizableHardness.ActualCertifiedSigmaSplitChecks
