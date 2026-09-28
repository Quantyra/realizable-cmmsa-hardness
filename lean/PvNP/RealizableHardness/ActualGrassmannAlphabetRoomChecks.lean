import PvNP.RealizableHardness.ActualGrassmannAlphabetRoom

/-!
Checks for the Grassmann alphabet room. The example calls the shipped
theorem. Axioms print after. This file does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGrassmannAlphabetRoomChecks

open ActualGrassmannAlphabetRoom
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open ActualCertifiedManuscriptParameters

#check rBlock_clears_manuscriptSigma

example :
    ∃ L0, ∀ L, L0 ≤ L →
      manuscriptSigma L * 2 ^ 11 ≤ RBlock L (certifiedM L) ∧
      (manuscriptSigma L : Rat) / (RBlock L (certifiedM L) : Rat) < 1 :=
  rBlock_clears_manuscriptSigma

#print axioms rBlock_clears_manuscriptSigma

end PvNP.RealizableHardness.ActualGrassmannAlphabetRoomChecks
