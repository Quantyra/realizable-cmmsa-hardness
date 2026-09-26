import PvNP.RealizableHardness.ActualManuscriptGapObstruction

namespace PvNP.RealizableHardness.ActualManuscriptGapObstructionChecks

open ActualHeadlineParameters
open ActualManuscriptGapObstruction

example : ∃ L0, ∀ L, L0 ≤ L → gammaL L < 3 / 4 :=
  manuscript_gamma_eventually_lt_three_quarters

example : ∃ L0, ∀ L, L0 ≤ L → manuscriptGamma L < 3 / 4 :=
  manuscriptGamma_eventually_lt_three_quarters

example : ∃ L0, ∀ L, L0 ≤ L →
    (1 ≤ rofSigma L → 2 ≤ rofSigma L) ∧ gammaL L < 3 / 4 :=
  manuscript_large_gap_parameters

end PvNP.RealizableHardness.ActualManuscriptGapObstructionChecks
