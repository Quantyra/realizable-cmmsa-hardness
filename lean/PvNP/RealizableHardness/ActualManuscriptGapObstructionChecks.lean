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

example (c : Rat) (hc : 0 < c) :
    ∃ L0, ∀ L, L0 ≤ L →
      ¬ ((8 : Rat) * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1) * c
        ≤ (5 : Rat) / 8 :=
  constant_csp_ceiling_misses_manuscript_hn c hc

example (L : Nat) (zeta : Rat)
    (hbase : 0 < (8 : Rat) * (manuscriptSigma L : Rat))
    (hz : zeta ≤ (5 : Rat) / 8 /
        (((8 : Rat) * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1))) :
    ((8 : Rat) * (manuscriptSigma L : Rat)) ^
        (ActualCertifiedManuscriptParameters.certifiedM L + 1) * zeta
      ≤ (5 : Rat) / 8 :=
  manuscript_hn_zeta_ceiling_meets_endpoint L zeta hbase hz

example (c : Rat) (hc : 0 < c) :
    ∃ L0, ∀ L, L0 ≤ L →
      (5 : Rat) / 8 /
        (((8 : Rat) * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1))
        < c :=
  manuscript_hn_zeta_ceiling_lt_constant c hc

example :
    ∃ L0, ∀ L, L0 ≤ L → ∀ zeta : Rat,
      zeta ≤
        ((ActualCmmsaParameterReconciliation.gapRoot L
            (ActualCertifiedManuscriptParameters.certifiedM L) : Rat) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1))⁻¹ →
      ((8 : Rat) * (manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1) * zeta
        ≤ (5 : Rat) / 8 :=
  manuscript_gapRoot_zeta_meets_hn_endpoint

#print axioms constant_csp_ceiling_misses_manuscript_hn
#print axioms manuscript_hn_zeta_ceiling_meets_endpoint
#print axioms manuscript_hn_zeta_ceiling_lt_constant
#print axioms manuscript_gapRoot_zeta_meets_hn_endpoint

end PvNP.RealizableHardness.ActualManuscriptGapObstructionChecks
