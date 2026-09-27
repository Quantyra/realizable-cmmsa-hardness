import PvNP.RealizableHardness.ActualDinurArityGap

/-!
Checks for the Dinur repetition / manuscript HN split. Does not assemble
Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualDinurArityGapChecks

open ActualDinurArityGap
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters

#check half_base_repetition_misses_hn
#check fixed_arity_base_meets_hn

example :
    ∃ L0, ∀ L, L0 ≤ L → ∀ t : ℕ,
      ¬ ((8 * (manuscriptSigma L : Rat)) ^ (t + 1) * ((1 : Rat) / 2) ^ t ≤
          (5 : Rat) / 8) :=
  half_base_repetition_misses_hn ((1 : Rat) / 2) (by norm_num)

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ t : ℕ,
        (8 * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
            ((1 : Rat) / 2) ^ t ≤
          (5 : Rat) / 8 :=
  fixed_arity_base_meets_hn ((1 : Rat) / 2) (by norm_num) (by norm_num)

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ t : ℕ,
        (8 * (manuscriptSigma L : Rat)) ^ (certifiedM L + 1) *
            ((3 : Rat) / 4) ^ t ≤
          (5 : Rat) / 8 :=
  fixed_arity_base_meets_hn ((3 : Rat) / 4) (by norm_num) (by norm_num)

#print axioms half_base_repetition_misses_hn
#print axioms fixed_arity_base_meets_hn

end PvNP.RealizableHardness.ActualDinurArityGapChecks
