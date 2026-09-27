import PvNP.RealizableHardness.ActualDinurShrinkingCeiling

namespace PvNP.RealizableHardness.ActualDinurShrinkingCeilingChecks

open ActualDinurShrinkingCeiling
open Complexity
open Complexity.SAT
open Dinur

#check every_unsat_threeCnf_powered_ceiling
#check manuscript_block_ceiling_shrinks
#check every_unsat_threeCnf_meets_manuscript_hn
#check every_unsat_threeCnf_manuscript_zeta_large

example (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) :
    ∃ L0, ∀ L, L0 ≤ L → ∀ a : (manuscriptGap φ).Assignment,
      ((8 : Rat) * (ActualHeadlineParameters.manuscriptSigma L : Rat)) ^
          (ActualCertifiedManuscriptParameters.certifiedM L + 1) *
        manuscriptZeta φ L a ≤ (5 : Rat) / 8 :=
  every_unsat_threeCnf_manuscript_zeta_large φ h3 hunsat

example (F : FinBase) (hd : 1 < F.deg)
    (φ : CNF) (h3 : φ.Is3CNF) (hunsat : ¬ φ.Satisfiable) (L : Nat)
    (a : (gapAllG F hd (fun _ => List.replicate (3 * φ.length) true)
        (Φ := fun _ => φ) ([] : List Bool)).Assignment) :
    ((8 : Rat) * (ActualHeadlineParameters.manuscriptSigma L : Rat)) ^
        (ActualCertifiedManuscriptParameters.certifiedM L + 1) *
      independentEdgeDecoder _ (manuscriptReps F hd L) a
      ≤ (5 : Rat) / 8 :=
  every_unsat_threeCnf_meets_manuscript_hn F hd φ h3 hunsat L a

#print axioms every_unsat_threeCnf_powered_ceiling
#print axioms manuscript_block_ceiling_shrinks
#print axioms manuscriptReps_spec
#print axioms every_unsat_threeCnf_meets_manuscript_hn
#print axioms every_unsat_threeCnf_manuscript_zeta
#print axioms every_unsat_threeCnf_manuscript_zeta_large

end PvNP.RealizableHardness.ActualDinurShrinkingCeilingChecks
