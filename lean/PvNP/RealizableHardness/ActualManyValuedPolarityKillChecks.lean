import PvNP.RealizableHardness.ActualManyValuedPolarityKill

/-!
Check: for large `L`, the equal-weight polarity OR is not a manuscript
no-predicate.
-/
namespace PvNP.RealizableHardness.ActualManyValuedPolarityKillChecks

open ActualManyValuedPolarityKill
open ActualPolarityBudget
open ActualPositiveFormulaMono
open ActualHeadlineParameters

set_option autoImplicit false

example :
    ∃ L0, ∀ L, L0 ≤ L → ∀ gam : Rat, gam ≤ 1 →
      ¬ (∀ x : Fin 2 → Bool,
          weight w2 x ≤ (manuscriptSigma L : Rat) * weight w2 onePolarity →
            average (fun _ : Fin 1 => Formula.eval x polarityOr) < gam) :=
  manuscript_polarity_not_sound

end PvNP.RealizableHardness.ActualManyValuedPolarityKillChecks
