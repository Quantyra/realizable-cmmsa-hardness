import PvNP.RealizableHardness.ActualBudgetOneObstruction
import PvNP.RealizableHardness.ActualPolarityBudget

/-!
Equal-weight polarity is not a manuscript no-predicate.

The positive OR of the two polarity coordinates is satisfied by lighting
either coordinate, at cost `1/2`. Lighting both costs `1`. For every large
`L`, `manuscriptSigma L ≥ 2`, so both polarities lie under
`σ` times the one-polarity cost, and the satisfaction stays `1`.

A many-valued compiler that only swaps which positive formula is written
on this weight pair does not land in the manuscript no-set. This file
does not construct a `Complexity.FP` `MapReducesVia`, does not decide
3SAT, and does not assemble Theorem 1 or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualManyValuedPolarityKill

open ActualPositiveFormulaMono
open ActualPolarityBudget
open ActualBudgetOneObstruction
open ActualHeadlineParameters

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem manuscript_polarity_not_sound :
    ∃ L0, ∀ L, L0 ≤ L → ∀ gam : Rat, gam ≤ 1 →
      ¬ (∀ x : Fin 2 → Bool,
          weight w2 x ≤ (manuscriptSigma L : Rat) * weight w2 onePolarity →
            average (fun _ : Fin 1 => Formula.eval x polarityOr) < gam) := by
  obtain ⟨L0, hL0⟩ := manuscriptSigma_ge_two_eventual
  refine ⟨L0, ?_⟩
  intro L hL gam hγ
  exact not_sound_two_polarity (manuscriptSigma L) gam (hL0 L hL) hγ

end PvNP.RealizableHardness.ActualManyValuedPolarityKill
