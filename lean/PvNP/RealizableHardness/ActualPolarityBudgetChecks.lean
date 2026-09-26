import PvNP.RealizableHardness.ActualPolarityBudget

/-!
Checks call the shipped polarity-budget lemmas.
-/
namespace PvNP.RealizableHardness.ActualPolarityBudgetChecks

open PvNP.RealizableHardness
open ActualPolarityBudget

example {k sig : Nat} (hk : 1 ≤ k) (hσ : 2 ≤ sig) : k + 1 ≤ sig * k :=
  two_cover_le hk hσ

example : (1 + 1 : Nat) ≤ 2 * 1 :=
  two_cover_le (by decide) (by decide)

example {n k sig : Nat} (hn : 0 < n) (hk : 1 ≤ k) (hσ : 2 ≤ sig) :
    ((k + 1 : Nat) : Rat) / n ≤ (sig : Rat) * (((k : Nat) : Rat) / n) :=
  extension_cost_le hn hk hσ

example :
    Formula.eval (fun _ : Fin 2 => true)
      (Formula.or (Formula.var ⟨0, by decide⟩) (Formula.var ⟨1, by decide⟩)) = true :=
  polarity_or_extension

example {L : Nat} (h : 1 ≤ ActualHeadlineParameters.rofSigma L) :
    2 ≤ ActualHeadlineParameters.rofSigma L :=
  headline_sigma_ge_two h

example : weight w2 bothPolarities = 1 :=
  weight_bothPolarities

example : weight w2 onePolarity = 1 / 2 :=
  weight_onePolarity

example (sig : Nat) (gam : Rat) (hσ : 2 ≤ sig) (hγ : gam ≤ 1) :
    ¬ (∀ x : Fin 2 → Bool,
        weight w2 x ≤ (sig : Rat) * weight w2 onePolarity →
          average (fun _ : Fin 1 => Formula.eval x polarityOr) < gam) :=
  not_sound_two_polarity sig gam hσ hγ

end PvNP.RealizableHardness.ActualPolarityBudgetChecks
