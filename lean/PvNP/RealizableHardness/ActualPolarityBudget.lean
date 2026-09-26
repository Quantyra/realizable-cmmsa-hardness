import PvNP.RealizableHardness.ActualManuscriptGapObstruction
import PvNP.RealizableHardness.ActualPositiveFormulaMono

/-!
Equal-weight polarity budget at the headline promise.

A consistent assignment that lights `k ≥ 1` coordinates costs `k/n`.
Turning one more coordinate on costs `(k+1)/n`. Whenever `σ ≥ 2`,
`k + 1 ≤ σ * k`, so the extra coordinate still lies under `σ` times the
original cost. Positive formulas stay true under that extension.

Headline `rofSigma` is in this regime whenever `1 ≤ rofSigma`, by the shipped
`rofSigma_ge_two_of_one`. This file does not construct a `MapReducesVia`,
does not place a compiler in `Complexity.FP`, and does not prove Theorem 1
or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualPolarityBudget

open ActualPositiveFormulaMono
open ActualManuscriptGapObstruction
open ActualHeadlineParameters

theorem two_cover_le {k sig : Nat} (hk : 1 ≤ k) (hσ : 2 ≤ sig) :
    k + 1 ≤ sig * k := by
  have h2 : k + 1 ≤ 2 * k := by
    have hk2 : k + k = 2 * k := by ring
    have hle : k + 1 ≤ k + k := Nat.add_le_add_left hk k
    simpa [hk2] using hle
  exact h2.trans (Nat.mul_le_mul_right k hσ)

theorem extension_cost_le {n k sig : Nat} (hn : 0 < n) (hk : 1 ≤ k)
    (hσ : 2 ≤ sig) :
    ((k + 1 : Nat) : Rat) / n ≤ (sig : Rat) * (((k : Nat) : Rat) / n) := by
  have hden : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hnum : ((k + 1 : Nat) : Rat) ≤ (sig : Rat) * (k : Rat) := by
    exact_mod_cast two_cover_le hk hσ
  have hmul : (sig : Rat) * ((k : Rat) / n) = ((sig : Rat) * (k : Rat)) / n := by
    field_simp
  rw [hmul]
  exact (div_le_div_iff_of_pos_right hden).mpr hnum

/-- One true polarity extends to both polarities, and the positive OR stays true. -/
theorem polarity_or_extension :
    Formula.eval (fun _ : Fin 2 => true)
      (Formula.or (Formula.var ⟨0, by decide⟩) (Formula.var ⟨1, by decide⟩)) = true := by
  have hx :
      Formula.eval (fun v : Fin 2 => decide (v.val = 0))
        (Formula.or (Formula.var ⟨0, by decide⟩) (Formula.var ⟨1, by decide⟩)) = true := by
    simp [Formula.eval]
  exact eval_mono (fun _ _ => rfl) _ hx

theorem headline_sigma_ge_two {L : Nat} (h : 1 ≤ rofSigma L) : 2 ≤ rofSigma L :=
  rofSigma_ge_two_of_one h

def w2 : Fin 2 → Rat := fun _ => (1 : Rat) / 2

def onePolarity (v : Fin 2) : Bool := decide (v.val = 0)

def bothPolarities : Fin 2 → Bool := fun _ => true

def polarityOr : Formula (Fin 2) :=
  Formula.or (Formula.var ⟨0, by decide⟩) (Formula.var ⟨1, by decide⟩)

theorem weight_onePolarity : weight w2 onePolarity = 1 / 2 := by
  unfold weight w2 onePolarity
  simp

theorem weight_bothPolarities : weight w2 bothPolarities = 1 := by
  unfold weight w2 bothPolarities
  simp

theorem both_le_sigma_budget (sig : Nat) (hσ : 2 ≤ sig) :
    weight w2 bothPolarities ≤ (sig : Rat) * weight w2 onePolarity := by
  rw [weight_bothPolarities, weight_onePolarity]
  have hσR : (2 : Rat) ≤ (sig : Rat) := by exact_mod_cast hσ
  calc
    (1 : Rat) = 2 * (1 / 2) := by norm_num
    _ ≤ (sig : Rat) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hσR (by norm_num)

/-- Both polarities stay inside the no-budget and keep the positive OR true. -/
theorem not_sound_two_polarity (sig : Nat) (gam : Rat) (hσ : 2 ≤ sig)
    (hγ : gam ≤ 1) :
    ¬ (∀ x : Fin 2 → Bool,
        weight w2 x ≤ (sig : Rat) * weight w2 onePolarity →
          average (fun _ : Fin 1 => Formula.eval x polarityOr) < gam) := by
  intro hno
  have hcost := both_le_sigma_budget sig hσ
  have htrue : Formula.eval bothPolarities polarityOr = true := by
    unfold bothPolarities polarityOr
    exact polarity_or_extension
  have hfun : (fun _ : Fin 1 => Formula.eval bothPolarities polarityOr) = fun _ => true := by
    funext i
    exact htrue
  have havg : average (fun _ : Fin 1 => Formula.eval bothPolarities polarityOr) = 1 := by
    rw [hfun]
    exact average_true
  have hlt := hno bothPolarities hcost
  rw [havg] at hlt
  exact not_lt_of_ge hγ hlt

end PvNP.RealizableHardness.ActualPolarityBudget
