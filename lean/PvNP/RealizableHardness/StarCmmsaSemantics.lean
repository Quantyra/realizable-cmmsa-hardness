import PvNP.RealizableHardness.StarListDecoding
import PvNP.RealizableHardness.StarFormulaInterface

/-!
  The finite semantics bridge for the compiled star instance.

  `starWeight` is the occurrence weight after the alphabet normalization
  `1 / alphabetMass`.  A Boolean assignment selects labels by its `true`
  coordinates; `compiledSatisfaction` is the mass of the compiled formulas
  that evaluate to `true`.  This file is only the semantic bridge: it does
  not instantiate a source promise or a hardness theorem.
-/
namespace PvNP.RealizableHardness.StarCmmsaSemantics

open scoped BigOperators
open PvNP.RealizableHardness.StarListDecoding
open PvNP.RealizableHardness.StarFormulaInterface

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]
  {Sigma : V → Type*} [∀ v, Fintype (Sigma v)]
  [∀ v, Nonempty (Sigma v)] {m : ℕ}

/-- Occurrence weight of a label, normalized by the total alphabet mass. -/
def starWeight (p : E → ℝ) (edges : E → Star V Sigma m)
    (v : V) (_a : Sigma v) : ℝ :=
  occurrenceWeight p edges v / alphabetMass p edges

/-- The reciprocal alphabet mass used as the normalized list budget. -/
def starBudget (p : E → ℝ) (edges : E → Star V Sigma m) : ℝ :=
  1 / alphabetMass p edges

/-- Cost of a Boolean labeling, summing the normalized weights of its true
coordinates. -/
def assignmentCost (p : E → ℝ) (edges : E → Star V Sigma m)
    (Z : (Σ v, Sigma v) → Bool) : ℝ :=
  ∑ v, ∑ a, if Z ⟨v, a⟩ = true then starWeight p edges v a else 0

/-- Mass of edges whose compiled optional formula evaluates to true. -/
def compiledSatisfaction (p : E → ℝ) (edges : E → Star V Sigma m)
    (Z : (Σ v, Sigma v) → Bool) : ℝ :=
  eventMass p (fun e => evalOpt Z (compile (edges e)) = true)

theorem starWeight_sum (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hnorm : ∑ e, p e = 1) (edges : E → Star V Sigma m) :
    ∑ v, ∑ a, starWeight p edges v a = 1 := by
  have hL : 0 < alphabetMass p edges :=
    lt_of_lt_of_le zero_lt_one (alphabetMass_ge_one p hp hnorm edges)
  unfold starWeight
  calc
    (∑ v, ∑ a, occurrenceWeight p edges v / alphabetMass p edges) =
        (∑ v, occurrenceWeight p edges v * (Fintype.card (Sigma v) : ℝ)) /
          alphabetMass p edges := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_div]
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (Fintype.card (Sigma v) : ℝ) * occurrenceWeight p edges v /
        alphabetMass p edges = _
      ring
    _ = 1 := by
      change alphabetMass p edges / alphabetMass p edges = 1
      exact div_self hL.ne'

theorem assignmentCost_eq_selectedWeight (p : E → ℝ)
    (edges : E → Star V Sigma m)
    (Z : (Σ v, Sigma v) → Bool) :
    assignmentCost p edges Z = selectedWeight p edges (selected Z) := by
  classical
  unfold assignmentCost selectedWeight starWeight variableWeight selected
  simp only [Finset.sum_filter]

theorem compiledSatisfaction_eq_witnessMass (p : E → ℝ)
    (edges : E → Star V Sigma m)
    (Z : (Σ v, Sigma v) → Bool) :
    compiledSatisfaction p edges Z =
      eventMass p (fun e => (edges e).listWitness (selected Z)) := by
  unfold compiledSatisfaction eventMass
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : evalOpt Z (compile (edges e)) = true
  · have hw := (eval_compile_iff_listWitness (edges e) Z).mp h
    simp [h, hw]
  · have hw : ¬ (edges e).listWitness (selected Z) := by
      intro hw
      exact h ((eval_compile_iff_listWitness (edges e) Z).mpr hw)
    simp [h, hw]

theorem constantAlphabet_alphabetMass_eq (p : E → ℝ)
    (hnorm : ∑ e, p e = 1) (edges : E → Star V Sigma m)
    {R : ℕ} (hR : ∀ v : V, Fintype.card (Sigma v) = R) :
    alphabetMass p edges = (R : ℝ) := by
  unfold alphabetMass
  simp_rw [hR]
  rw [← Finset.sum_mul, occurrenceWeight_sum p hnorm edges]
  norm_num

theorem compiledSatisfaction_le_three_quarters (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hnorm : ∑ e, p e = 1)
    (edges : E → Star V Sigma m) (rho zeta : ℝ)
    (Z : (Σ v, Sigma v) → Bool) (hrho : 0 < rho)
    (hcost : assignmentCost p edges Z ≤ rho * starBudget p edges)
    (hvalue : ∀ l : Labeling Sigma, score p edges l ≤ zeta)
    (hparam : (8 * rho) ^ (m + 1) * zeta ≤ 5 / 8) :
    compiledSatisfaction p edges Z ≤ 3 / 4 := by
  have hbudget : selectedWeight p edges (selected Z) ≤
      rho * (1 / alphabetMass p edges) := by
    rw [← assignmentCost_eq_selectedWeight p edges Z]
    simpa [starBudget] using hcost
  have hlist : listBudget p edges (selected Z) ≤ rho :=
    (selectedWeight_budget_iff p hp hnorm edges (selected Z) rho).mp hbudget
  have hw := witness_mass_le_three_quarters p hp edges (selected Z)
    rho zeta hrho hlist hvalue hparam
  rw [compiledSatisfaction_eq_witnessMass p edges Z]
  exact hw

end
end PvNP.RealizableHardness.StarCmmsaSemantics
