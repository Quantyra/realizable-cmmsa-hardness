import PvNP.RealizableHardness.ActualFormulaProduct
import PvNP.RealizableHardness.StarCmmsaSemantics

/-!
Uniform compiled stars, repeated under manuscript gamma.

`compiledSatisfaction_le_three_quarters` bounds one uniform star family by
`3/4` inside the normalized cost ball, once every labeling has score at most
`zeta` and `(8ρ)^{m+1} ζ ≤ 5/8`. `product_average_lt_certifiedGamma_index`
turns that rational average into a `q`-fold AND strictly below
`certifiedGamma`. The score bound stays a hypothesis: this file does not read
a 3CNF, does not build a `SeededMap`, and does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualCompiledProduct

open PvNP.RealizableHardness
open ActualFormulaProduct
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
  {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]
  {m : ℕ}

def uniformEdge (_e : E) : ℝ := (1 : ℝ) / (Fintype.card E : ℝ)

theorem uniformEdge_nonneg (e : E) : 0 ≤ uniformEdge e := by
  unfold uniformEdge
  positivity

theorem uniformEdge_sum : ∑ e : E, uniformEdge e = 1 := by
  unfold uniformEdge
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hc]

def compiledFormula (edges : E → Star V Sigma m)
    (hcompile : ∀ e, (compile (edges e)).isSome = true) (e : E) :
    Formula (Σ v, Sigma v) :=
  (compile (edges e)).get (hcompile e)

omit [Fintype V] [Fintype E] [Nonempty E] [∀ (v : V), Nonempty (Sigma v)] in
theorem eval_compiledFormula (edges : E → Star V Sigma m)
    (hcompile : ∀ e, (compile (edges e)).isSome = true)
    (Z : (Σ v, Sigma v) → Bool) (e : E) :
    Formula.eval Z (compiledFormula edges hcompile e) =
      evalOpt Z (compile (edges e)) := by
  cases hc : compile (edges e) with
  | none =>
      have h := hcompile e
      simp [hc] at h
  | some f =>
      simp [compiledFormula, evalOpt, hc]

omit [Fintype V] [Nonempty E] [∀ (v : V), Nonempty (Sigma v)] in
theorem uniform_average_eq_compiledSatisfaction
    (edges : E → Star V Sigma m)
    (hcompile : ∀ e, (compile (edges e)).isSome = true)
    (Z : (Σ v, Sigma v) → Bool) :
    (average (fun e => Formula.eval Z (compiledFormula edges hcompile e)) : ℝ) =
      compiledSatisfaction uniformEdge edges Z := by
  classical
  unfold average compiledSatisfaction eventMass
  rw [Rat.cast_div, Rat.cast_sum]
  have hcastCard : ((Fintype.card E : Rat) : ℝ) = (Fintype.card E : ℝ) := by
    norm_cast
  rw [hcastCard]
  let bit : E → Rat := fun e =>
    if Formula.eval Z (compiledFormula edges hcompile e) = true then 1 else 0
  have hpush :
      (∑ e, (bit e : ℝ)) =
        ∑ e, if evalOpt Z (compile (edges e)) = true then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro e _
    have heq := eval_compiledFormula edges hcompile Z e
    cases h : Formula.eval Z (compiledFormula edges hcompile e)
    · rw [h] at heq
      have hop : evalOpt Z (compile (edges e)) = false := heq.symm
      simp [bit, h, hop]
    · rw [h] at heq
      have hop : evalOpt Z (compile (edges e)) = true := heq.symm
      simp [bit, h, hop]
  rw [hpush, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro e _
  by_cases h : evalOpt Z (compile (edges e)) = true
  · simp [h, one_div, uniformEdge]
  · simp [h]

theorem uniform_compiled_product_lt_certifiedGamma
    {L : Nat}
    (edges : E → Star V Sigma m)
    (hcompile : ∀ e, (compile (edges e)).isSome = true)
    (rho zeta : ℝ) (hrho : 0 < rho)
    (hvalue : ∀ l : Labeling Sigma, score uniformEdge edges l ≤ zeta)
    (hparam : (8 * rho) ^ (m + 1) * zeta ≤ 5 / 8)
    (hq : 0 < q (certifiedM L))
    (Z : (Σ v, Sigma v) → Bool)
    (hcost : assignmentCost uniformEdge edges Z ≤ rho * starBudget uniformEdge edges) :
    average (fun ι : Fin (q (certifiedM L)) → E =>
        Formula.eval Z
          (andAll (fun j => compiledFormula edges hcompile (ι j)) hq)) <
      certifiedGamma L := by
  have hsat :=
    compiledSatisfaction_le_three_quarters uniformEdge uniformEdge_nonneg
      uniformEdge_sum edges rho zeta Z hrho hcost hvalue hparam
  have h34 : (3 : ℝ) / 4 = (Rat.cast ((3 : Rat) / 4) : ℝ) := by
    rw [Rat.cast_div]
    simp
  have hleR :
      (Rat.cast (average (fun e => Formula.eval Z (compiledFormula edges hcompile e))) : ℝ) ≤
        (Rat.cast ((3 : Rat) / 4) : ℝ) := by
    rw [uniform_average_eq_compiledSatisfaction edges hcompile Z, ← h34]
    exact hsat
  have hle :
      average (fun e => Formula.eval Z (compiledFormula edges hcompile e)) ≤
        (3 : Rat) / 4 :=
    Rat.cast_le.mp hleR
  exact product_average_lt_certifiedGamma_index
    (compiledFormula edges hcompile) Z hq hle

end

end PvNP.RealizableHardness.ActualCompiledProduct
