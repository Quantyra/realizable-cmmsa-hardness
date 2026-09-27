import PvNP.RealizableHardness.ActualFormulaProduct
import PvNP.RealizableHardness.StarCmmsaSemantics

/-!
Uniform compiled stars, repeated under manuscript gamma.

`compiledSatisfaction_le_three_quarters` bounds one uniform star family by
`3/4` inside the normalized cost ball, once every labeling has score at most
`zeta` and `(8ρ)^{m+1} ζ ≤ 5/8`. `product_average_lt_certifiedGamma_index`
turns that rational average into a `q`-fold AND strictly below
`certifiedGamma`. An accepting labeling has one-hot cost equal to the
normalized budget and q-fold satisfaction `1`. The score bound stays a
hypothesis: this file does not read a 3CNF, does not build a `SeededMap`,
and does not inhabit `hSrcCmmsa`.
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

/-- One true coordinate per vertex, at the labeling `l`. -/
def oneHot (l : Labeling Sigma) : (Σ v, Sigma v) → Bool :=
  fun p => decide (p.2 = l p.1)

omit [Fintype V] [∀ (v : V), Nonempty (Sigma v)] in
theorem selected_oneHot (l : Labeling Sigma) (v : V) :
    selected (oneHot l) v = {l v} := by
  classical
  ext a
  unfold selected oneHot
  simp [Finset.mem_filter]

omit [Fintype E] [Nonempty E] in
theorem accepting_compiles (edges : E → Star V Sigma m) (l : Labeling Sigma)
    (hacc : ∀ e, (edges e).accepts l) (e : E) :
    (compile (edges e)).isSome = true := by
  cases h : compile (edges e) with
  | some _ => rfl
  | none => exact ((compile_eq_none_iff (edges e)).mp h ⟨l, hacc e⟩).elim

theorem uniform_accepting_cost (edges : E → Star V Sigma m) (l : Labeling Sigma)
    (hacc : ∀ e, (edges e).accepts l) :
    assignmentCost uniformEdge edges (oneHot l) = starBudget uniformEdge edges ∧
      compiledSatisfaction uniformEdge edges (oneHot l) = 1 := by
  have hA : ∀ v, selected (oneHot l) v = {l v} := fun v => selected_oneHot l v
  have hcost : assignmentCost uniformEdge edges (oneHot l) =
      starBudget uniformEdge edges := by
    rw [assignmentCost_eq_selectedWeight]
    simp only [selectedWeight, variableWeight, hA, Finset.sum_singleton, starBudget]
    rw [← Finset.sum_div, occurrenceWeight_sum uniformEdge uniformEdge_sum edges]
  have hsat : compiledSatisfaction uniformEdge edges (oneHot l) = 1 := by
    rw [compiledSatisfaction_eq_witnessMass]
    have hw : ∀ e, (edges e).listWitness (selected (oneHot l)) := by
      intro e
      refine ⟨l, hacc e, ?_⟩
      intro j
      rw [hA]
      exact Finset.mem_singleton_self _
    unfold eventMass
    simp [hw, uniformEdge_sum]
  exact ⟨hcost, hsat⟩

theorem uniform_accepting_product (edges : E → Star V Sigma m) (l : Labeling Sigma)
    (hacc : ∀ e, (edges e).accepts l) {q : Nat} (hq : 0 < q) :
    average (fun ι : Fin q → E =>
        Formula.eval (oneHot l)
          (andAll (fun j =>
              compiledFormula edges (accepting_compiles edges l hacc) (ι j)) hq)) = 1 := by
  have hsat := (uniform_accepting_cost edges l hacc).2
  have hcast :=
    uniform_average_eq_compiledSatisfaction edges (accepting_compiles edges l hacc) (oneHot l)
  have hbase : average (fun e =>
      Formula.eval (oneHot l)
        (compiledFormula edges (accepting_compiles edges l hacc) e)) = 1 := by
    apply Rat.cast_injective (α := ℝ)
    rw [hcast, hsat]
    simp
  rw [average_andAll_pow_index _ _ hq, hbase, one_pow]

end

end PvNP.RealizableHardness.ActualCompiledProduct
