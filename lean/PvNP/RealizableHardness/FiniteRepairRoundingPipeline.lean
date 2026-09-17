import PvNP.RealizableHardness.WeightRounding

namespace PvNP.RealizableHardness.FiniteRepairRoundingPipeline
open scoped BigOperators
open WeightRounding

/-- Parameters and validity only: neither a YES nor a NO promise is stored. -/
structure Parameters {V : Type*} [Fintype V] (w : V -> Rat) where
  s : Rat
  eps : Rat
  gam : Rat
  sig : Nat
  weights_pos : forall v, 0 < w v
  weights_sum : ∑ v, w v = 1
  s_pos : 0 < s
  s_le_one : s <= 1
  eps_nonneg : 0 <= eps
  gam_pos : 0 < gam
  gam_lt_half : gam < 1 / 2
  sig_ge : 8 <= sig
  small : eps * sig <= gam / 2

variable {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
variable {w : V -> Rat}

def lam (p : Parameters w) : Rat := (p.sig : Rat) * p.s / p.gam
def budget (p : Parameters w) : Rat := (p.s + lam p * p.eps) / (1 + lam p)
noncomputable def weights (p : Parameters w) : V ⊕ I -> Rat := repairedWeights w (lam p)
def scale (p : Parameters w) : Nat := dyadicScale (Fintype.card (V ⊕ I)) (budget p)
noncomputable def outputWeights (p : Parameters w) : V ⊕ I -> Rat :=
  roundedWeights (weights p) (scale (I := I) p)
noncomputable def outputBudget (p : Parameters w) : Rat :=
  roundedBudget (weights (I := I) p) (scale (I := I) p) (budget p)
noncomputable def outputDenominator (p : Parameters w) : Nat :=
  denominator (weights (I := I) p) (scale (I := I) p)
def outputFormula (F : I -> Formula V) : I -> Formula (V ⊕ I) := Formula.repair F
def gap (p : Parameters w) : Nat := (p.sig / 4) / 2

lemma lam_pos (p : Parameters w) : 0 < lam p := by
  unfold lam
  have h : (0 : Rat) < p.sig := by exact_mod_cast (show 0 < p.sig by have := p.sig_ge; omega)
  exact div_pos (mul_pos h p.s_pos) p.gam_pos

lemma eps_le_one (p : Parameters w) : p.eps <= 1 := by
  have h : (8 : Rat) <= p.sig := by exact_mod_cast p.sig_ge
  have hm := mul_le_mul_of_nonneg_left h p.eps_nonneg
  have := p.small
  have := p.gam_lt_half
  nlinarith

lemma budget_pos (p : Parameters w) : 0 < budget p :=
  repairedBudget_pos _ _ _ p.s_pos p.eps_nonneg (lam_pos p).le

lemma budget_le_one (p : Parameters w) : budget p <= 1 :=
  repairedBudget_le_one _ _ _ p.s_le_one (eps_le_one p) (lam_pos p).le

lemma weights_pos (p : Parameters w) : forall z : V ⊕ I, 0 < weights p z :=
  repairedWeights_pos w (lam p) p.weights_pos (lam_pos p)

lemma weights_sum (p : Parameters w) : ∑ z : V ⊕ I, weights p z = 1 :=
  repairedWeights_sum w (lam p) p.weights_sum (lam_pos p).le

/-- The output instance depends only on input weights, formulas and parameters. -/
theorem output_valid (p : Parameters w) :
    (forall z : V ⊕ I, 0 < outputWeights p z) ∧
    (∑ z : V ⊕ I, outputWeights p z = 1) ∧
    (0 < outputBudget (I := I) p ∧ outputBudget (I := I) p <= 1) ∧
    1 <= gap p ∧ 0 < 2 * p.gam ∧ 2 * p.gam < 1 := by
  have hD := dyadicScale_pos (Fintype.card (V ⊕ I)) (budget p)
  have hw := weights_pos (I := I) p
  have hn := weights_sum (I := I) p
  refine ⟨roundedWeights_pos _ _ hw hn hD,
    roundedWeights_sum _ _ (fun z => (hw z).le) hn hD,
    roundedBudget_valid _ _ _ (fun z => (hw z).le) hn hD (budget_pos p), ?_, ?_, ?_⟩
  · unfold gap; have := p.sig_ge; omega
  · have := p.gam_pos; linarith
  · have := p.gam_lt_half; linarith

/-- YES preservation is a separate implication, never conjoined as a premise with NO. -/
theorem yes_preserved (p : Parameters w) (F : I -> Formula V)
    (x : V -> Bool) (hx : weight w x <= p.s)
    (hy : 1 - p.eps <= average (fun i => Formula.eval x (F i))) :
    ∃ y : V ⊕ I -> Bool, weight (outputWeights p) y <= outputBudget (I := I) p ∧
      forall i, Formula.eval y (outputFormula F i) = true := by
  obtain ⟨e, he, hf⟩ := exception_completeness w (fun i x => Formula.eval x (F i))
    p.s p.eps (lam p) (lam_pos p).le x hx hy
  refine ⟨Sum.elim x e, ?_, ?_⟩
  · apply rounding_complete (weights (I := I) p) (scale (I := I) p) (budget p)
      (fun z => (weights_pos p z).le)
    change weight (repairedWeights w (lam p)) (Sum.elim x e) <= budget p
    rw [repairedWeight_eq_sum]
    exact he
  · intro i
    exact (Formula.eval_repair F x e i).trans (hf i)

/-- NO preservation quantifies over every assignment to the complete new coordinate set. -/
theorem no_preserved (p : Parameters w) (F : I -> Formula V)
    (hno : forall x, weight w x <= (p.sig : Rat) * p.s ->
      average (fun i => Formula.eval x (F i)) < p.gam)
    (y : V ⊕ I -> Bool)
    (hy : weight (outputWeights p) y <= (gap p : Rat) * outputBudget (I := I) p) :
    average (fun i => Formula.eval y (outputFormula F i)) < 2 * p.gam := by
  apply rounding_sound (weights (I := I) p) (fun i y => Formula.eval y (Formula.repair F i))
    (scale (I := I) p) (p.sig / 4) (budget p) (2 * p.gam)
    (fun z => (weights_pos p z).le) (weights_sum p)
    (dyadicScale_pos _ _) (budget_pos p)
    (by have := p.sig_ge; omega) (dyadicScale_lower _ _) ?_ y hy
  intro z hz
  exact Formula.repair_sound w F p.s p.gam p.eps p.sig
    (fun v => (p.weights_pos v).le) p.s_pos p.sig_ge p.gam_pos p.eps_nonneg p.small hno z hz

omit [Fintype V] [Fintype I] [Nonempty I] in
@[simp] theorem output_leaves (F : I -> Formula V) (i : I) :
    Formula.leaves (outputFormula F i) = Formula.leaves (F i) + 1 :=
  Formula.leaves_repair F i

/-- The positive repair addition can only improve this reciprocal bound. -/
theorem reciprocal_budget (p : Parameters w) :
    1 / budget p <= 1 / p.s + (p.sig : Rat) / p.gam := by
  have hl := lam_pos p
  have hs := p.s_pos
  have hg := p.gam_pos
  have he : 1 / budget p <= (1 + lam p) / p.s := by
    unfold budget
    rw [one_div_div]
    apply div_le_div_of_nonneg_left (by linarith : 0 <= 1 + lam p) hs
    exact le_add_of_nonneg_right (mul_nonneg hl.le p.eps_nonneg)
  calc
    _ <= (1 + lam p) / p.s := he
    _ = _ := by
      unfold lam
      field_simp [ne_of_gt hs, ne_of_gt hg]

theorem denominator_bound (p : Parameters w) (P Q : Nat)
    (hP : 1 / p.s <= (P : Rat)) (hQ : (p.sig : Rat) / p.gam <= (Q : Rat)) :
    outputDenominator (I := I) p <=
      16 * (Fintype.card (V ⊕ I) + 1) * (P + Q) + Fintype.card (V ⊕ I) := by
  apply denominator_bound_of_inverse_budget (weights (I := I) p) (budget p) (P + Q)
    (fun z => (weights_pos p z).le) (weights_sum p) (budget_pos p) (budget_le_one p)
  have := reciprocal_budget p
  push_cast
  linarith

/-- Positive bounded integer numerators for every final coordinate and the clipped budget. -/
theorem output_common_denominator (p : Parameters w) :
    0 < outputDenominator (I := I) p ∧
    (forall z : V ⊕ I,
      0 < coordinate (weights p) (scale (I := I) p) z ∧
      coordinate (weights p) (scale (I := I) p) z <= outputDenominator (I := I) p ∧
      outputWeights p z * outputDenominator (I := I) p =
        (coordinate (weights p) (scale (I := I) p) z : Rat)) ∧
    (0 < budgetNumerator (weights (I := I) p) (scale (I := I) p) (budget p) ∧
      budgetNumerator (weights (I := I) p) (scale (I := I) p) (budget p) <= outputDenominator (I := I) p ∧
      outputBudget (I := I) p * outputDenominator (I := I) p =
        (budgetNumerator (weights (I := I) p) (scale (I := I) p) (budget p) : Rat)) :=
  common_denominator (weights (I := I) p) (scale (I := I) p) (budget p)
    (weights_pos p) (weights_sum p) (dyadicScale_pos _ _) (budget_pos p)

end PvNP.RealizableHardness.FiniteRepairRoundingPipeline
