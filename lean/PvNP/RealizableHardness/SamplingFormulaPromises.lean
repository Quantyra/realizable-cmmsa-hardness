import PvNP.RealizableHardness.SamplingGuarantee
import PvNP.RealizableHardness.FiniteRepairRoundingPipeline
import PvNP.RealizableHardness.ComputableSampleCount

/-! Actual finite sampled-formula promises and probabilities. No encoded runtime claim. -/
namespace PvNP.RealizableHardness.SamplingFormulaPromises
open scoped BigOperators
open SamplingGuarantee JointSamplingLaw FiniteConcentration

variable {N S M : Nat}

/-- Trial positions remain distinct when several draws select the same atom. -/
def sampled (F : Nat → Formula (Fin N)) (draws : Fin M → Fin S) :
    Fin M → Formula (Fin N) := fun i => F (draws i).val

def events (F : Nat → Formula (Fin N)) (x : Fin N → Bool) (j : Nat) : Bool :=
  Formula.eval x (F j)

/-- This identity also covers zero trials, with both divisions equal to zero. -/
theorem empirical_eq_average (F : Nat → Formula (Fin N))
    (draws : Fin M → Fin S) (x : Fin N → Bool) :
    empirical (fun i : Fin S => events F x i.val) M draws =
      (average (fun i => Formula.eval x (sampled F draws i)) : Real) := by
  unfold empirical average indicator sampled events
  simp only [Fintype.card_fin]
  push_cast <;> simp only [apply_ite, Rat.cast_one, Rat.cast_zero]

theorem good_yes_average (p : Nat → Rat) (F : Nat → Formula (Fin N))
    (draws : Fin M → Fin S) (eps : Rat) (heps : 0 ≤ eps)
    (hgood : Good p S N M (events F) eps draws) (x : Fin N → Bool)
    (hyes : 1 - (eps : Real) / 4 ≤ originalMean p S (events F x)) :
    1 - eps ≤ average (fun i => Formula.eval x (sampled F draws i)) := by
  have h := (abs_lt.mp (hgood x)).1
  rw [empirical_eq_average] at h
  have hepsR : (0 : Real) ≤ eps := by exact_mod_cast heps
  have hout : (1 : Real) - eps ≤
      (average (fun i => Formula.eval x (sampled F draws i)) : Real) := by linarith
  exact_mod_cast hout

theorem good_no_average (p : Nat → Rat) (F : Nat → Formula (Fin N))
    (draws : Fin M → Fin S) (eps gam : Rat)
    (hmargin : eps / 4 < gam / 2)
    (hgood : Good p S N M (events F) eps draws) (x : Fin N → Bool)
    (hno : originalMean p S (events F x) ≤ (gam : Real) / 2) :
    average (fun i => Formula.eval x (sampled F draws i)) < gam := by
  have h := (abs_lt.mp (hgood x)).2
  rw [empirical_eq_average] at h
  have hm : (eps : Real) / 4 < (gam : Real) / 2 := by exact_mod_cast hmargin
  have hout : (average (fun i => Formula.eval x (sampled F draws i)) : Real) < gam :=
    by linarith
  exact_mod_cast hout

/-- The NO margin follows from the actual repair parameters. -/
theorem parameter_margin {w : Fin N → Rat}
    (a : FiniteRepairRoundingPipeline.Parameters w) : a.eps / 4 < a.gam / 2 := by
  have hs : (8 : Rat) ≤ a.sig := by exact_mod_cast a.sig_ge
  have hm := mul_le_mul_of_nonneg_left hs a.eps_nonneg
  have hc := a.small
  have hg := a.gam_pos
  nlinarith

/-- The same input-only construction is used for both separate promise implications. -/
def output (F : Nat → Formula (Fin N)) (draws : Fin M → Fin S) :
    Fin M → Formula (Fin N ⊕ Fin M) :=
  FiniteRepairRoundingPipeline.outputFormula (sampled F draws)

theorem good_yes_output {w : Fin N → Rat}
    (a : FiniteRepairRoundingPipeline.Parameters w) (p : Nat → Rat)
    (F : Nat → Formula (Fin N)) (draws : Fin M → Fin S) (hM : 0 < M)
    (hgood : Good p S N M (events F) a.eps draws)
    (x : Fin N → Bool) (hx : weight w x ≤ a.s)
    (hyes : 1 - (a.eps : Real) / 4 ≤ originalMean p S (events F x)) :
    ∃ y : Fin N ⊕ Fin M → Bool,
      weight (FiniteRepairRoundingPipeline.outputWeights a) y ≤
        FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a ∧
      ∀ i, Formula.eval y (output F draws i) = true := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact FiniteRepairRoundingPipeline.yes_preserved a (sampled F draws) x hx
    (good_yes_average p F draws a.eps a.eps_nonneg hgood x hyes)

theorem good_no_output {w : Fin N → Rat}
    (a : FiniteRepairRoundingPipeline.Parameters w) (p : Nat → Rat)
    (F : Nat → Formula (Fin N)) (draws : Fin M → Fin S) (hM : 0 < M)
    (hgood : Good p S N M (events F) a.eps draws)
    (hno : ∀ x, weight w x ≤ (a.sig : Rat) * a.s →
      originalMean p S (events F x) ≤ (a.gam : Real) / 2)
    (y : Fin N ⊕ Fin M → Bool)
    (hy : weight (FiniteRepairRoundingPipeline.outputWeights a) y ≤
      (FiniteRepairRoundingPipeline.gap a : Rat) *
        FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a) :
    average (fun i => Formula.eval y (output F draws i)) < 2 * a.gam := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  apply FiniteRepairRoundingPipeline.no_preserved a (sampled F draws) _ y hy
  intro x hx
  exact good_no_average p F draws a.eps a.gam (parameter_margin a) hgood x (hno x hx)

/-- Actual input bits select the original formulas; no deduplication occurs. -/
def fromSeeds (p : Nat → Rat) (S b M : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (F : Nat → Formula (Fin N))
    (seeds : SeedArray M b) : Fin M → Formula (Fin N) :=
  sampled F (sampleArray p S b M hn seeds)

@[simp] theorem fromSeeds_eval (p : Nat → Rat) (S b M : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (F : Nat → Formula (Fin N))
    (seeds : SeedArray M b) (x : Fin N → Bool) (i : Fin M) :
    Formula.eval x (fromSeeds p S b M hn F seeds i) =
      events F x (sampleArray p S b M hn seeds i).val := rfl

@[simp] theorem output_leaves (F : Nat → Formula (Fin N))
    (draws : Fin M → Fin S) (i : Fin M) :
    Formula.leaves (output F draws i) = Formula.leaves (F (draws i).val) + 1 :=
  FiniteRepairRoundingPipeline.output_leaves (sampled F draws) i

/-- Monotonicity for the actual uniform seed count, without an assumed law. -/
theorem seedProbability_mono (M b : Nat) (E H : SeedArray M b → Prop)
    (h : ∀ seeds, E seeds → H seeds) :
    seedProbability M b E ≤ seedProbability M b H := by
  classical
  unfold seedProbability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro seeds _
  by_cases he : E seeds
  · simp [he, h seeds he]
  · simp only [he, if_false]
    split <;> norm_num

/-- The repaired and rounded YES event on the actual indexed sampled list. -/
def YesOutput {w : Fin N → Rat} (a : FiniteRepairRoundingPipeline.Parameters w)
    (F : Nat → Formula (Fin N)) (draws : Fin M → Fin S) : Prop :=
  ∃ y : Fin N ⊕ Fin M → Bool,
    weight (FiniteRepairRoundingPipeline.outputWeights a) y ≤
      FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a ∧
    ∀ i, Formula.eval y (output F draws i) = true

/-- The NO event quantifies over every output assignment in the floor-gap budget. -/
def NoOutput {w : Fin N → Rat} (a : FiniteRepairRoundingPipeline.Parameters w)
    (F : Nat → Formula (Fin N)) (draws : Fin M → Fin S) : Prop :=
  ∀ y : Fin N ⊕ Fin M → Bool,
    weight (FiniteRepairRoundingPipeline.outputWeights a) y ≤
      (FiniteRepairRoundingPipeline.gap a : Rat) *
        FiniteRepairRoundingPipeline.outputBudget (I := Fin M) a →
    average (fun i => Formula.eval y (output F draws i)) < 2 * a.gam

/-- A concrete natural count and actual dyadic precision, then genuine event inclusion. -/
theorem computed_event_probability (p : Nat → Rat) (S N P : Nat)
    (F : Nat → Formula (Fin N)) (eps : Rat)
    (hn : FiniteSampling.cumulative p S = 1) (hp : ∀ i, 0 ≤ p i)
    (heps : 0 < eps) (hInv : 1 / eps ≤ (P : Rat))
    (E : (Fin (ComputableSampleCount.count N P) → Fin S) → Prop)
    (hE : ∀ draws, Good p S N (ComputableSampleCount.count N P) (events F) eps draws →
      E draws) :
    (5 / 6 : Real) ≤ seedProbability (ComputableSampleCount.count N P) (precision S eps)
      (fun seeds => E (sampleArray p S (precision S eps)
        (ComputableSampleCount.count N P) hn seeds)) := by
  have hepsR : (0 : Real) < eps := by exact_mod_cast heps
  have hInvR : 1 / (eps : Real) ≤ (P : Real) := by exact_mod_cast hInv
  have hg := good_probability_of_learningThreshold p S (precision S eps) N
    (ComputableSampleCount.count N P) (events F) eps hn hp heps (precision_bound S eps)
    (ComputableSampleCount.learningThreshold_le_count N P eps hepsR hInvR)
  apply hg.trans
  apply seedProbability_mono
  intro seeds hs
  exact hE _ hs

/-- Separate YES implication: both requested confidence bounds for the same output event. -/
theorem computed_yes_probability {w : Fin N → Rat}
    (a : FiniteRepairRoundingPipeline.Parameters w) (p : Nat → Rat) (S P : Nat)
    (F : Nat → Formula (Fin N)) (hn : FiniteSampling.cumulative p S = 1)
    (hp : ∀ i, 0 ≤ p i) (heps : 0 < a.eps) (hInv : 1 / a.eps ≤ (P : Rat))
    (x : Fin N → Bool) (hx : weight w x ≤ a.s)
    (hyes : 1 - (a.eps : Real) / 4 ≤ originalMean p S (events F x)) :
    let prob := seedProbability (ComputableSampleCount.count N P) (precision S a.eps)
      (fun seeds => YesOutput a F (sampleArray p S (precision S a.eps)
        (ComputableSampleCount.count N P) hn seeds))
    (5 / 6 : Real) ≤ prob ∧ (2 / 3 : Real) ≤ prob := by
  dsimp only
  have h := computed_event_probability p S N P F a.eps hn hp heps hInv (YesOutput a F)
    (fun draws hg => good_yes_output a p F draws (ComputableSampleCount.count_pos N P)
      hg x hx hyes)
  exact ⟨h, (by norm_num : (2 / 3 : Real) ≤ 5 / 6).trans h⟩

/-- Separate NO implication with universal source and output quantifiers. -/
theorem computed_no_probability {w : Fin N → Rat}
    (a : FiniteRepairRoundingPipeline.Parameters w) (p : Nat → Rat) (S P : Nat)
    (F : Nat → Formula (Fin N)) (hn : FiniteSampling.cumulative p S = 1)
    (hp : ∀ i, 0 ≤ p i) (heps : 0 < a.eps) (hInv : 1 / a.eps ≤ (P : Rat))
    (hno : ∀ x, weight w x ≤ (a.sig : Rat) * a.s →
      originalMean p S (events F x) ≤ (a.gam : Real) / 2) :
    let prob := seedProbability (ComputableSampleCount.count N P) (precision S a.eps)
      (fun seeds => NoOutput a F (sampleArray p S (precision S a.eps)
        (ComputableSampleCount.count N P) hn seeds))
    (5 / 6 : Real) ≤ prob ∧ (2 / 3 : Real) ≤ prob := by
  dsimp only
  have h := computed_event_probability p S N P F a.eps hn hp heps hInv (NoOutput a F)
    (fun draws hg y hy => good_no_output a p F draws (ComputableSampleCount.count_pos N P)
      hg hno y hy)
  exact ⟨h, (by norm_num : (2 / 3 : Real) ≤ 5 / 6).trans h⟩

end PvNP.RealizableHardness.SamplingFormulaPromises
