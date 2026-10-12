import PvNP.RealizableHardness.ActualTotalOrderedStrategy
import PvNP.RealizableHardness.ActualFiniteLocalDerandomization

/-! Exact aggregation of the raw occurrence verifier into a finite payoff
kernel and local deterministic domination. External source soundness and
its question-domain comparison remain separate. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVerifierAggregation

open scoped BigOperators
open ActualFiniteLaw ActualFiniteLocalDerandomization ActualPrivateAssignmentLaw
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualOrderedDeletionLaw ActualOccurrenceAdviceLaw ActualTotalOrderedStrategy
open ActualOriginalOrderedRowLaw ActualNumericSourceHeight TripleRestrictionRank
open ActualTaggedRowDeletion SamplerParameters VectorAdvice
open ActualTaggedOrderedQuestionSourceBridge ActualLocalAssignmentStrategies
open ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance ActualVisibleQuestionCompletion

open CoveringSpan ActualQuestionMassBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

section FiniteVerifier

variable {W Q1 Q2 A B : Type*}
variable [Fintype W] [Fintype Q1] [Fintype Q2] [Fintype A] [Fintype B]

private theorem weighted_sum_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (c : X → Real) (F : X → Y → Real) :
    (∑ x : X, c x * ∑ y : Y, F x y) = ∑ y : Y, ∑ x : X, c x * F x y := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- A verifier sample contributes only at its two actual local questions. -/
def questionKernel (q0 : Q1) (s0 : Q2) (F : A → B → Real)
    (q : Q1) (s : Q2) (a : A) (b : B) : Real :=
  if q = q0 then if s = s0 then F a b else 0 else 0

theorem randomizedValue_questionKernel (μ : Q1 → FiniteLaw A)
    (ν : Q2 → FiniteLaw B) (q0 : Q1) (s0 : Q2) (F : A → B → Real) :
    randomizedValue μ ν (questionKernel q0 s0 F) =
      ∑ a : A, ((μ q0).mass a : Real) * ∑ b : B, ((ν s0).mass b : Real) * F a b := by
  simp [randomizedValue, questionKernel, mul_ite, Finset.sum_ite_irrel]

theorem deterministicValue_questionKernel (f : Q1 → A) (g : Q2 → B)
    (q0 : Q1) (s0 : Q2) (F : A → B → Real) :
    deterministicValue f g (questionKernel q0 s0 F) = F (f q0) (g s0) := by
  simp [deterministicValue, questionKernel, Finset.sum_ite_irrel]

/-- Finite linearity moves the hidden verifier sample outside the four
local question/answer sums, without exposing it to either strategy. -/
theorem randomizedValue_sum (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B)
    (K : W → Q1 → Q2 → A → B → Real) :
    randomizedValue μ ν (fun q s a b => ∑ w : W, K w q s a b) =
      ∑ w : W, randomizedValue μ ν (K w) := by
  have hs (q : Q1) (a : A) :
      (∑ s : Q2, ∑ b : B, ((ν s).mass b : Real) * ∑ w : W, K w q s a b) =
        ∑ w : W, ∑ s : Q2, ∑ b : B, ((ν s).mass b : Real) * K w q s a b := by
    calc
      _ = ∑ s : Q2, ∑ w : W, ∑ b : B, ((ν s).mass b : Real) * K w q s a b := by
        apply Finset.sum_congr rfl
        intro s _
        exact weighted_sum_comm (fun b => ((ν s).mass b : Real)) (fun b w => K w q s a b)
      _ = _ := Finset.sum_comm
  have ha (q : Q1) :
      (∑ a : A, ((μ q).mass a : Real) *
        ∑ s : Q2, ∑ b : B, ((ν s).mass b : Real) * ∑ w : W, K w q s a b) =
          ∑ w : W, ∑ a : A, ((μ q).mass a : Real) *
            ∑ s : Q2, ∑ b : B, ((ν s).mass b : Real) * K w q s a b := by
    simp_rw [hs]
    exact weighted_sum_comm (fun a => ((μ q).mass a : Real))
      (fun a w => ∑ s : Q2, ∑ b : B, ((ν s).mass b : Real) * K w q s a b)
  unfold randomizedValue
  simp_rw [ha]
  exact Finset.sum_comm

theorem deterministicValue_sum (f : Q1 → A) (g : Q2 → B)
    (K : W → Q1 → Q2 → A → B → Real) :
    deterministicValue f g (fun q s a b => ∑ w : W, K w q s a b) =
      ∑ w : W, deterministicValue f g (K w) := by
  unfold deterministicValue
  calc
    _ = ∑ q : Q1, ∑ w : W, ∑ s : Q2, K w q s (f q) (g s) := by
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem independent_product_event_real (μ : FiniteLaw A) (ν : FiniteLaw B)
    (R : A → B → Prop) :
    (eventMass (independentProduct μ ν) (Finset.univ.filter fun p => R p.1 p.2) : Real) =
      ∑ a : A, ∑ b : B, if R a b then (μ.mass a : Real) * (ν.mass b : Real) else 0 := by
  unfold eventMass
  rw [Finset.sum_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hR : R a b <;> simp [hR, independentProduct]

def verifierKernel (weight : W → Real) (first : W → Q1) (second : W → Q2)
    (accepts : W → A → B → Prop) (q : Q1) (s : Q2) (a : A) (b : B) : Real :=
  ∑ w : W, questionKernel (first w) (second w)
    (fun x y => weight w * (if accepts w x y then 1 else 0)) q s a b

def randomizedVerifierMean (weight : W → Real) (first : W → Q1) (second : W → Q2)
    (accepts : W → A → B → Prop) (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B) : Real :=
  ∑ w : W, weight w *
    (eventMass (independentProduct (μ (first w)) (ν (second w)))
      (Finset.univ.filter fun p => accepts w p.1 p.2) : Real)

def deterministicVerifierMean (weight : W → Real) (first : W → Q1) (second : W → Q2)
    (accepts : W → A → B → Prop) (f : Q1 → A) (g : Q2 → B) : Real :=
  ∑ w : W, weight w * (if accepts w (f (first w)) (g (second w)) then 1 else 0)

theorem randomizedValue_verifierKernel (weight : W → Real)
    (first : W → Q1) (second : W → Q2) (accepts : W → A → B → Prop)
    (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B) :
    randomizedValue μ ν (verifierKernel weight first second accepts) =
      randomizedVerifierMean weight first second accepts μ ν := by
  unfold verifierKernel randomizedVerifierMean
  rw [randomizedValue_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [randomizedValue_questionKernel, independent_product_event_real]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hR : accepts w a b <;> simp [hR] <;> ring

theorem deterministicValue_verifierKernel (weight : W → Real)
    (first : W → Q1) (second : W → Q2) (accepts : W → A → B → Prop)
    (f : Q1 → A) (g : Q2 → B) :
    deterministicValue f g (verifierKernel weight first second accepts) =
      deterministicVerifierMean weight first second accepts f g := by
  unfold verifierKernel deterministicVerifierMean
  rw [deterministicValue_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact deterministicValue_questionKernel f g _ _ _

theorem exists_deterministic_ge_verifier [Nonempty A] [Nonempty B]
    (weight : W → Real) (first : W → Q1) (second : W → Q2)
    (accepts : W → A → B → Prop) (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B) :
    ∃ f : Q1 → A, ∃ g : Q2 → B,
      randomizedVerifierMean weight first second accepts μ ν ≤
        deterministicVerifierMean weight first second accepts f g := by
  obtain ⟨f, g, h⟩ := exists_deterministic_ge_randomized μ ν
    (verifierKernel weight first second accepts)
  rw [randomizedValue_verifierKernel, deterministicValue_verifierKernel] at h
  exact ⟨f, g, h⟩

end FiniteVerifier

section OriginalOccurrenceVerifier

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)

/-- The complete hidden sample retains each occurrence's own advice. -/
abbrev OriginalVerifierSample (A m h : Nat) :=
  Σ u : Fin (blocks A h) → TaggedRow I copies,
    Σ d : Draw (blocks A h), Fin (numericRankThreshold m) →
      OccurrenceAdvice I copies (orderedVisibleBlock I copies u d)

abbrev OriginalFirstQuestion (A m h : Nat) :=
  (Fin (blocks A h) → TaggedRow I copies) ×
    (Fin (numericRankThreshold m) → TaggedAmbient I copies)

abbrev OriginalSecondQuestion (A m h : Nat) :=
  Finset (TaggedVar I copies) ×
    (Fin (numericRankThreshold m) → TaggedAmbient I copies)

def originalSampleWeight {A m h : Nat} (w : OriginalVerifierSample I copies A m h) : Real :=
  (iidOrderedMass I copies (blocks A h) w.1 : Real) * (prior (beta A h) w.2.1 : Real) *
    uniformArray w.2.2

def originalFirstQuestion {A m h : Nat} (w : OriginalVerifierSample I copies A m h) :
    OriginalFirstQuestion I copies A m h :=
  (w.1, fun i => sumRawVector I copies (fun j => (w.2.2 i j).val))

def originalSecondQuestion {A m h : Nat} (w : OriginalVerifierSample I copies A m h) :
    OriginalSecondQuestion I copies A m h :=
  (orderedVisibleUnion I copies w.1 w.2.1,
    fun i => sumRawVector I copies (fun j => (w.2.2 i j).val))

def originalSampleAccepts {A m h : Nat} (w : OriginalVerifierSample I copies A m h)
    (first second : TaggedAmbient I copies) : Prop :=
  orderedAssignmentAccepts I copies w.1 (orderedVisibleUnion I copies w.1 w.2.1) first second

def originalFirstLaw {A m h : Nat} (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h)
    (q : OriginalFirstQuestion I copies A m h) : FiniteLaw (TaggedAmbient I copies) :=
  if hu : GoodOrderedQuestion (taggedSource I copies).support q.1 then
    let U := orderedToGoodU I copies (blocks A h) ⟨q.1, hu⟩
    if hv : ∀ i, q.2 i ∈ OriginalSpace I copies U then
      originalLocalLaw I copies m a U T choice (fun i => ⟨q.2 i, hv i⟩)
    else dirac 0
  else dirac 0

def originalSecondLaw {A m h : Nat} (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat)
    (s : OriginalSecondQuestion I copies A m h) : FiniteLaw (TaggedAmbient I copies) :=
  if hv : ∀ i, s.2 i ∈ visibleCoordinateSpace I copies s.1 then
    visibleLocalLaw I copies m a T choice C s.1 (fun i => ⟨s.2 i, hv i⟩)
  else dirac 0

/-- This is the actual dependent finite verifier expansion, with the
original iid, deletion and full occurrence-array weights unchanged. -/
theorem original_verifier_randomized_mean {A m h : Nat}
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    randomizedVerifierMean (originalSampleWeight I copies (A := A) (m := m) (h := h))
      (originalFirstQuestion I copies) (originalSecondQuestion I copies)
      (originalSampleAccepts I copies) (originalFirstLaw I copies a T choice)
      (originalSecondLaw I copies a T choice C) =
        ∑ u : Fin (blocks A h) → TaggedRow I copies,
          (iidOrderedMass I copies (blocks A h) u : Real) *
            orderedQuestionScore I copies a T choice C u := by
  simp only [randomizedVerifierMean, Fintype.sum_sigma]
  unfold orderedQuestionScore
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro v _
  change (iidOrderedMass I copies (blocks A h) u : Real) *
      (prior (beta A h) d : Real) * uniformArray v *
      (orderedTupleScore I copies m a T choice C u d v : Real) =
    (iidOrderedMass I copies (blocks A h) u : Real) *
      ((prior (beta A h) d : Real) *
        (uniformArray v * (orderedTupleScore I copies m a T choice C u d v : Real)))
  ring

/-- Actual local deterministic global assignments dominate the constructed
raw iid strategy. This theorem has no assumed final success identity and
does not yet apply an external bound to its question domain. -/
theorem original_iid_local_derandomization {A m h : Nat}
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    ∃ f : OriginalFirstQuestion I copies A m h → TaggedAmbient I copies,
      ∃ g : OriginalSecondQuestion I copies A m h → TaggedAmbient I copies,
        (∑ u : Fin (blocks A h) → TaggedRow I copies,
          (iidOrderedMass I copies (blocks A h) u : Real) *
            orderedQuestionScore I copies a T choice C u) ≤
          deterministicVerifierMean (originalSampleWeight I copies)
            (originalFirstQuestion I copies) (originalSecondQuestion I copies)
            (originalSampleAccepts I copies) f g := by
  obtain ⟨f, g, hfg⟩ := exists_deterministic_ge_verifier
    (originalSampleWeight I copies (A := A) (m := m) (h := h))
    (originalFirstQuestion I copies) (originalSecondQuestion I copies)
    (originalSampleAccepts I copies) (originalFirstLaw I copies a T choice)
    (originalSecondLaw I copies a T choice C)
  rw [original_verifier_randomized_mean] at hfg
  exact ⟨f, g, hfg⟩

end OriginalOccurrenceVerifier
end
end PvNP.RealizableHardness.ActualVerifierAggregation
