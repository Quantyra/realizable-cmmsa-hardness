import PvNP.RealizableHardness.ActualSharedAdviceSpans
import PvNP.RealizableHardness.ActualPrivateAssignmentLaw

/-! Two local normalized assignment strategies on the actual received
vectors, with independent private randomness and fixed fallbacks. The full
original iid-row source-game identification is still separate.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualLocalAssignmentStrategies

open scoped BigOperators
open ActualSharedAdviceSpans ActualPrivateAssignmentLaw ActualCountedAssignmentScore
open ActualFullAdvicePrefix ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance
open ActualOriginalDecoderSelection ActualRandomExtensionSuccess
open ActualTaggedRowDeletion ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualVisibleQuestionCompletion ActualFiniteLaw ActualNumericSourceHeight
open ActualNumericRobustReal ActualMaximalPairLadder VectorAdvice GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

/-- Independent private laws commute with separate local output maps. -/
theorem independent_product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω → A) (g : Γ → B) :
    pushforward (fun p : Ω × Γ => (f p.1, g p.2)) (independentProduct μ ν) =
      independentProduct (pushforward f μ) (pushforward g ν) := by
  apply FiniteLaw.ext
  rintro ⟨a, b⟩
  simp only [pushforward_apply, independentProduct]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : f x = a <;> by_cases hg : g y = b <;> simp [hf, hg]

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- The first strategy takes only its original question and its full received
vector tuple; the global table, choice and dimension were fixed beforehand. -/
def originalLocalLaw {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (v : Fin (numericRankThreshold m) → OriginalSpace I copies U) :
    FiniteLaw (TaggedAmbient I copies) :=
  match output (advicePrefix (Nat.le_of_lt_succ a.isLt) v) with
  | none => dirac 0
  | some Q =>
    let P := selectedPair I copies U (refreshThreshold m h) (numericRankThreshold m) T choice Q
    pushforward (fun G : ActualStarAffineFunctionalSelection.FunctionalExtensionFiber P.W P.g =>
      originalAssignment I copies U G.1) (ambientExtensionLaw P.W P.g)

/-- The second strategy takes only its visible set and its full received
visible vector tuple. In particular, it has no original-U argument. -/
def visibleLocalLaw {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (X : Finset (TaggedVar I copies))
    (v : Fin (numericRankThreshold m) → visibleCoordinateSpace I copies X) :
    FiniteLaw (TaggedAmbient I copies) :=
  match output (advicePrefix (Nat.le_of_lt_succ a.isLt) v) with
  | none => dirac 0
  | some Q => pushforward (visibleAssignment I copies X)
      (visibleQuestionOutputLaw I copies T choice (numericRankThreshold m) C X Q)

/-- Literal acceptance of the two separately constructed local assignment
laws on the same retained supplied tuple. -/
def localAssignmentScore {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U)
    (v : Fin (numericRankThreshold m) → actualRetained I copies U s) : Rat :=
  eventMass (independentProduct
    (originalLocalLaw I copies m a U T choice (fun i => (v i).val))
    (visibleLocalLaw I copies m a T choice C (retainedVariables I copies J U s)
      (fun i => retainedVisibleEquiv I copies J U s (v i))))
    (assignmentAcceptanceEvent I copies U (retainedVariables I copies J U s))

theorem local_assignment_score_nonneg {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U)
    (v : Fin (numericRankThreshold m) → actualRetained I copies U s) :
    0 ≤ localAssignmentScore I copies m a U T choice C s v := by
  unfold localAssignmentScore eventMass
  exact Finset.sum_nonneg (fun p _ => (independentProduct _ _).nonneg p)

/-- A successful first prefix identifies the exact actual conditional
assignment probability, using the same original selected pair. -/
theorem local_assignment_score_of_prefix {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U)
    (v : Fin (numericRankThreshold m) → actualRetained I copies U s)
    (Q : Grass (OriginalSpace I copies U) a.val)
    (hQ : output (fun i => (advicePrefix (Nat.le_of_lt_succ a.isLt) v i).val) = some Q) :
    ∃ hQV : Q.val ≤ actualRetained I copies U s,
      localAssignmentScore I copies m a U T choice C s v =
        selectedAssignmentMass I copies m U T choice C s Q hQV := by
  obtain ⟨hQV, hvis⟩ := original_visible_prefix_some I copies
    (Nat.le_of_lt_succ a.isLt) U s v Q hQ
  refine ⟨hQV, ?_⟩
  unfold localAssignmentScore originalLocalLaw visibleLocalLaw
  change eventMass (independentProduct
    ((output (fun i => (advicePrefix (Nat.le_of_lt_succ a.isLt) v i).val)).elim
      (dirac 0) (fun Q =>
        let P := selectedPair I copies U (refreshThreshold m h) (numericRankThreshold m) T choice Q
        pushforward (fun G : ActualStarAffineFunctionalSelection.FunctionalExtensionFiber P.W P.g =>
          originalAssignment I copies U G.1) (ambientExtensionLaw P.W P.g)))
    ((output (fun i => retainedVisibleEquiv I copies J U s
        (advicePrefix (Nat.le_of_lt_succ a.isLt) v i))).elim
      (dirac 0) (fun Q => pushforward
        (visibleAssignment I copies (retainedVariables I copies J U s))
        (visibleQuestionOutputLaw I copies T choice (numericRankThreshold m) C
          (retainedVariables I copies J U s) Q))))
    (assignmentAcceptanceEvent I copies U (retainedVariables I copies J U s)) = _
  rw [hQ, hvis]
  dsimp only [Option.elim]
  rw [← independent_product_pushforward]
  rfl

/-- Analysis totalization in original coordinates; neither local prover
uses this draw-dependent containment test. -/
def originalTupleAnalysisScore {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U)
    (v : Fin (numericRankThreshold m) → actualRetained I copies U s) : Rat :=
  (output (fun i => (advicePrefix (Nat.le_of_lt_succ a.isLt) v i).val)).elim 0
    (fun Q => if hQV : Q.val ≤ actualRetained I copies U s then
      selectedAssignmentMass I copies m U T choice C s Q hQV else 0)

/-- Dependence is scored zero only in analysis; the actual normalized
fallback strategy remains in the experiment and has nonnegative acceptance. -/
theorem original_tuple_analysis_le_local {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U)
    (v : Fin (numericRankThreshold m) → actualRetained I copies U s) :
    originalTupleAnalysisScore I copies m a U T choice C s v ≤
      localAssignmentScore I copies m a U T choice C s v := by
  cases hQ : output (fun i => (advicePrefix (Nat.le_of_lt_succ a.isLt) v i).val) with
  | none =>
    simpa [originalTupleAnalysisScore, hQ] using
      local_assignment_score_nonneg I copies m a U T choice C s v
  | some Q =>
    obtain ⟨hQV, heq⟩ := local_assignment_score_of_prefix I copies m a U T choice C s v Q hQ
    simp only [originalTupleAnalysisScore, hQ, Option.elim, dif_pos hQV]
    exact heq.ge

end
end PvNP.RealizableHardness.ActualLocalAssignmentStrategies
