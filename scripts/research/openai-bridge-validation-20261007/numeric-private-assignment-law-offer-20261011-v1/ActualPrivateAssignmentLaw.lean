import PvNP.RealizableHardness.ActualVisibleActualMatch
import PvNP.RealizableHardness.ActualVisibleOutputTransport
import PvNP.RealizableHardness.ActualVisibleAmbientLadder
import PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance
import PvNP.RealizableHardness.ActualOriginalDecoderSelection
import PvNP.RealizableHardness.ActualFiniteLaw

/-! The independent private-output experiment and its literal assignment test.
The second output table is factored through its visible question. The exact
conditional law is not yet the complete original source-game law.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualPrivateAssignmentLaw

open scoped BigOperators
open ActualFiniteLaw ActualMaximalPairLadder ActualStarAffineFunctionalSelection
open ActualRandomExtensionSuccess ActualVisibleListStrategy ActualVisibleOutputTransport
open ActualVisibleActualMatch ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance
open ActualOriginalDecoderSelection ActualOccurrenceAllocation ActualTaggedConcreteStarLaw
open ActualTaggedFixedCenterGeometry ActualTaggedRowDeletion ActualVisibleQuestionCompletion
open ActualVisibleLeafAgreementLoss GrassmannCounting
open ActualOriginalLawFullDecoderIntegration

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

/-- The two provers' private choices are independent after fixing questions
and supplied advice. -/
def independentProduct {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  mass p := μ.mass p.1 * ν.mass p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ν.normalized, mul_one, μ.normalized]

/-- Exact finite disintegration of the independent private-output event. -/
theorem independent_product_event_mass
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (R : Ω → Γ → Prop) :
    eventMass (independentProduct μ ν) (Finset.univ.filter fun p => R p.1 p.2) =
      ∑ y, ν.mass y * eventMass μ (Finset.univ.filter fun x => R x y) := by
  simp only [eventMass, Finset.sum_filter, independentProduct]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hR : R x y <;> simp [hR, mul_comm]

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- A table on the second prover's visible question, with no original-U input. -/
def visibleQuestionTable {J h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies)) :
    (L : Grass (visibleCoordinateSpace I copies X) (2 * h)) →
      Module.Dual (ZMod 2) L.val := by
  intro L
  exact (visibleLeafTable I copies J T choice X
      (L.val.map (visibleCoordinateSpace I copies X).subtype)).comp
    (((visibleCoordinateSpace I copies X).subtype.comp L.val.subtype).codRestrict
      (L.val.map (visibleCoordinateSpace I copies X).subtype)
      (fun x => ⟨x.1, x.2, rfl⟩))

/-- The actual geometry wrapper uses U and s only through the visible set X. -/
theorem actual_visible_table_depends_only_on_question {J h : Nat}
    (U : TaggedGoodU I copies J)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U) :
    actualVisibleAmbientTable I copies J U T choice s =
      visibleQuestionTable I copies T choice (retainedVariables I copies J U s) := rfl

/-- The total second-prover law uses only its visible set and supplied advice
span, together with parameters and the globally fixed table. -/
def visibleQuestionOutputLaw {J h a : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (r : Nat) (C : Rat) (X : Finset (TaggedVar I copies))
    (Q : Grass (visibleCoordinateSpace I copies X) a) :
    FiniteLaw (Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X)) :=
  visibleOutputLaw (visibleQuestionTable I copies T choice X) Q r C

/-- The literal two-part assignment test: original equations and retained
coordinate agreement. Totalized values outside each question are irrelevant. -/
def assignmentAccepts {J : Nat} (U : TaggedGoodU I copies J)
    (X : Finset (TaggedVar I copies)) (first second : TaggedAmbient I copies) : Prop :=
  (∀ row (hrow : row ∈ U.1),
    first ((taggedSource I copies).row row 0) +
      first ((taggedSource I copies).row row 1) +
      first ((taggedSource I copies).row row 2) = (taggedSource I copies).rhs row) ∧
    ∀ x, x ∈ X → first x = second x

def assignmentAcceptanceEvent {J : Nat} (U : TaggedGoodU I copies J)
    (X : Finset (TaggedVar I copies)) :
    Finset (TaggedAmbient I copies × TaggedAmbient I copies) :=
  Finset.univ.filter fun p => assignmentAccepts I copies U X p.1 p.2

/-- Push the independent original-extension and visible-output choices to
their actual assignments. The first choice takes U,W,g but no retained draw. -/
def assignmentPairLaw {J : Nat} (U : TaggedGoodU I copies J)
    (W : Submodule (ZMod 2) (OriginalSpace I copies U))
    (g : Module.Dual (ZMod 2) W) (X : Finset (TaggedVar I copies))
    (ν : FiniteLaw (Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X))) :
    FiniteLaw (TaggedAmbient I copies × TaggedAmbient I copies) :=
  pushforward
    (fun p : FunctionalExtensionFiber W g ×
        Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X) =>
      (originalAssignment I copies U p.1.1, visibleAssignment I copies X p.2))
    (independentProduct (ambientExtensionLaw W g) ν)

/-- The literal conditional score is bounded on every question, including
those outside the favorable event. -/
theorem assignment_acceptance_mass_bounds {J : Nat} (U : TaggedGoodU I copies J)
    (W : Submodule (ZMod 2) (OriginalSpace I copies U))
    (g : Module.Dual (ZMod 2) W) (X : Finset (TaggedVar I copies))
    (ν : FiniteLaw (Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X))) :
    0 ≤ eventMass (assignmentPairLaw I copies U W g X ν)
        (assignmentAcceptanceEvent I copies U X) ∧
      eventMass (assignmentPairLaw I copies U W g X ν)
        (assignmentAcceptanceEvent I copies U X) ≤ 1 := by
  let μ := assignmentPairLaw I copies U W g X ν
  constructor
  · exact Finset.sum_nonneg (fun p _ => μ.nonneg p)
  · calc
      _ ≤ ∑ p, μ.mass p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro p _ _
        exact μ.nonneg p
      _ = 1 := μ.normalized

/-- For the same favorable selected pair, the literal assignment-acceptance
mass equals the complete functional matching mass. Every matching output is
included; compatibility with a ladder witness is not an extra condition. -/
theorem favorable_private_assignment_mass_eq_matching {J h a : Nat}
    (U : TaggedGoodU I copies J) (e : Real) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (OriginalSpace I copies U) a)
    (hfav : actualFullDecoderFavorable I copies U e r T choice Q)
    (s : ActualRowDraw I copies U)
    (ν : FiniteLaw (Module.Dual (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s)))) :
    let P := selectedPair I copies U e r T choice Q
    let X := retainedVariables I copies J U s
    eventMass (assignmentPairLaw I copies U P.W P.g X ν)
        (assignmentAcceptanceEvent I copies U X) =
      extensionMatchProbability P.W (actualRetained I copies U s) P.g
        (pushforward (fun f => f.comp (actualRetainedToVisible I copies U s)) ν) := by
  let P := selectedPair I copies U e r T choice Q
  let X := retainedVariables I copies J U s
  change eventMass (assignmentPairLaw I copies U P.W P.g X ν)
      (assignmentAcceptanceEvent I copies U X) = _
  unfold assignmentPairLaw
  rw [eventMass_pushforward]
  have hpre :
      preimageEvent
        (fun p : FunctionalExtensionFiber P.W P.g ×
            Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X) =>
          (originalAssignment I copies U p.1.1, visibleAssignment I copies X p.2))
        (assignmentAcceptanceEvent I copies U X) =
      Finset.univ.filter (fun p : FunctionalExtensionFiber P.W P.g ×
          Module.Dual (ZMod 2) (visibleCoordinateSpace I copies X) =>
        p.1.1.comp (actualRetained I copies U s).subtype =
          p.2.comp (actualRetainedToVisible I copies U s)) := by
    ext p
    simp only [preimageEvent, assignmentAcceptanceEvent, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hp
      exact (original_visible_assignment_agreement_iff I copies U s p.1.1 p.2).mpr hp.2
    · intro hp
      exact ⟨selected_pair_equation_acceptance I copies U e r T choice Q hfav p.1,
        (original_visible_assignment_agreement_iff I copies U s p.1.1 p.2).mp hp⟩
  rw [hpre, independent_product_event_mass (ambientExtensionLaw P.W P.g) ν
    (fun G f => G.1.comp (actualRetained I copies U s).subtype =
      f.comp (actualRetainedToVisible I copies U s)), extensionMatchProbability_pushforward]
  rfl

end
end PvNP.RealizableHardness.ActualPrivateAssignmentLaw
