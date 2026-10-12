import PvNP.RealizableHardness.ActualVisibleCountImport
import PvNP.RealizableHardness.ActualSelectedVisibleMatchBridge
import PvNP.RealizableHardness.ActualPrivateAssignmentLaw

/-! The literal selected event pays the uniform actual visible-list cost in
the concrete private assignment experiment. The canonical score is totalized
by zero off retained advice. Original supplied-vector and question-law
identification remain separate. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualCountedAssignmentScore

open ActualVisibleCountImport ActualMaximalCountSpecialization
open ActualSelectedVisibleMatchBridge ActualPrivateAssignmentLaw
open ActualVisibleActualMatch ActualVisibleAmbientLadder ActualVisibleListStrategy
open ActualVisibleOutputTransport ActualFunctionalAssignmentAcceptance
open ActualOriginalDecoderSelection ActualOriginalLawFullDecoderIntegration
open ActualFixedScoreVisibleApplication ActualFixedScoreConditionalAgreement
open ActualVisibleJointSuccess ActualCompletionEquationPullback
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedRowDeletion ActualVisibleQuestionCompletion ActualFiniteLaw
open ActualMaximalPairLadder ActualNumericRobustReal ActualNumericSourceHeight
open ActualNumericExplicitHeight ActualCmmsaParameterReconciliation
open SamplerParameters GrassmannCounting GrassmannIncidence TripleRestrictionRank

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- The containment transport needed to define the actual score on every
retained-advice branch, independently of any favorable event. -/
theorem original_advice_containment {J a : Nat}
    (U : TaggedGoodU I copies J) (Q : Advice J a) (s : Draw J)
    (hQ : Q.val ≤ retained s) :
    ((actualRowGrassEquiv I copies U a).symm Q).val ≤
      actualRetained I copies U ((rowDrawEquiv I copies U).symm s) := by
  let e := actualRowCoordinateEquiv I copies U
  let Qact := (actualRowGrassEquiv I copies U a).symm Q
  have hframe : actualRowGrassEquiv I copies U a Qact = Q :=
    (actualRowGrassEquiv I copies U a).apply_symm_apply Q
  intro x hx
  have hxe : e x ∈ Q.val := by
    rw [← hframe]
    exact ⟨x, hx, rfl⟩
  have hmap : e x ∈
      (actualRetained I copies U ((rowDrawEquiv I copies U).symm s)).map e.toLinearMap := by
    rw [actualRetained_map_coordinates]
    simpa using hQ hxe
  rcases hmap with ⟨y, hy, hxy⟩
  exact e.injective hxy ▸ hy

/-- The actual conditional assignment score for the same selected original
pair and the visible-question-only second law. -/
def selectedAssignmentMass {J h a : Nat} (m : Nat)
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U) (Q : Grass (OriginalSpace I copies U) a)
    (hQV : Q.val ≤ actualRetained I copies U s) : Rat :=
  let P := selectedPair I copies U (refreshThreshold m h) (numericRankThreshold m) T choice Q
  let X := retainedVariables I copies J U s
  let Qvis := pushGrass (retainedVisibleEquiv I copies J U s)
    (retainedPreimageGrass I copies J U s Q hQV)
  eventMass (assignmentPairLaw I copies U P.W P.g X
    (visibleQuestionOutputLaw I copies T choice (numericRankThreshold m) C X Qvis))
    (assignmentAcceptanceEvent I copies U X)

theorem selected_assignment_mass_bounds {J h a : Nat} (m : Nat)
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U) (Q : Grass (OriginalSpace I copies U) a)
    (hQV : Q.val ≤ actualRetained I copies U s) :
    0 ≤ selectedAssignmentMass I copies m U T choice C s Q hQV ∧
      selectedAssignmentMass I copies m U T choice C s Q hQV ≤ 1 := by
  exact assignment_acceptance_mass_bounds I copies U _ _ _ _

/-- Literal favorable-pair identity for the actual second law used above. -/
theorem selected_assignment_mass_eq_matching {J h a : Nat} (m : Nat)
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U) (Q : Grass (OriginalSpace I copies U) a)
    (hQV : Q.val ≤ actualRetained I copies U s)
    (hfav : actualFullDecoderFavorable I copies U (refreshThreshold m h)
      (numericRankThreshold m) T choice Q) :
    let P := selectedPair I copies U (refreshThreshold m h) (numericRankThreshold m) T choice Q
    let Qvis := pushGrass (retainedVisibleEquiv I copies J U s)
      (retainedPreimageGrass I copies J U s Q hQV)
    selectedAssignmentMass I copies m U T choice C s Q hQV =
      extensionMatchProbability P.W (actualRetained I copies U s) P.g
        (pushforward (fun f => f.comp (retainedVisibleEquiv I copies J U s).toLinearMap)
          (visibleOutputLaw (actualVisibleAmbientTable I copies J U T choice s)
            Qvis (numericRankThreshold m) C)) := by
  exact favorable_private_assignment_mass_eq_matching I copies U
    (refreshThreshold m h) (numericRankThreshold m) T choice Q hfav s _

/-- The canonical analysis score, zero outside retained advice. This does not
claim that an invalid supplied prefix is resampled or conditioned away. -/
def canonicalAssignmentScore {J h a : Nat} (m : Nat)
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (Q : Advice J a) (s : Draw J) : Real :=
  if hQ : Q.val ≤ retained s then
    (selectedAssignmentMass I copies m U T choice C
      ((rowDrawEquiv I copies U).symm s) ((actualRowGrassEquiv I copies U a).symm Q)
      (original_advice_containment I copies U Q s hQ) : Real)
  else 0

theorem canonical_assignment_score_bounds {J h a : Nat} (m : Nat)
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (Q : Advice J a) (s : Draw J) :
    0 ≤ canonicalAssignmentScore I copies m U T choice C Q s ∧
      canonicalAssignmentScore I copies m U T choice C Q s ≤ 1 := by
  by_cases hQ : Q.val ≤ retained s
  · simp only [canonicalAssignmentScore, dif_pos hQ]
    exact_mod_cast selected_assignment_mass_bounds I copies m U T choice C
      ((rowDrawEquiv I copies U).symm s) ((actualRowGrassEquiv I copies U a).symm Q)
      (original_advice_containment I copies U Q s hQ)
  · simp [canonicalAssignmentScore, hQ]

def countedAssignmentCost (m h : Nat) : Real :=
  1 / ((countConstant m : Real) * (2 : Real) ^ (countExponent m * h) *
    ((numericRankThreshold m : Real) + 1) * (2 : Real) ^ numericRankThreshold m)

theorem countedAssignmentCost_nonneg (m h : Nat) : 0 ≤ countedAssignmentCost m h := by
  unfold countedAssignmentCost
  positivity

private theorem count_cost_le_matching_factor {n m h : Nat} (hn : 0 < n)
    (hcount : (n : Real) ≤ (countConstant m : Real) * (2 : Real) ^ (countExponent m * h)) :
    countedAssignmentCost m h ≤
      (((1 / (n : Rat)) / (numericRankThreshold m + 1)) *
        (1 / (2 : Rat) ^ numericRankThreshold m) : Rat) := by
  let M : Real := (countConstant m : Real) * (2 : Real) ^ (countExponent m * h)
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hdiv : 1 / M ≤ 1 / (n : Real) :=
    div_le_div_of_nonneg_left (by norm_num) hnR hcount
  have hp := mul_le_mul_of_nonneg_right hdiv
    (show (0 : Real) ≤ (1 / ((numericRankThreshold m : Real) + 1)) *
      (1 / (2 : Real) ^ numericRankThreshold m) by positivity)
  have hid : countedAssignmentCost m h = (1 / M) *
      ((1 / ((numericRankThreshold m : Real) + 1)) *
        (1 / (2 : Real) ^ numericRankThreshold m)) := by
    simp only [countedAssignmentCost, M, one_div, mul_inv_rev] <;> ring
  have hcast :
      ((((1 / (n : Rat)) / (numericRankThreshold m + 1)) *
        (1 / (2 : Rat) ^ numericRankThreshold m) : Rat) : Real) =
      (1 / (n : Real)) * ((1 / ((numericRankThreshold m : Real) + 1)) *
        (1 / (2 : Real) ^ numericRankThreshold m)) := by
    push_cast <;> ring
  rw [hid, hcast]
  exact hp

/-- The successful event used by the full-vector theorem implies the same
uniform conditional assignment cost on every actual original question. -/
theorem literal_event_counted_assignment_lower
    {A m h a sourceCutoff : Nat}
    (U : TaggedGoodU I copies (blocks A h))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h)
    (Q : Advice (blocks A h) a) (s : Draw (blocks A h))
    (hCount : DeclaredMaximalCountContract m sourceCutoff)
    (hm : 256 ≤ m) (hA : 1 ≤ A) (ha : a ≤ numericRankThreshold m)
    (hsource : sourceCutoff ≤ h) (hnum : numericHnum m ≤ h)
    (hguards : max 200 (bOf m ^ 2 * (3 * numericRankThreshold m + 5)) ≤ h)
    (C : Rat) (hC : 0 < C)
    (hthreshold : refreshThreshold m h / 5 < (C : Real))
    (hEvent :
      goodFavorable (A := A) (h := h) (a := a)
        (selectedCoordinateFavorable I copies U (refreshThreshold m h)
          (numericRankThreshold m) T choice)
        (completionPulledBack I copies U) Q &&
      visibleEvent (A := A) (h := h) (a := a) Q
        (selectedCoordinateWindow I copies U (refreshThreshold m h)
          (numericRankThreshold m) T choice Q)
        (completionPulledBack I copies U)
        (selectedVisibleAgreementScore I copies U (refreshThreshold m h)
          (numericRankThreshold m) T choice Q) C s = true) :
    countedAssignmentCost m h ≤ canonicalAssignmentScore I copies m U T choice C Q s := by
  obtain ⟨hQ, hQV, j, hcard, hmass, _hassign⟩ :=
    selected_visible_event_actual_matching_and_assignments I copies U
      (refreshThreshold m h) T choice Q s C hC hEvent
  let Qact := (actualRowGrassEquiv I copies U a).symm Q
  let sact := (rowDrawEquiv I copies U).symm s
  let Qvis := pushGrass (retainedVisibleEquiv I copies (blocks A h) U sact)
    (retainedPreimageGrass I copies (blocks A h) U sact Qact hQV)
  have hgood := (goodFavorable_eq_true (A := A) (h := h) (a := a)
    (selectedCoordinateFavorable I copies U (refreshThreshold m h)
      (numericRankThreshold m) T choice)
    (completionPulledBack I copies U) Q).mp (Bool.and_eq_true.mp hEvent).1
  have hdec : decide (Qact.val ⊓ OriginalH I copies U = ⊥ ∧
      actualFullDecoderFavorable I copies U (refreshThreshold m h)
        (numericRankThreshold m) T choice Qact) = true := by
    simpa [selectedCoordinateFavorable, ActualOriginalDecoderSelection.favorable, Qact]
      using hgood.1
  have hfav := (of_decide_eq_true hdec).2
  have hlist := actual_visible_lists_uniform_count I copies U T choice sact Qvis
    hCount hm hA ha hsource hnum hguards C hC hthreshold j.val (Nat.le_of_lt_succ j.isLt)
  have hcost := count_cost_le_matching_factor hcard hlist
  have hid := selected_assignment_mass_eq_matching I copies m U T choice C sact Qact hQV hfav
  calc
    countedAssignmentCost m h ≤
        (selectedAssignmentMass I copies m U T choice C sact Qact hQV : Real) := by
      rw [hid]
      exact hcost.trans (by exact_mod_cast hmass)
    _ = canonicalAssignmentScore I copies m U T choice C Q s := by
      simp only [canonicalAssignmentScore, dif_pos hQ]

end
end PvNP.RealizableHardness.ActualCountedAssignmentScore
