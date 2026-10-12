import PvNP.RealizableHardness.ActualFixedScoreVisibleApplication
import PvNP.RealizableHardness.ActualVisibleActualMatch
import PvNP.RealizableHardness.ActualVisibleAmbientLadder
import PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance
import PvNP.RealizableHardness.ActualOriginalDecoderSelection
import PvNP.RealizableHardness.ActualRestrictedVisiblePair
import PvNP.RealizableHardness.ActualTaggedRowDeletion
import PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss
import PvNP.RealizableHardness.ActualVisibleJointSuccess
import PvNP.RealizableHardness.ActualVisibleListStrategy
import PvNP.RealizableHardness.ActualRandomExtensionSuccess
import PvNP.RealizableHardness.ActualFiniteLaw

/-! Bind the literal selected visible event to the same actual decoder pair,
its actual matching output law, and the pointwise retained-assignment/equation
bridge. This is not yet a source-game law identification. -/
namespace PvNP.RealizableHardness.ActualSelectedVisibleMatchBridge

open PvNP.RealizableHardness
open ActualFixedScoreVisibleApplication ActualVisibleActualMatch
open ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance
open ActualOriginalDecoderSelection ActualRestrictedVisiblePair
open ActualTaggedRowDeletion ActualVisibleLeafAgreementLoss
open ActualVisibleJointSuccess ActualVisibleListStrategy
open ActualRandomExtensionSuccess ActualFiniteLaw ActualMaximalPairLadder
open GrassmannCounting TripleRestrictionRank
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

private theorem agreement_transport_advice
    {Ambient : Type*} [AddCommGroup Ambient] [Module (ZMod 2) Ambient]
    [Fintype Ambient] {a d : Nat}
    (T : (L : Grass Ambient d) → Module.Dual (ZMod 2) L.val)
    {Q Q' : Grass Ambient a} (hQQ' : Q = Q')
    (P : DecodedPair Q d) :
    agreement T Q P = agreement T Q' (hQQ' ▸ P) := by
  cases hQQ'
  rfl

/-- If the literal visible event holds for the globally selected coordinates,
then the matching bound applies to the same selected pair; every matched
extension realizes the visible assignment on retained coordinates and the
original tagged equations. No pair or dimension is reselected after the draw. -/
theorem selected_visible_event_actual_matching_and_assignments
    {N rows A h a r : Nat}
    (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
    (U : TaggedGoodU I copies (blocks A h))
    (e : Real) (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h)
    (Q : Advice (blocks A h) a) (s : Draw (blocks A h))
    (C : Rat) (hC : 0 < C)
    (hEvent :
      goodFavorable (A := A) (h := h) (a := a)
        (selectedCoordinateFavorable I copies U e r T choice)
        (completionPulledBack I copies U) Q &&
      visibleEvent (A := A) (h := h) (a := a)
        Q (selectedCoordinateWindow I copies U e r T choice Q)
        (completionPulledBack I copies U)
        (selectedVisibleAgreementScore I copies U e r T choice Q)
        C s = true) :
    ∃ hQ : Q.val ≤ retained s,
    let Qact := (actualRowGrassEquiv I copies U a).symm Q
    let sact := (rowDrawEquiv I copies U).symm s
    ∃ hQVact : Qact.val ≤ actualRetained I copies U sact,
    let P := ActualOriginalDecoderSelection.selectedPair I copies U e r T choice Qact
    let X := retainedVariables I copies (blocks A h) U sact
    let Qvis := pushGrass (retainedVisibleEquiv I copies (blocks A h) U sact)
      (retainedPreimageGrass I copies (blocks A h) U sact Qact hQVact)
    let Pvis := actualVisibleRestrictedPair I copies (blocks A h) U sact Qact P hQVact
    let Tvis := actualVisibleAmbientTable I copies (blocks A h) U T choice sact
    ∃ j : Fin (r + 1),
      0 < (maximalPairList Tvis Qvis r (C / (4 * 5 ^ j.val))).card ∧
      ((1 / (maximalPairList Tvis Qvis r (C / (4 * 5 ^ j.val))).card) / (r + 1)) *
          (1 / (2 : Rat) ^ r) ≤
        extensionMatchProbability P.W (actualRetained I copies U sact) P.g
          (pushforward (fun f => f.comp
            (retainedVisibleEquiv I copies (blocks A h) U sact).toLinearMap)
            (visibleOutputLaw Tvis Qvis r C)) ∧
      (∀ f, f ∈ compatibleOutputEvent Pvis →
        ∀ G : FunctionalExtensionFiber P.W P.g,
          G.1.comp (actualRetained I copies U sact).subtype =
            f.comp (retainedVisibleEquiv I copies (blocks A h) U sact).toLinearMap →
          (∀ x, x ∈ X →
            originalAssignment I copies U G.1 x =
              visibleAssignment I copies X f x) ∧
          ∀ row (hrow : row ∈ U.1),
            originalAssignment I copies U G.1 ((taggedSource I copies).row row 0) +
              originalAssignment I copies U G.1 ((taggedSource I copies).row row 1) +
              originalAssignment I copies U G.1 ((taggedSource I copies).row row 2) =
                (taggedSource I copies).rhs row) := by
  classical
  have hGoodTrue := (Bool.and_eq_true.mp hEvent).1
  have hVisibleTrue := (Bool.and_eq_true.mp hEvent).2
  have hVisibleParts :
      !(excluded Q (selectedCoordinateWindow I copies U e r T choice Q)
          (completionPulledBack I copies U) s) &&
        decide (C / 4 ≤
          selectedVisibleAgreementScore I copies U e r T choice Q s) = true := by
    simpa [visibleEvent] using hVisibleTrue
  have hscoreBool : decide (C / 4 ≤
      selectedVisibleAgreementScore I copies U e r T choice Q s) = true :=
    (Bool.and_eq_true.mp hVisibleParts).2
  have hscore : C / 4 ≤
      selectedVisibleAgreementScore I copies U e r T choice Q s :=
    of_decide_eq_true hscoreBool
  have hQ : Q.val ≤ retained s := by
    by_contra hn
    have hzero : selectedVisibleAgreementScore I copies U e r T choice Q s = 0 := by
      simp [selectedVisibleAgreementScore, hn]
    rw [hzero] at hscore
    have hpositive : (0 : Rat) < C / 4 := by positivity
    linarith

  let Qact := (actualRowGrassEquiv I copies U a).symm Q
  let sact := (rowDrawEquiv I copies U).symm s
  have hQframe : actualRowGrassEquiv I copies U a Qact = Q :=
    (actualRowGrassEquiv I copies U a).apply_symm_apply Q
  have hQVact : Qact.val ≤ actualRetained I copies U sact := by
    intro x hx
    let eCoord := actualRowCoordinateEquiv I copies U
    have hxe : eCoord x ∈ Q.val := by
      rw [← hQframe]
      exact ⟨x, hx, rfl⟩
    have hsact : rowDrawEquiv I copies U sact = s :=`r`n      (rowDrawEquiv I copies U).apply_symm_apply s`r`n    have hmap : eCoord x ∈`r`n        (actualRetained I copies U sact).map eCoord.toLinearMap := by`r`n      rw [actualRetained_map_coordinates I copies U sact]`r`n      simpa [hsact] using hQ hxe
    rcases hmap with ⟨y, hy, hxy⟩
    exact eCoord.injective hxy ▸ hy

  have hgood := (goodFavorable_eq_true
    (selectedCoordinateFavorable I copies U e r T choice)
    (completionPulledBack I copies U) Q).mp hGoodTrue
  have hfavorableSelected :
      ActualOriginalDecoderSelection.favorable I copies U e r T choice Qact = true := by
    simpa [selectedCoordinateFavorable, Qact] using hgood.1
  have hfavProp :
      Qact.val ⊓ OriginalH I copies U = ⊥ ∧
        actualFullDecoderFavorable I copies U e r T choice Qact := by
    have hdec : decide
        (Qact.val ⊓ OriginalH I copies U = ⊥ ∧
          actualFullDecoderFavorable I copies U e r T choice Qact) = true := by
      simpa [ActualOriginalDecoderSelection.favorable] using hfavorableSelected
    exact of_decide_eq_true hdec
  have hfav : actualFullDecoderFavorable I copies U e r T choice Qact := hfavProp.2
  let P := ActualOriginalDecoderSelection.selectedPair I copies U e r T choice Qact
  have hselected := ActualOriginalDecoderSelection.selectedPair_properties
    I copies U e r T choice Qact hfav
  have hthreshold : C / 4 ≤ agreement
      (visibleTableInOriginalCoordinates I copies U T choice
        (retainedVariables I copies (blocks A h) U sact)) Qact
      (ActualRestrictedVisiblePair.restrictedPair I copies U Qact P sact hQVact) := by
    let X := retainedVariables I copies (blocks A h) U sact
    let P := ActualOriginalDecoderSelection.selectedPair I copies U e r T choice Qact
    let PRestr := ActualRestrictedVisiblePair.restrictedPair I copies U Qact P sact hQVact
    have hPair : selectedVisibleRestrictedPair I copies U e r T choice Q s hQ =
        (hQframe ▸ actualRowCoordinatePair I copies U Qact PRestr) := by
      rfl
    have hscoreEq : selectedVisibleAgreementScore I copies U e r T choice Q s =
        agreement
          (visibleTableInOriginalCoordinates I copies U T choice X)
          Qact PRestr := by
      rw [selectedVisibleAgreementScore, dif_pos hQ]
      rw [hPair]
      rw [← agreement_transport_advice
        (actualRowCoordinateTable I copies U
          (visibleTableInOriginalCoordinates I copies U T choice X))
        hQframe (actualRowCoordinatePair I copies U Qact PRestr)]
      exact (ActualFixedScoreConditionalAgreement.actualRowAgreement_eq
        I copies U Qact PRestr
        (visibleTableInOriginalCoordinates I copies U T choice X)).symm
    rw [← hscoreEq]
    exact hscore

  have hmatching := ActualVisibleActualMatch.actual_visible_matching_bound
    (I := I) (copies := copies) (U := U) T choice sact Qact P hQVact
    hselected.1 C hC hthreshold
  rcases hmatching with ⟨j, hcard, hmass⟩
  refine ⟨hQ, hQVact, j, hcard, hmass, ?_⟩
  intro f hf G hmatch
  have hmatch' : G.1.comp (actualRetained I copies U sact).subtype =
      f.comp (actualRetainedToVisible I copies U sact) := by
    simpa [retainedVisibleEquiv] using hmatch
  have hassign := (original_visible_assignment_agreement_iff
    I copies U sact G.1 f).mp hmatch'
  have hequations := ActualVisibleActualMatch.selected_pair_equation_acceptance
    I copies U e r T choice Qact hfav G
  exact ⟨hassign, hequations⟩

end
end PvNP.RealizableHardness.ActualSelectedVisibleMatchBridge