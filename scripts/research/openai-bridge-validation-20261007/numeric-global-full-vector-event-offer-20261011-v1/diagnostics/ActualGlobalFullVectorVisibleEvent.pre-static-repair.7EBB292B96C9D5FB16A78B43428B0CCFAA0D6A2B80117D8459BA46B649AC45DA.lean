import PvNP.RealizableHardness.ActualGlobalPosteriorSuccess
import PvNP.RealizableHardness.ActualFullAdvicePrefix
import PvNP.RealizableHardness.ActualGlobalDecoderScalar
import PvNP.RealizableHardness.ActualSelectedCoordinateMass
import PvNP.RealizableHardness.ActualFixedScoreVisibleApplication
import PvNP.RealizableHardness.ActualVisibleJointSuccess
import PvNP.RealizableHardness.ActualSelectedCompletionPosteriorBound
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.SamplerProximity
import PvNP.RealizableHardness.GoodAdvice
import PvNP.RealizableHardness.SamplerParameters
import PvNP.RealizableHardness.DropTailParameters

/-! Compose the actual global posterior visible-success average, the exact
full-tuple prefix marginal, and the same-height scalar loss. This reaches an
original-law full-vector visible-event mean, not source-game acceptance. -/
namespace PvNP.RealizableHardness.ActualGlobalFullVectorVisibleEvent

open scoped BigOperators
open ActualGlobalPosteriorSuccess ActualFullAdvicePrefix ActualGlobalDecoderScalar
open ActualSelectedCoordinateMass ActualFixedScoreVisibleApplication
open ActualVisibleJointSuccess ActualSelectedCompletionPosteriorBound
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry ActualTaggedMZSideDraw
open ActualTaggedSelectedDecoderBridge ActualOriginalDecoderSelection ActualTaggedRowDeletion
open ActualNumericSourceHeight ActualNumericExplicitHeight ActualNumericRobustReal
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualStarAcceptedGoodMass ActualStarFixedRhoDimensionGuard
open ActualGlobalSelectedDensity ActualTaggedOrderedQuestionSourceBridge
open ActualTaggedOrderedFullLawForce ActualTaggedFixedTableAcceptance
open ActualTaggedPresentedSelection ActualTaggedFixedUDensityForce
open ActualFiniteLaw ActualCompletionEquationPullback ActualVaryingCompletionException
open ActualVisibleVectorAdvice VectorAdvice GoodAdvice SamplerParameters SamplerProximity
open DropTailParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat)

/-- The actual full tuple is sampled, while only the fixed globally selected
prefix is decoded and checked by the literal visible event. -/
private def selectedFullVectorVisibleScore {A m r h : Nat}
    (U : TaggedGoodU I copies (blocks A h))
    (a : Fin (r + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h)
    (C : ℚ) : Real :=
  let F := selectedCoordinateFavorable I copies U (refreshThreshold m h) r T choice
  let W := selectedCoordinateWindow I copies U (refreshThreshold m h) r T choice
  let H := completionPulledBack I copies U
  let g := selectedVisibleAgreementScore I copies U (refreshThreshold m h) r T choice
  fullAdviceJointScore (Nat.le_of_lt_succ a.isLt) (beta A h)
    (fun s Q => if goodFavorable F H Q && visibleEvent Q (W Q) H (g Q) C s then 1 else 0)

/-- Physical score yields a globally fixed table/choice/advice dimension whose
actual original-good-question full-vector visible-event mean is at least D8.
One full-tuple dependence loss is paid after the global posterior charges. -/
theorem physical_forces_actual_full_vector_visible_mean
    {L m A : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I copies (blocks A (hBlock L m)))]
    (hcenter : ∀ U : TaggedGoodU I copies (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I copies (leafT m (hBlock L m)) U))
    (hleaf : ∀ (U : TaggedGoodU I copies (blocks A (hBlock L m)))
        (K : TaggedCenterOver I copies (leafT m (hBlock L m)) U),
      Nonempty (TaggedLeafOver I copies (hBlock L m) (questionOf I copies U K)))
    (ht : leafT m (hBlock L m) <= 2 * hBlock L m)
    (hheight : hBlock L m <= blocks A (hBlock L m))
    (hexp : 2 * blocks A (hBlock L m) <=
      (2 * hBlock L m - leafT m (hBlock L m)) *
        (2 * blocks A (hBlock L m) - 2 * hBlock L m))
    (hk : m ^ 2 <= 2 ^ blocks A (hBlock L m))
    (center : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies (blocks A (hBlock L m)) (hBlock L m))
    (alpha : ℚ)
    (hphysicalSlack : (1 / 2 : ℚ) ^ blocks A (hBlock L m) +
      16 * successMargin (badExponent m (hBlock L m)) <= alpha)
    (hphysical : alpha <= taggedPhysicalMass I copies
      (orderedStarLaw I copies (blocks A (hBlock L m))
        (t := leafT m (hBlock L m)) (h := hBlock L m) (k := m) hcenter hleaf).mass
      (sampledStar I copies (J := blocks A (hBlock L m))
        (t := leafT m (hBlock L m)) (h := hBlock L m) (k := m)) center T)
    (hRankLt : numericRankThreshold m < hBlock L m)
    (h16 : 16 <= hBlock L m)
    (hBase : 2 * m + 4 <= hBlock L m)
    (C : ℚ) (hC : 0 < C)
    (hCsmall : (C : Real) < refreshThreshold m (hBlock L m) / 3)
    (hCthreshold : refreshThreshold m (hBlock L m) / 5 < (C : Real))
    (hmargin : qdecay 10 (hBlock L m) +
      (2 / (2 : ℚ) ^ (2 * blocks A (hBlock L m) -
        2 * (hBlock L m) ^ 4 - 2 * hBlock L m - numericRankThreshold m - 1)) +
      4 * GoodAdvice.zeta (hBlock L m) <= C / 2)
    (hslack : blocks A (hBlock L m) + 2 * hBlock L m + 1 <=
      3 * blocks A (hBlock L m) - 2 * (hBlock L m) ^ 4 -
        numericRankThreshold m)
    (hP : ActualSelectedCompletionPosteriorBound.proximityThreshold A
      (numericRankThreshold m) (by omega : 0 < A) <= hBlock L m)
    (hT : ActualSelectedCompletionPosteriorBound.actualTailThreshold A
      (by omega : 0 < A) <= hBlock L m)
    (hvector : numericRankThreshold m + 100 * (hBlock L m) ^ 2 <=
      blocks A (hBlock L m)) :
    ∃ choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m),
    ∃ a : Fin (numericRankThreshold m + 1),
      decay 8 (hBlock L m) <=
        ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
          ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
            selectedFullVectorVisibleScore I copies U a T choice C := by
  classical
  let J := blocks A (hBlock L m)
  let R := numericRankThreshold m
  let H := hBlock L m
  let Us := TaggedGoodU I copies J
  let mu := uniformLaw Us
  obtain ⟨choice, a, havg⟩ :=
    physical_forces_fixed_choice_actual_visible_success_average
      I copies base cutoff hA hsel hcenter hleaf ht hheight hexp hk center T alpha
      hphysicalSlack hphysical hRankLt h16 C hC hCsmall hmargin hslack hP hT
  have ha : a.val <= R := Nat.le_of_lt_succ a.isLt
  have hRJ : R <= J := by dsimp [R, J, H]; omega
  have hsumWeight : (∑ U : Us, (mu.mass U : Real)) = 1 := by
    exact_mod_cast mu.normalized
  have hglobal : posteriorFloor m R H (C : Real) <=
      ∑ U : Us, (mu.mass U : Real) *
        (jointVisibleSuccess (A := A) (h := H) (a := a.val)
          (selectedCoordinateFavorable I copies U (refreshThreshold m H) R T choice)
          (selectedCoordinateWindow I copies U (refreshThreshold m H) R T choice)
          (completionPulledBack I copies U)
          (selectedVisibleAgreementScore I copies U (refreshThreshold m H) R T choice) C : Real) := by
    have hfloor :
        (selectedCoordinateGlobalMassLower L m - decay 20 H - decay 69 H - decay 20 H / 3) *
            ((C : Real) / 4) = posteriorFloor m R H (C : Real) := by
      simp [R, H, selectedCoordinateGlobalMassLower, posteriorFloor, decay]
      ring
    rw [← hfloor]
    simpa [Us, mu, H, R] using havg
  have hscalar := actual_posterior_floor_sub_vector_lower
    (m := m) (r := R) (J := J) (h := H) (C := (C : Real))
    (by dsimp [R, H]; omega) hBase hCthreshold (by dsimp [R, J, H]; exact hvector)
  have hF (U : Us) : Advice J a.val -> Bool :=
    selectedCoordinateFavorable I copies U (refreshThreshold m H) R T choice
  have hW (U : Us) : Advice J a.val -> Submodule (ZMod 2) (Vector J) :=
    selectedCoordinateWindow I copies U (refreshThreshold m H) R T choice
  have hDraw (U : Us) : Draw J -> Submodule (ZMod 2) (Vector J) :=
    completionPulledBack I copies U
  have hg (U : Us) : Advice J a.val -> Draw J -> ℚ :=
    selectedVisibleAgreementScore I copies U (refreshThreshold m H) R T choice
  have htransfer (U : Us) :
      (jointVisibleSuccess (A := A) (h := H) (a := a.val)
        (hF U) (hW U) (hDraw U) (hg U) C : Real) -
          VectorAdvice.error R J <= selectedFullVectorVisibleScore I copies U a T choice C := by
    have h := ActualFullAdvicePrefix.visible_joint_event_full_advice_transfer
      (A := A) (h := H) (a := a.val) (r := R) ha hRJ
      (hF U) (hW U) (hDraw U) (hg U) C
    simpa [selectedFullVectorVisibleScore, hF, hW, hDraw, hg, H, R, J] using h
  have hpoint (U : Us) :
      (mu.mass U : Real) *
          ((jointVisibleSuccess (A := A) (h := H) (a := a.val)
            (hF U) (hW U) (hDraw U) (hg U) C : Real) - VectorAdvice.error R J) <=
        (mu.mass U : Real) * selectedFullVectorVisibleScore I copies U a T choice C := by
    have hμ : 0 <= (mu.mass U : Real) := by exact_mod_cast mu.nonneg U
    exact mul_le_mul_of_nonneg_left (htransfer U) hμ
  have hsum := Finset.sum_le_sum (fun U _ => hpoint U)
  have hidentity :
      (∑ U : Us, (mu.mass U : Real) *
        ((jointVisibleSuccess (A := A) (h := H) (a := a.val)
          (hF U) (hW U) (hDraw U) (hg U) C : Real))) - VectorAdvice.error R J =
      ∑ U : Us, (mu.mass U : Real) *
        ((jointVisibleSuccess (A := A) (h := H) (a := a.val)
          (hF U) (hW U) (hDraw U) (hg U) C : Real) - VectorAdvice.error R J) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumWeight]
    ring
  have htransferAvg :
      (∑ U : Us, (mu.mass U : Real) *
        ((jointVisibleSuccess (A := A) (h := H) (a := a.val)
          (hF U) (hW U) (hDraw U) (hg U) C : Real))) - VectorAdvice.error R J <=
      ∑ U : Us, (mu.mass U : Real) *
        selectedFullVectorVisibleScore I copies U a T choice C := by
    rw [hidentity]
    exact hsum
  have hfinal : decay 8 H <=
      ∑ U : Us, (mu.mass U : Real) *
        selectedFullVectorVisibleScore I copies U a T choice C := by
    calc
      _ <= posteriorFloor m R H (C : Real) - VectorAdvice.error R J := hscalar
      _ <= (∑ U : Us, (mu.mass U : Real) *
          (jointVisibleSuccess (A := A) (h := H) (a := a.val)
            (hF U) (hW U) (hDraw U) (hg U) C : Real)) - VectorAdvice.error R J :=
        sub_le_sub_right hglobal _
      _ <= _ := htransferAvg
  exact ⟨choice, a, by simpa [Us, mu, H, R, J] using hfinal⟩

end
end PvNP.RealizableHardness.ActualGlobalFullVectorVisibleEvent
