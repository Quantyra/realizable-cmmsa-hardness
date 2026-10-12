import PvNP.RealizableHardness.ActualSelectedCoordinateMass
import PvNP.RealizableHardness.ActualFixedScoreVisibleApplication
import PvNP.RealizableHardness.ActualSelectedCompletionPosteriorBound
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.SamplerProximity
import PvNP.RealizableHardness.GoodAdvice
import PvNP.RealizableHardness.AdviceExceptions
import PvNP.RealizableHardness.CoveringSpan
import PvNP.RealizableHardness.SamplerParameters
import PvNP.RealizableHardness.DropTailParameters

/-! Average the actual fixed-score visible-joint success inequality over the
original uniform good-question law, with one globally selected table, choice,
and advice dimension. The first result keeps all actual posterior charges;
the second pays their captured numerical bounds. Uncompiled author candidate. -/
namespace PvNP.RealizableHardness.ActualGlobalPosteriorSuccess

open scoped BigOperators
open ActualSelectedCoordinateMass ActualFixedScoreVisibleApplication ActualMaximalPairLadder
open ActualOriginalDecoderSelection ActualTaggedConcreteStarLaw
open ActualTaggedRowDeletion ActualVisibleJointSuccess
open ActualSelectedCompletionPosteriorBound ActualVaryingCompletionException ActualCompletionEquationPullback
open ActualFiniteLaw PosteriorReweighting PosteriorDensity CoveringSpan AdviceExceptions
open GrassmannCounting GrassmannIncidence
open SamplerParameters SamplerProximity GoodAdvice DropTailParameters
open ActualNumericSourceHeight ActualCmmsaParameterReconciliation
open ActualCmmsaAdmissibilitySelector ActualStarAcceptedGoodMass
open ActualStarFixedRhoDimensionGuard ActualNumericRobustReal
open ActualTaggedMZSideDraw ActualTaggedFixedCenterGeometry
open ActualTaggedSelectedDecoderBridge ActualNumericExplicitHeight
open ActualGlobalSelectedDensity ActualTaggedFixedTableAcceptance
open ActualTaggedOrderedQuestionSourceBridge ActualTaggedOrderedFullLawForce
open ActualTaggedPresentedSelection ActualTaggedFixedUDensityForce
open TripleRestrictionRank

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat)

/-- The actual original-favorable advice mass averaged over the original
uniform good-question law, at one fixed coordinate dimension. -/
def selectedCoordinateFavorableMean {J h : Nat} (a : Nat) (e : Real) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) : Real :=
  ∑ U : TaggedGoodU I copies J,
    ((uniformLaw (TaggedGoodU I copies J)).mass U : Real) *
      ((mass (ambientMass : Advice J a → ℚ)
        (selectedCoordinateFavorable I copies U e r T choice) : ℚ) : Real)

/-- The quantitative favorable-mass floor supplied by the physical score
argument, before the conditional-posterior error charges are paid. -/
def selectedCoordinateGlobalMassLower (L m : Nat) : Real :=
  ((1 : Real) / (2 : Real) ^ (6 * (hBlock L m) ^ 2) /
    (numericRankThreshold m + 1)) *
      (8 * successMargin (badExponent m (hBlock L m)))
/-- The fixed-coordinate average result, before replacing any posterior loss
by its asymptotic estimate. T and choice remain fixed for every U in the sum. -/
private theorem fixed_choice_actual_visible_success_average_of_favorable_mass
    {L m A : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I copies (blocks A (hBlock L m)))]
    (choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m))
    (a : Fin (numericRankThreshold m + 1))
    (e : Real) (C : ℚ)
    (hReady : SamplerProximity.Ready A (numericRankThreshold m) (hBlock L m))
    (hh : numericRankThreshold m < hBlock L m)
    (h16 : 16 <= hBlock L m)
    (ha : a.val <= numericRankThreshold m)
    (hah : a.val <= 2 * hBlock L m)
    (h2hJ : 2 * hBlock L m <= blocks A (hBlock L m))
    (hambient : 2 * hBlock L m + numericRankThreshold m <=
      3 * blocks A (hBlock L m))
    (hC : 0 < C) (hCsmall : (C : Real) < e / 3)
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
    (T : TaggedRawVertexTable I copies (blocks A (hBlock L m)) (hBlock L m))
    (hFavorable : selectedCoordinateGlobalMassLower L m <=
      selectedCoordinateFavorableMean I copies a.val e (numericRankThreshold m) T choice) :
    (((∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
      ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real))) -
      ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
        (GoodAdvice.bad A (hBlock L m)) : Real)) -
      (∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
            (badPosterior (beta A (hBlock L m))
              (GoodAdvice.zeta (hBlock L m))
              (completionPulledBack I copies U) : Real))) -
      (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) *
        (C / 4) <=
      (∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          ((jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
            (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
            (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
            (completionPulledBack I copies U)
            (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real))) ∧
      ((((1 : Real) / (2 : Real) ^ (6 * (hBlock L m) ^ 2) /
          (numericRankThreshold m + 1)) *
        (8 * successMargin (badExponent m (hBlock L m))) -
        decay 20 (hBlock L m) - decay 69 (hBlock L m) -
        decay 20 (hBlock L m) / 3) * (C / 4) <=
      (∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
            (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
            (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
            (completionPulledBack I copies U)
            (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real))) := by
  classical
  let Us := TaggedGoodU I copies (blocks A (hBlock L m))
  let mu := uniformLaw Us
  have htail := actualTailThreshold_spec A (hBlock L m) (by omega : 0 < A) hT
  have hbad := GoodAdvice.ready_bad_mass_lt hReady ha hah htail.2
  have hbadC : (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
      (GoodAdvice.bad A (hBlock L m)) : Real) < decay 20 (hBlock L m) := hbad
  let comp := fun U : Us =>
    (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
      (badPosterior (beta A (hBlock L m)) (GoodAdvice.zeta (hBlock L m))
        (completionPulledBack I copies U)) : Real)
  have hcomp (U : Us) : comp U <= decay 69 (hBlock L m) := by
    simpa [comp] using completion_badPosterior_mass_le_decay69 A
      (numericRankThreshold m) (hBlock L m) a.val hA
      h16
      (by omega : numericRankThreshold m <= hBlock L m) hP hT ha I copies U
  have hex := SamplerProximity.ready_exceptional hReady ha
  have hdim := SamplerProximity.ready_dimensions hReady
  have haJ : a.val <= blocks A (hBlock L m) := by omega
  have htvQ := CoveringSpan.actual_adviceTV_le_manuscript
    (beta A (hBlock L m)) (beta_nonneg A (hBlock L m))
    (beta_le_one A (hBlock L m)) haJ
  change adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val <= _ at htvQ
  have htvBound : (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real) <=
      (beta A (hBlock L m) : Real) * Real.sqrt (blocks A (hBlock L m) : Real) *
        (2 : Real) ^ (a.val + 4) := by exact_mod_cast htvQ
  have htv : (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real) <
      decay 20 (hBlock L m) / 3 := by
    have hsqrt : 0 <= Real.sqrt (beta A (hBlock L m) : Real) := Real.sqrt_nonneg _
    have hother : 0 <= Real.sqrt (beta A (hBlock L m) : Real) *
        (blocks A (hBlock L m) : Real) ^ (1 / 4 : Real) := by positivity
    have hdecay : 0 <= decay 70 (hBlock L m) := (decay_pos 70 (hBlock L m)).le
    have hthree : 3 * (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real) <
        decay 20 (hBlock L m) := by nlinarith [hex, hother, hdecay, htvBound]
    linarith
  have hsumWeight : (∑ U : Us, (mu.mass U : Real)) = 1 := by
    have hn := mu.normalized
    exact_mod_cast hn
  have hpoint (U : Us) :
      (mu.mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real) -
         (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) - comp U -
         (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4) <=
      (mu.mass U : Real) *
        (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
          (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
          (completionPulledBack I copies U)
          (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real) := by
    have hper := selected_pair_ready_visible_joint_success I copies hReady hh ha
      h2hJ hambient e C hC hCsmall hmargin hslack U T choice
    have hperQ :
        ((((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : ℚ) : Real) -
         ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : ℚ) : Real) -
         ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (badPosterior (beta A (hBlock L m)) (GoodAdvice.zeta (hBlock L m))
            (completionPulledBack I copies U)) : ℚ) : Real) -
         (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) *
          ((C : Real) / 4)) <=
        (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
          (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
          (completionPulledBack I copies U)
          (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real) := by
      exact_mod_cast hper
    have hμ : 0 <= (mu.mass U : Real) := by exact_mod_cast mu.nonneg U
    simpa [comp, mul_assoc] using mul_le_mul_of_nonneg_left hperQ hμ
  have hsum :
      (∑ U : Us, (mu.mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real) -
         (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) - comp U -
         (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4)) <=
      ∑ U : Us, (mu.mass U : Real) *
        (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
          (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
          (completionPulledBack I copies U)
          (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real) := by
    apply Finset.sum_le_sum
    intro U hU
    exact hpoint U
  have hidentity :
      (∑ U : Us, (mu.mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real) -
         (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) - comp U -
         (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4)) =
      (((∑ U : Us, (mu.mass U : Real) *
          (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
            (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real)) -
        (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) -
        (∑ U : Us, (mu.mass U : Real) * comp U) -
        (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumWeight]
    ring
  rw [hidentity] at hsum
  have hraw : (((∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
      ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : ℚ) : Real)) -
      ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
        (GoodAdvice.bad A (hBlock L m)) : ℚ) : Real) -
      (∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
            (badPosterior (beta A (hBlock L m)) (GoodAdvice.zeta (hBlock L m))
              (completionPulledBack I copies U)) : ℚ) : Real)) -
      (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4) <=
    ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
      ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
        (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
          (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
          (completionPulledBack I copies U)
          (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real) := by
    simpa [Us, mu, comp] using hsum
  have hcompAvg : (∑ U : Us, (mu.mass U : Real) * comp U) <= decay 69 (hBlock L m) := by
    calc
      _ <= ∑ U : Us, (mu.mass U : Real) * decay 69 (hBlock L m) :=
        Finset.sum_le_sum (fun U _ => mul_le_mul_of_nonneg_left (hcomp U)
          (by exact_mod_cast mu.nonneg U))
      _ = decay 69 (hBlock L m) := by rw [← Finset.sum_mul, hsumWeight]; ring
  have hnum :
      selectedCoordinateGlobalMassLower L m - decay 20 (hBlock L m) -
        decay 69 (hBlock L m) - decay 20 (hBlock L m) / 3 <=
      ((∑ U : Us, (mu.mass U : Real) *
        (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real)) -
       (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) -
       (∑ U : Us, (mu.mass U : Real) * comp U) -
       (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) := by
    linarith [hFavorable, hbadC, hcompAvg, htv]
  refine ⟨hraw, ?_⟩
  calc
    _ <= (((∑ U : Us, (mu.mass U : Real) *
        (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real)) -
       (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) -
       (∑ U : Us, (mu.mass U : Real) * comp U) -
       (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4)) :=
         mul_le_mul_of_nonneg_right hnum (by positivity)
    _ <= (∑ U : Us, (mu.mass U : Real) *
        (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
          (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
          (completionPulledBack I copies U)
          (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real)) := hraw

/-- Invoke the original physical-score forcing theorem, keep its single table
and representative choice fixed, and then apply the actual posterior average
at the globally selected advice dimension. -/
theorem physical_forces_fixed_choice_actual_visible_success_average
    {L m A : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I copies (blocks A (hBlock L m)))]
    (hcenter : ∀ U : TaggedGoodU I copies (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I copies (leafT m (hBlock L m)) U))
    (hleaf : ∀ (U : TaggedGoodU I copies (blocks A (hBlock L m)))
        (K : TaggedCenterOver I copies (leafT m (hBlock L m)) U),
      Nonempty (TaggedLeafOver I copies (hBlock L m) (questionOf I copies U K)))
    (ht : leafT m (hBlock L m) <= 2 * (hBlock L m))
    (hheight : hBlock L m <= blocks A (hBlock L m))
    (hexp : 2 * blocks A (hBlock L m) <=
      (2 * (hBlock L m) - leafT m (hBlock L m)) *
        (2 * blocks A (hBlock L m) - 2 * (hBlock L m)))
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
    (C : ℚ) (hC : 0 < C)
    (hCsmall : (C : Real) < refreshThreshold m (hBlock L m) / 3)
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
      (by omega : 0 < A) <= hBlock L m) :
    ∃ choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m),
    ∃ a : Fin (numericRankThreshold m + 1),
    (((selectedCoordinateGlobalMassLower L m - decay 20 (hBlock L m) -
        decay 69 (hBlock L m) - decay 20 (hBlock L m) / 3) * (C / 4)) <=
      ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          (jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
            (selectedCoordinateFavorable I copies U (refreshThreshold m (hBlock L m))
              (numericRankThreshold m) T choice)
            (selectedCoordinateWindow I copies U (refreshThreshold m (hBlock L m))
              (numericRankThreshold m) T choice)
            (completionPulledBack I copies U)
            (selectedVisibleAgreementScore I copies U (refreshThreshold m (hBlock L m))
              (numericRankThreshold m) T choice) C : Real)) := by
  obtain ⟨choice, a, hmass⟩ := physical_forces_global_coordinate_dimension
    I copies base cutoff hA hsel hcenter hleaf ht hheight hexp hk center T alpha
    hphysicalSlack hphysical
  have hready := ActualSelectedCompletionPosteriorBound.proximityThreshold_spec A
    (numericRankThreshold m) (hBlock L m) (by omega : 0 < A) hP
  have hdim := SamplerProximity.ready_dimensions hready
  have hfav : selectedCoordinateGlobalMassLower L m <=
      selectedCoordinateFavorableMean I copies a.val (refreshThreshold m (hBlock L m))
        (numericRankThreshold m) T choice := by
    dsimp [selectedCoordinateGlobalMassLower, selectedCoordinateFavorableMean]
    exact_mod_cast hmass
  refine ⟨choice, a, ?_⟩
  have hsuccess := fixed_choice_actual_visible_success_average_of_favorable_mass
    I copies base cutoff hA hsel choice a (refreshThreshold m (hBlock L m)) C
    hready hRankLt h16 (Nat.le_of_lt_succ a.isLt) (by omega) hdim.2 (by omega)
    hC hCsmall hmargin hslack hP hT T hfav
  exact hsuccess.2
end
end PvNP.RealizableHardness.ActualGlobalPosteriorSuccess
