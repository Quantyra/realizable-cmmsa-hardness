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

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat)

/-- The fixed-coordinate average result, before replacing any posterior loss
by its asymptotic estimate. T and choice remain fixed for every U in the sum. -/
theorem fixed_choice_actual_visible_success_average
    {L m A : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I copies (blocks A (hBlock L m)))]
    (choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m))
    (a : Fin (numericRankThreshold m + 1))
    (e : Real) (C : ℚ)
    (hReady : SamplerProximity.Ready A (numericRankThreshold m) (hBlock L m))
    (hh : numericRankThreshold m < hBlock L m)
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
    (hFavorable :
      ((1 : Real) / (2 : Real) ^ (6 * (hBlock L m) ^ 2) /
          (numericRankThreshold m + 1)) *
        (8 * successMargin (badExponent m (hBlock L m))) <=
      (\sum U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
            (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real)))) :
    (((\sum U : TaggedGoodU I copies (blocks A (hBlock L m)),
      ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real))) -
      ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
        (GoodAdvice.bad A (hBlock L m)) : Real)) -
      (\sum U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
            (badPosterior (beta A (hBlock L m))
              (GoodAdvice.zeta (hBlock L m))
              (completionPulledBack I copies U) : Real))) -
      (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) *
        (C / 4) <=
      (\sum U : TaggedGoodU I copies (blocks A (hBlock L m)),
        ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
          ((jointVisibleSuccess (A := A) (h := hBlock L m) (a := a.val)
            (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice)
            (selectedCoordinateWindow I copies U e (numericRankThreshold m) T choice)
            (completionPulledBack I copies U)
            (selectedVisibleAgreementScore I copies U e (numericRankThreshold m) T choice) C : Real))) âˆ§
      ((((1 : Real) / (2 : Real) ^ (6 * (hBlock L m) ^ 2) /
          (numericRankThreshold m + 1)) *
        (8 * successMargin (badExponent m (hBlock L m))) -
        decay 20 (hBlock L m) - decay 69 (hBlock L m) -
        decay 20 (hBlock L m) / 3) * (C / 4) <=
      (\sum U : TaggedGoodU I copies (blocks A (hBlock L m)),
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
        (completionPulledBack I copies U) : Real))
  have hcomp (U : Us) : comp U <= decay 69 (hBlock L m) := by
    simpa [comp] using completion_badPosterior_mass_le_decay69 A
      (numericRankThreshold m) (hBlock L m) a.val hA
      (by omega : 16 <= hBlock L m)
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
  have hsumWeight : (\sum U : Us, (mu.mass U : Real)) = 1 := by
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
    have hper := selected_pair_ready_visible_joint_success I copies U hReady hh ha
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
    simpa [comp] using mul_le_mul_of_nonneg_left hperQ hμ
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
      (\sum U : Us, (mu.mass U : Real) *
        ((mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real) -
         (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) - comp U -
         (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4)) =
      (((\sum U : Us, (mu.mass U : Real) *
          (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
            (selectedCoordinateFavorable I copies U e (numericRankThreshold m) T choice) : Real)) -
        (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) -
        (\sum U : Us, (mu.mass U : Real) * comp U) -
        (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real)) * (C / 4)) := by
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul, hsumWeight]
    ring
  rw [hidentity] at hsum
  have hraw := (by simpa [Us, mu, comp] using hsum)
  have hcompAvg : (∑ U : Us, (mu.mass U : Real) * comp U) <= decay 69 (hBlock L m) := by
    calc
      _ <= ∑ U : Us, (mu.mass U : Real) * decay 69 (hBlock L m) :=
        Finset.sum_le_sum (fun U _ => mul_le_mul_of_nonneg_left (hcomp U)
          (by exact_mod_cast mu.nonneg U))
      _ = decay 69 (hBlock L m) := by rw [Finset.sum_mul, hsumWeight]; ring
  have hnum :
      ((1 : Real) / (2 : Real) ^ (6 * (hBlock L m) ^ 2) /
        (numericRankThreshold m + 1)) *
        (8 * successMargin (badExponent m (hBlock L m))) -
        (mass (ambientMass : Advice (blocks A (hBlock L m)) a.val -> ℚ)
          (GoodAdvice.bad A (hBlock L m)) : Real) -
        (∑ U : Us, (mu.mass U : Real) * comp U) -
        (adviceTV (beta A (hBlock L m)) (blocks A (hBlock L m)) a.val : Real) <=
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
end PvNP.RealizableHardness.ActualGlobalPosteriorSuccess
