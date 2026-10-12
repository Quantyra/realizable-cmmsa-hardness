import PvNP.RealizableHardness.ActualCountedAssignmentScore
import PvNP.RealizableHardness.ActualGlobalFullVectorVisibleEvent

/-! Average the literal conditional assignment score under exactly the
existing full-vector law. The independently computed local spans and the
complete original source-game law still require identification.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualFullVectorAssignmentScore

open scoped BigOperators
open ActualCountedAssignmentScore ActualGlobalFullVectorVisibleEvent
open ActualVisibleCountImport ActualFullAdvicePrefix VectorAdvice CoveringSpan
open ActualFixedScoreVisibleApplication ActualVisibleJointSuccess
open ActualCompletionEquationPullback ActualFiniteLaw
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualOccurrenceAllocation ActualNumericSourceHeight ActualNumericExplicitHeight
open ActualNumericRobustReal ActualCmmsaParameterReconciliation
open ActualCmmsaAdmissibilitySelector ActualSelectedCompletionPosteriorBound
open ActualTaggedOrderedFullLawForce ActualTaggedFixedTableAcceptance
open ActualTaggedOrderedQuestionSourceBridge ActualTaggedSelectedDecoderBridge
open ActualGlobalSelectedDensity ActualStarAcceptedGoodMass ActualStarFixedRhoDimensionGuard
open SamplerParameters GrassmannCounting GrassmannIncidence TripleRestrictionRank

open DropTailParameters ZoomOutPosterior

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A constant multiplies the actual full-vector score without changing its
zero branch on dependent prefixes. -/
theorem fullAdviceJointScore_mul {J a r : Nat} (ha : a ≤ r)
    (b : Rat) (k : Real) (f : Draw J → Advice J a → Real) :
    fullAdviceJointScore ha b (fun s Q => k * f s Q) =
      k * fullAdviceJointScore ha b f := by
  unfold fullAdviceJointScore
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro v _
  cases hv : output (advicePrefix ha v) <;> simp [hv] <;> ring

/-- Monotonicity uses the original prior and every supplied tuple, including
the zero-score dependence branch. -/
theorem fullAdviceJointScore_mono {J a r : Nat} (ha : a ≤ r)
    (b : Rat) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (f g : Draw J → Advice J a → Real) (hfg : ∀ s Q, f s Q ≤ g s Q) :
    fullAdviceJointScore ha b f ≤ fullAdviceJointScore ha b g := by
  unfold fullAdviceJointScore
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast drawMass_nonneg b hb hb1 s)
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (by unfold uniformArray; positivity)
  cases hv : output (advicePrefix ha v) with
  | none => simp [hv]
  | some R => simpa [hv] using hfg s (includeSubspace (retained s) R).val

/-- A bounded integrand gives a bounded actual full-vector score; the upper
bound permits dependence failures and uses the two exact normalizations. -/
theorem fullAdviceJointScore_bounds {J a r : Nat} (ha : a ≤ r)
    (b : Rat) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (g : Draw J → Advice J a → Real) (hg : ∀ s Q, 0 ≤ g s Q ∧ g s Q ≤ 1) :
    0 ≤ fullAdviceJointScore ha b g ∧ fullAdviceJointScore ha b g ≤ 1 := by
  have hp (s : Draw J) : (0 : Real) ≤ prior b s := by
    exact_mod_cast drawMass_nonneg b hb hb1 s
  have hv (s : Draw J) (v : Fin r → retained s) :
      0 ≤ (output (advicePrefix ha v)).elim 0
        (fun R => g s (includeSubspace (retained s) R).val) ∧
      (output (advicePrefix ha v)).elim 0
        (fun R => g s (includeSubspace (retained s) R).val) ≤ 1 := by
    cases he : output (advicePrefix ha v) with
    | none => simp [he]
    | some R => simpa [he] using hg s (includeSubspace (retained s) R).val
  have harray (s : Draw J) : (∑ v : Fin r → retained s, uniformArray v) = 1 := by
    have hc : (Fintype.card (Fin r → retained s) : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin r → retained s) ≠ 0)
    simp [uniformArray, hc]
  have hprior : (∑ s : Draw J, (prior b s : Real)) = 1 := by
    exact_mod_cast prior_normalized (J := J) b
  constructor
  · unfold fullAdviceJointScore
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp s)
      (Finset.sum_nonneg (fun v _ => mul_nonneg (by unfold uniformArray; positivity) (hv s v).1)))
  · unfold fullAdviceJointScore
    calc
      _ ≤ ∑ s : Draw J, (prior b s : Real) * 1 := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (hp s)
        calc
          _ ≤ ∑ v : Fin r → retained s, uniformArray v := by
            apply Finset.sum_le_sum
            intro v _
            exact mul_le_of_le_one_right (by unfold uniformArray; positivity) (hv s v).2
          _ = 1 := harray s
      _ = 1 := by simpa only [mul_one] using hprior

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- Same full supplied vector tuple, now scored by the actual conditional
assignment test. Its original-law identification is a separate obligation. -/
def selectedFullVectorAssignmentScore {A m h : Nat}
    (U : TaggedGoodU I copies (blocks A h)) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) : Real :=
  fullAdviceJointScore (Nat.le_of_lt_succ a.isLt) (beta A h)
    (fun s Q => canonicalAssignmentScore I copies m U T choice C Q s)

theorem selected_full_vector_assignment_bounds {A m h : Nat}
    (U : TaggedGoodU I copies (blocks A h)) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    0 ≤ selectedFullVectorAssignmentScore I copies U a T choice C ∧
      selectedFullVectorAssignmentScore I copies U a T choice C ≤ 1 := by
  exact fullAdviceJointScore_bounds (Nat.le_of_lt_succ a.isLt) (beta A h)
    (beta_nonneg A h) (beta_le_one A h) _
    (fun s Q => canonical_assignment_score_bounds I copies m U T choice C Q s)

/-- Integrate the literal-event implication without another vector loss. -/
theorem full_vector_event_cost_le_assignment {A m h sourceCutoff : Nat}
    (U : TaggedGoodU I copies (blocks A h)) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h)
    (hCount : DeclaredMaximalCountContract m sourceCutoff)
    (hm : 256 ≤ m) (hA : 1 ≤ A) (hsource : sourceCutoff ≤ h)
    (hnum : numericHnum m ≤ h)
    (hguards : max 200 (bOf m ^ 2 * (3 * numericRankThreshold m + 5)) ≤ h)
    (C : Rat) (hC : 0 < C) (hthreshold : refreshThreshold m h / 5 < (C : Real)) :
    countedAssignmentCost m h * selectedFullVectorVisibleScore I copies m U a T choice C ≤
      selectedFullVectorAssignmentScore I copies U a T choice C := by
  unfold selectedFullVectorVisibleScore selectedFullVectorAssignmentScore
  rw [← fullAdviceJointScore_mul]
  apply fullAdviceJointScore_mono _ _ (beta_nonneg A h) (beta_le_one A h)
  intro s Q
  dsimp only
  split_ifs with he
  · simpa only [mul_one] using literal_event_counted_assignment_lower
      I copies U T choice Q s hCount hm hA (Nat.le_of_lt_succ a.isLt)
      hsource hnum hguards C hC hthreshold he
  · simpa only [mul_zero] using (canonical_assignment_score_bounds I copies m U T choice C Q s).1


/-- The actual physical antecedents produce the same fixed choice and dimension
with a counted conditional assignment mean; no final game probability is assumed. -/
theorem physical_forces_full_vector_assignment_mean
    {L m A sourceCutoff : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
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
      blocks A (hBlock L m))
    (hCount : DeclaredMaximalCountContract m sourceCutoff)
    (hm : 256 ≤ m) (hsource : sourceCutoff ≤ hBlock L m)
    (hnum : numericHnum m ≤ hBlock L m)
    (hguards : max 200 (bOf m ^ 2 * (3 * numericRankThreshold m + 5)) ≤ hBlock L m) :
    ∃ choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m),
    ∃ a : Fin (numericRankThreshold m + 1),
      countedAssignmentCost m (hBlock L m) * decay 8 (hBlock L m) ≤
        ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
          ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
            selectedFullVectorAssignmentScore I copies U a T choice C := by
  obtain ⟨choice, a, hmean⟩ := physical_forces_actual_full_vector_visible_mean
    I copies base cutoff hA hsel hcenter hleaf ht hheight hexp hk center T alpha
    hphysicalSlack hphysical hRankLt h16 hBase C hC hCsmall hCthreshold
    hmargin hslack hP hT hvector
  refine ⟨choice, a, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hmean
    (countedAssignmentCost_nonneg m (hBlock L m))
  calc
    _ ≤ countedAssignmentCost m (hBlock L m) *
        ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
          ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
            selectedFullVectorVisibleScore I copies m U a T choice C := hscaled
    _ = ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
          ((uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U : Real) *
            (countedAssignmentCost m (hBlock L m) *
              selectedFullVectorVisibleScore I copies m U a T choice C) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro U _
      apply mul_le_mul_of_nonneg_left
        (full_vector_event_cost_le_assignment I copies U a T choice hCount hm hA
          hsource hnum hguards C hC hCthreshold)
      exact_mod_cast (uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).nonneg U

end
end PvNP.RealizableHardness.ActualFullVectorAssignmentScore
