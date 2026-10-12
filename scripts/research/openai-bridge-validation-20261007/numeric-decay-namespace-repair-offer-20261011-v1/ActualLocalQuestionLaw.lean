import PvNP.RealizableHardness.ActualLocalAssignmentStrategies
import PvNP.RealizableHardness.ActualFullVectorAssignmentScore

/-! The canonical conditional mean is dominated by the actual two-local-law
question experiment, using exact vector and row-draw reindexing. Original
iid-row eligibility and the external strategy domain remain to be joined.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualLocalQuestionLaw

open scoped BigOperators
open ActualLocalAssignmentStrategies ActualFullVectorAssignmentScore
open ActualSharedAdviceSpans ActualCountedAssignmentScore ActualFullAdvicePrefix
open ActualFixedScoreConditionalAgreement ActualFunctionalAssignmentAcceptance
open ActualTaggedRowDeletion ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualVisibleQuestionCompletion ActualFiniteLaw ActualNumericSourceHeight
open ActualNumericRobustReal ActualVisibleCountImport ActualNumericExplicitHeight
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualTaggedOrderedFullLawForce ActualTaggedFixedTableAcceptance
open ActualTaggedOrderedQuestionSourceBridge ActualTaggedSelectedDecoderBridge
open ActualGlobalSelectedDensity ActualStarAcceptedGoodMass ActualStarFixedRhoDimensionGuard
open VectorAdvice CoveringSpan GrassmannCounting GrassmannIncidence TripleRestrictionRank
open SamplerParameters

open DropTailParameters ZoomOutPosterior

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- Forward coordinates evaluate the same literal conditional score; both
inverse equivalences cancel and containment proofs are irrelevant. -/
theorem canonical_assignment_score_forward {J h a : Nat} (m : Nat)
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U) (Q : Grass (OriginalSpace I copies U) a)
    (hQV : Q.val ≤ actualRetained I copies U s) :
    canonicalAssignmentScore I copies m U T choice C
      (actualRowGrassEquiv I copies U a Q) (rowDrawEquiv I copies U s) =
        (selectedAssignmentMass I copies m U T choice C s Q hQV : Real) := by
  have hQ : (actualRowGrassEquiv I copies U a Q).val ≤
      retained (rowDrawEquiv I copies U s) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hm : actualRowCoordinateEquiv I copies U x ∈
        (actualRetained I copies U s).map (actualRowCoordinateEquiv I copies U).toLinearMap :=
      ⟨x, hQV hx, rfl⟩
    rwa [actualRetained_map_coordinates] at hm
  simp only [canonicalAssignmentScore, dif_pos hQ, Equiv.symm_apply_apply]

/-- The exact inner full-array integrand in the canonical score. -/
def canonicalTupleScore {J h : Nat} (m : Nat) (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : Draw J) (v : Fin (numericRankThreshold m) → retained s) : Real :=
  (output (advicePrefix (Nat.le_of_lt_succ a.isLt) v)).elim 0
    (fun R => canonicalAssignmentScore I copies m U T choice C
      (includeSubspace (retained s) R).val s)

private theorem output_subtype_score
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] {a : Nat}
    (W : Submodule (ZMod 2) V) (v : Fin a → W) (F : Grass V a → Real) :
    (output (fun i => (v i).val)).elim 0 F =
      (output v).elim 0 (fun R => F (includeSubspace W R).val) := by
  rw [← output_subtype]
  cases output v <;> rfl

/-- Every actual supplied tuple has exactly the same zero-extended analysis
score after canonical transport, including dependent prefixes. -/
theorem canonical_tuple_score_actual {J h : Nat} (m : Nat)
    (a : Fin (numericRankThreshold m + 1))
    (U : TaggedGoodU I copies J) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) (C : Rat)
    (s : ActualRowDraw I copies U)
    (v : Fin (numericRankThreshold m) → actualRetained I copies U s) :
    canonicalTupleScore I copies m a U T choice C (rowDrawEquiv I copies U s)
      (fun i => actualRetainedCoordinateEquiv I copies U s (v i)) =
      (originalTupleAnalysisScore I copies m a U T choice C s v : Real) := by
  unfold canonicalTupleScore
  rw [← output_subtype_score]
  change (output (fun i => actualRowCoordinateEquiv I copies U
      (advicePrefix (Nat.le_of_lt_succ a.isLt) v i).val)).elim 0
      (fun Q => canonicalAssignmentScore I copies m U T choice C Q
        (rowDrawEquiv I copies U s)) = _
  rw [← original_prefix_span_coordinates I copies (Nat.le_of_lt_succ a.isLt) U s v]
  cases hQ : output (fun i => (advicePrefix (Nat.le_of_lt_succ a.isLt) v i).val) with
  | none => simp [originalTupleAnalysisScore, hQ]
  | some Q =>
    obtain ⟨hQV, _⟩ := original_visible_prefix_some I copies
      (Nat.le_of_lt_succ a.isLt) U s v Q hQ
    simp only [Option.map_some, Option.elim]
    rw [canonical_assignment_score_forward I copies m U T choice C s Q hQV]
    simp only [originalTupleAnalysisScore, hQ, Option.elim, dif_pos hQV]

/-- Actual row deletion, actual full retained vectors, and the literal
independent local assignment test. -/
def actualLocalQuestionScore {A m h : Nat}
    (U : TaggedGoodU I copies (blocks A h)) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) : Real :=
  ∑ s : ActualRowDraw I copies U, (actualRowDrawMass I copies U (beta A h) s : Real) *
    ∑ v : Fin (numericRankThreshold m) → actualRetained I copies U s,
      uniformArray v * (localAssignmentScore I copies m a U T choice C s v : Real)

theorem actual_local_question_score_nonneg {A m h : Nat}
    (U : TaggedGoodU I copies (blocks A h)) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    0 ≤ actualLocalQuestionScore I copies U a T choice C := by
  unfold actualLocalQuestionScore
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg
  · exact_mod_cast actualRowDrawMass_nonneg I copies U (beta A h)
      (beta_nonneg A h) (beta_le_one A h) s
  · apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg (by unfold uniformArray; positivity)
    exact_mod_cast local_assignment_score_nonneg I copies m a U T choice C s v

/-- Exact reindexing and the fallback domination compare the canonical
analysis with the actual local-strategy experiment for each question. -/
theorem full_vector_assignment_le_local_question {A m h : Nat}
    (U : TaggedGoodU I copies (blocks A h)) (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    selectedFullVectorAssignmentScore I copies U a T choice C ≤
      actualLocalQuestionScore I copies U a T choice C := by
  have hdraw := actual_draw_real_score_transport I copies U (beta A h)
    (fun s => ∑ v : Fin (numericRankThreshold m) → retained s,
      uniformArray v * canonicalTupleScore I copies m a U T choice C s v)
  change (∑ s : Draw (blocks A h), (prior (beta A h) s : Real) *
    ∑ v : Fin (numericRankThreshold m) → retained s,
      uniformArray v * canonicalTupleScore I copies m a U T choice C s v) ≤ _
  rw [← hdraw]
  unfold actualLocalQuestionScore
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (by
    exact_mod_cast actualRowDrawMass_nonneg I copies U (beta A h)
      (beta_nonneg A h) (beta_le_one A h) s)
  rw [← actual_retained_tuple_mean I copies U s
    (canonicalTupleScore I copies m a U T choice C (rowDrawEquiv I copies U s))]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (by unfold uniformArray; positivity)
  rw [canonical_tuple_score_actual]
  exact_mod_cast original_tuple_analysis_le_local I copies m a U T choice C s v

/-- The same globally fixed choice and dimension survive integration over
the original uniform good-question law. -/
theorem full_vector_assignment_mean_le_local {A m h : Nat}
    [Nonempty (TaggedGoodU I copies (blocks A h))]
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    (∑ U : TaggedGoodU I copies (blocks A h),
      ((uniformLaw (TaggedGoodU I copies (blocks A h))).mass U : Real) *
        selectedFullVectorAssignmentScore I copies U a T choice C) ≤
      ∑ U : TaggedGoodU I copies (blocks A h),
        ((uniformLaw (TaggedGoodU I copies (blocks A h))).mass U : Real) *
          actualLocalQuestionScore I copies U a T choice C := by
  apply Finset.sum_le_sum
  intro U _
  apply mul_le_mul_of_nonneg_left (full_vector_assignment_le_local_question I copies U a T choice C)
  exact_mod_cast (uniformLaw (TaggedGoodU I copies (blocks A h))).nonneg U


/-- The actual physical antecedents yield one fixed choice and dimension
for the actual two-local-law question experiment. Original iid rows remain separate. -/
theorem physical_forces_actual_local_question_mean
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
            actualLocalQuestionScore I copies U a T choice C := by
  obtain ⟨choice, a, hmean⟩ := physical_forces_full_vector_assignment_mean
    I copies base cutoff hA hsel hcenter hleaf ht hheight hexp hk center T alpha
    hphysicalSlack hphysical hRankLt h16 hBase C hC hCsmall hCthreshold
    hmargin hslack hP hT hvector hCount hm hsource hnum hguards
  exact ⟨choice, a, hmean.trans
    (full_vector_assignment_mean_le_local I copies a T choice C)⟩

end
end PvNP.RealizableHardness.ActualLocalQuestionLaw
