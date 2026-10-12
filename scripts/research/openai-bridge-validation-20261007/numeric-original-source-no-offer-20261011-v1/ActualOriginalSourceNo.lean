import PvNP.RealizableHardness.ActualVerifierAggregation
import PvNP.RealizableHardness.ActualOriginalSourceScalar
import PvNP.RealizableHardness.TaggedFinite3LinSource

/-! Literal source promises, exact padding transport and conditional numeric
NO composition. The imported source bound and actual-instance NO promise
are explicit hypotheses. No SAT reduction, common floor or certification
is asserted. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOriginalSourceNo

open scoped BigOperators
open ActualOccurrenceAllocation ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedOrderedQuestionSourceBridge ActualQuestionMassBridge ActualTaggedRowDeletion
open ActualVisibleQuestionCompletion ActualVisibleAmbientLadder ActualFunctionalAssignmentAcceptance
open ActualOrderedDeletionLaw ActualOccurrenceAdviceLaw ActualLocalAssignmentStrategies
open ActualLocalQuestionLaw ActualOriginalRealRowLaw ActualOriginalOrderedRowLaw
open ActualPrivateAssignmentLaw ActualFiniteLaw ActualNumericSourceHeight
open TripleRestrictionRank GrassmannIncidence VectorAdvice SamplerParameters

open ActualCountedAssignmentScore ActualNumericRobustReal ActualVisibleCountImport
open ActualNumericExplicitHeight ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualTaggedOrderedFullLawForce ActualTaggedFixedTableAcceptance ActualTaggedSelectedDecoderBridge
open ActualGlobalSelectedDensity ActualStarAcceptedGoodMass ActualStarFixedRhoDimensionGuard
open DropTailParameters ZoomOutPosterior

open CoveringSpan

open ActualVerifierAggregation ActualOriginalSourceScalar ActualMaximalCountSpecialization
open Finite3LinSource ActualTotalOrderedStrategy

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

/-- No assignment satisfies at least a (1-gap) fraction of the rows. -/
def StrictNoPromise {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var] (source : Finite3LinSource Row Var) (gap : Real) : Prop :=
  ∀ x : Var → ZMod 2, gap * (Fintype.card Row : Real) < (source.violations x : Real)

theorem strict_no_taggedCopy {Row Var : Type*} [Fintype Row] [Fintype Var]
    [DecidableEq Row] [DecidableEq Var] (source : Finite3LinSource Row Var)
    (copies : Nat) (hcopies : 0 < copies) (gap : Real)
    (hNo : StrictNoPromise source gap) : StrictNoPromise (source.taggedCopy copies) gap := by
  intro x
  change gap * (Fintype.card (Fin copies × Row) : Real) <
    ((source.taggedCopy copies).violations x : Real)
  rw [taggedCopy_violations]
  push_cast
  have hcard : (Fintype.card (Fin copies × Row) : Real) =
      (copies : Real) * (Fintype.card Row : Real) := by simp
  rw [hcard]
  calc
    gap * ((copies : Real) * (Fintype.card Row : Real)) =
        ∑ _k : Fin copies, gap * (Fintype.card Row : Real) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ < ∑ k : Fin copies, (source.violations (restrictAssignment x k) : Real) := by
      apply Finset.sum_lt_sum
      · intro k _
        exact (hNo (restrictAssignment x k)).le
      · exact ⟨⟨0,hcopies⟩, Finset.mem_univ _, hNo (restrictAssignment x ⟨0,hcopies⟩)⟩

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)

def ActualNoPromise (gap : Real) : Prop :=
  ∀ x : I.GlobalVar → ZMod 2, gap * (I.rows.length : Real) < (I.violations x : Real)

theorem actual_no_finite_source (gap : Real) (hNo : ActualNoPromise I gap) :
    StrictNoPromise (Finite3LinSource.ofActual I) gap := by
  intro x
  simpa only [I.rowId_card_eq_rows_length, ofActual_violations] using hNo x

theorem actual_no_tagged (hcopies : 0 < copies) (gap : Real)
    (hNo : ActualNoPromise I gap) : StrictNoPromise (taggedSource I copies) gap := by
  exact strict_no_taggedCopy (Finite3LinSource.ofActual I) copies hcopies gap
    (actual_no_finite_source I gap hNo)

/-- Declared consequence of the external repeated-game theorem for the
literal verifier and local summaries. This is an explicit proposition
parameter, not an axiom or a locally proved imported theorem. -/
structure DeclaredOriginalSourceBound (kappa gap : Real) : Prop where
  kappa_pos : 0 < kappa
  gap_pos : 0 < gap
  gap_lt_one : gap < 1
  bound : ∀ {n rowCount : Nat} (source : Instance n rowCount) (copies A m h : Nat),
    0 < rowCount → 0 < copies → 0 < A → 0 < h →
    StrictNoPromise (taggedSource source copies) gap →
    ∀ f : OriginalFirstQuestion source copies A m h → TaggedAmbient source copies,
    ∀ g : OriginalSecondQuestion source copies A m h → TaggedAmbient source copies,
      deterministicVerifierMean (originalSampleWeight source copies (A := A) (m := m) (h := h))
        (originalFirstQuestion source copies) (originalSecondQuestion source copies)
        (originalSampleAccepts source copies) f g ≤
          1 / (2 : Real) ^ ((kappa * gap ^ 2 / (2 : Real) ^ numericRankThreshold m) *
            (beta A h : Real) * (blocks A h : Real))

/-- The imported bound is applied to the actual derandomized strategies,
then transported back to the concrete raw iid score. -/
theorem original_iid_le_declared_source_upper {A m h : Nat} (kappa gap : Real)
    (hSound : DeclaredOriginalSourceBound kappa gap)
    (hrows : 0 < rows) (hcopies : 0 < copies) (hA : 0 < A) (hh : 0 < h)
    (hNo : StrictNoPromise (taggedSource I copies) gap)
    (a : Fin (numericRankThreshold m + 1))
    (T : TaggedRawVertexTable I copies (blocks A h) h)
    (choice : TaggedRepresentativeChoice I copies (blocks A h) h) (C : Rat) :
    (∑ u : Fin (blocks A h) → TaggedRow I copies,
      (iidOrderedMass I copies (blocks A h) u : Real) *
        orderedQuestionScore I copies a T choice C u) ≤
      sourceOuterUpper kappa gap A (numericRankThreshold m) h := by
  obtain ⟨f,g,hfg⟩ := original_iid_local_derandomization I copies a T choice C
  have hbound := hSound.bound I copies A m h hrows hcopies hA hh hNo f g
  rw [original_outer_exponent_identity] at hbound
  exact hfg.trans hbound

/-- Conditional numeric NO with every original physical antecedent copied
unchanged. Source construction and common-floor discharge remain required. -/
theorem physical_source_no_contradiction
    {L m A sourceCutoff : Nat} (padding : Nat) (hpadding : 4 ≤ padding)
    (hrows : 0 < rows) (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) padding) (blocks A (hBlock L m)))]
    (hcenter : ∀ U : TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) padding) (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) padding) (leafT m (hBlock L m)) U))
    (hleaf : ∀ (U : TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) padding) (blocks A (hBlock L m)))
        (K : TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) padding) (leafT m (hBlock L m)) U),
      Nonempty (TaggedLeafOver I (actualPaddingCopies (blocks A (hBlock L m)) padding) (hBlock L m) (questionOf I (actualPaddingCopies (blocks A (hBlock L m)) padding) U K)))
    (ht : leafT m (hBlock L m) <= 2 * hBlock L m)
    (hheight : hBlock L m <= blocks A (hBlock L m))
    (hexp : 2 * blocks A (hBlock L m) <=
      (2 * hBlock L m - leafT m (hBlock L m)) *
        (2 * blocks A (hBlock L m) - 2 * hBlock L m))
    (hk : m ^ 2 <= 2 ^ blocks A (hBlock L m))
    (center : TaggedCenterTable I (actualPaddingCopies (blocks A (hBlock L m)) padding))
    (T : TaggedRawVertexTable I (actualPaddingCopies (blocks A (hBlock L m)) padding) (blocks A (hBlock L m)) (hBlock L m))
    (alpha : ℚ)
    (hphysicalSlack : (1 / 2 : ℚ) ^ blocks A (hBlock L m) +
      16 * successMargin (badExponent m (hBlock L m)) <= alpha)
    (hphysical : alpha <= taggedPhysicalMass I (actualPaddingCopies (blocks A (hBlock L m)) padding)
      (orderedStarLaw I (actualPaddingCopies (blocks A (hBlock L m)) padding) (blocks A (hBlock L m))
        (t := leafT m (hBlock L m)) (h := hBlock L m) (k := m) hcenter hleaf).mass
      (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) padding) (J := blocks A (hBlock L m))
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
    (hguards : max 200 (bOf m ^ 2 * (3 * numericRankThreshold m + 5)) ≤ hBlock L m)
    (kappa gap : Real) (hSound : DeclaredOriginalSourceBound kappa gap)
    (hNo : ActualNoPromise I gap)
    (hcost : countCostHeight m ≤ hBlock L m)
    (hcoef : 9 < kappa * gap ^ 2 * (A : Real) / (2 : Real) ^ numericRankThreshold m) : False := by
  obtain ⟨choice,a,hlower⟩ := physical_forces_total_original_iid_mean I padding hpadding hrows
    base cutoff hA hsel hcenter hleaf ht hheight hexp hk center T alpha
    hphysicalSlack hphysical hRankLt h16 hBase C hC hCsmall hCthreshold
    hmargin hslack hP hT hvector hCount hm hsource hnum hguards
  have hcopies := actualPaddingCopies_pos (blocks A (hBlock L m)) padding
  have htagged := actual_no_tagged I (actualPaddingCopies (blocks A (hBlock L m)) padding)
    hcopies gap hNo
  have hupper := original_iid_le_declared_source_upper I
    (actualPaddingCopies (blocks A (hBlock L m)) padding) kappa gap hSound hrows hcopies
    (by omega : 0 < A) (by omega : 0 < hBlock L m) htagged a T choice C
  exact source_scalar_contradiction (by omega : 1 ≤ m) hcost
    (by omega : 0 < hBlock L m) hcoef hlower hupper

end
end PvNP.RealizableHardness.ActualOriginalSourceNo
