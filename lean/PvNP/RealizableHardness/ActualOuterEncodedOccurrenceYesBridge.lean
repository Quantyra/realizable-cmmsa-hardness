import PvNP.RealizableHardness.ActualMZOuterSourceContract
import PvNP.RealizableHardness.ActualOccurrenceCompleteness
import PvNP.RealizableHardness.ActualLateTauPadding
import PvNP.RealizableHardness.ActualCommonBlockYesComposition

/-!
The source output of the external MZ contract is mapped to the actual ordered
occurrence instance, before the late copy count. No hardness or encoding
constructor is proved here.
-/

namespace PvNP.RealizableHardness.ActualOuterEncodedOccurrenceYesBridge

open PvNP.RealizableHardness
open ActualMZOuterSourceContract
open ActualOccurrenceAllocation
open ActualQuestionMassBridge
open ActualLateTauPadding
open ActualOriginalBlockYesJoint
open ActualTaggedFixedCenterGeometry
open ActualStarSpanIntersection
open ActualConditionalTheorem1Core
open RandomizedReduction
open ActualCommonBlockYesComposition
open ActualTaggedConcreteStarLaw
open ActualTaggedPresentedSelection
open ActualOriginalPostPaddingVerifier
open ActualFiniteLaw
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def occurrenceOfEncoded (E : Encoded3Lin) : Instance E.vars E.rows :=
  ⟨E.source.row, E.source.rhs⟩

local instance encodedRowDecidableEq (E : Encoded3Lin) :
    DecidableEq (occurrenceOfEncoded E).RowId := Classical.decEq _

local instance encodedVarDecidableEq (E : Encoded3Lin) :
    DecidableEq (occurrenceOfEncoded E).GlobalVar := inferInstance

local instance encodedTaggedVarDecidableEq (E : Encoded3Lin) (copies : Nat) :
    DecidableEq (TaggedVar (occurrenceOfEncoded E) copies) := instDecidableEqProd

theorem occurrenceOfEncoded_vars (E : Encoded3Lin)
    (q : Fin E.rows) (i : Fin 3) :
    (occurrenceOfEncoded E).vars q i = E.source.row q i := rfl

theorem occurrenceOfEncoded_rhs (E : Encoded3Lin) (q : Fin E.rows) :
    (occurrenceOfEncoded E).rhs q = E.source.rhs q := rfl

/-- The source violation count is unchanged by the concrete occurrence
allocator's source representation. -/
theorem occurrence_sourceViolations_eq (E : Encoded3Lin)
    (y : Fin E.vars → ZMod 2) :
    (occurrenceOfEncoded E).sourceViolations y = E.source.violations y := by
  have hcount (k : Nat) (p : Fin k → Bool) :
      (List.finRange k).countP p = ∑ r : Fin k, if p r then 1 else 0 := by
    have hl (l : List (Fin k)) (q : Fin k → Bool) :
        l.countP q = (l.map (fun a => if q a then 1 else 0)).sum := by
      induction l with
      | nil => rfl
      | cons a l ih => cases h : q a <;> simp [h, ih, Nat.add_comm]
    rw [hl, ← Fin.sum_univ_def]
  unfold Instance.sourceViolations Finite3LinSource.violations
  rw [hcount]
  apply Finset.sum_congr rfl
  intro q _
  rfl

/-- Positive-error source assignments extend to the actual occurrence and
equality-cloud output without increasing their absolute violation count. -/
theorem occurrence_extension_violations_eq (E : Encoded3Lin)
    (y : Fin E.vars → ZMod 2) :
    (occurrenceOfEncoded E).violations
        ((occurrenceOfEncoded E).sourceExtension y) =
      E.source.violations y := by
  rw [(occurrenceOfEncoded E).sourceExtension_violations,
    occurrence_sourceViolations_eq]

/-- The actual global linear functional induced by a variable assignment. -/
def assignmentFunctional (E : Encoded3Lin) (copies : Nat)
    (x : TaggedVar (occurrenceOfEncoded E) copies → ZMod 2) :
    TaggedAmbient (occurrenceOfEncoded E) copies →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun z => ∑ v, z v * x v
    map_add' := fun a b => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun r a => by
      simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
      refine Eq.trans (Finset.sum_congr rfl fun v _ => mul_assoc r (a v) (x v)) ?_
      exact (Finset.mul_sum Finset.univ (fun v => a v * x v) r).symm }

/-- Evaluating one actual copied equation vector is the original three-term
3Lin row evaluation under the induced functional. -/
theorem assignmentFunctional_equation (E : Encoded3Lin) (copies : Nat)
    (x : TaggedVar (occurrenceOfEncoded E) copies → ZMod 2)
    (e : TaggedRow (occurrenceOfEncoded E) copies) :
    assignmentFunctional E copies x
        (equationVector (taggedSource (occurrenceOfEncoded E) copies).support e) =
      x ((taggedSource (occurrenceOfEncoded E) copies).row e 0) +
      x ((taggedSource (occurrenceOfEncoded E) copies).row e 1) +
      x ((taggedSource (occurrenceOfEncoded E) copies).row e 2) := by
  classical
  change (∑ v : TaggedVar (occurrenceOfEncoded E) copies,
      equationVector (taggedSource (occurrenceOfEncoded E) copies).support e v * x v) = _
  have hsubset : (taggedSource (occurrenceOfEncoded E) copies).support e ⊆
      (Finset.univ : Finset (TaggedVar (occurrenceOfEncoded E) copies)) :=
    Finset.subset_univ _
  have hzero : ∀ v ∈ (Finset.univ : Finset
      (TaggedVar (occurrenceOfEncoded E) copies)),
      v ∉ (taggedSource (occurrenceOfEncoded E) copies).support e →
      equationVector (taggedSource (occurrenceOfEncoded E) copies).support e v * x v = 0 := by
    intro v _ hv
    simp [equationVector, hv]
  have hsum : (∑ v : TaggedVar (occurrenceOfEncoded E) copies,
      equationVector (taggedSource (occurrenceOfEncoded E) copies).support e v * x v) =
      ∑ v ∈ (taggedSource (occurrenceOfEncoded E) copies).support e, x v := by
    rw [← Finset.sum_subset hsubset hzero]
    refine Finset.sum_congr rfl fun v hv => ?_
    simp [equationVector, hv]
  rw [hsum, (taggedSource (occurrenceOfEncoded E) copies).support_eq e]
  have hinj : Set.InjOn ((taggedSource (occurrenceOfEncoded E) copies).row e)
      (Finset.univ : Finset (Fin 3)) := by
    intro a _ b _ hab
    exact (taggedSource (occurrenceOfEncoded E) copies).row_injective e hab
  rw [Finset.sum_image hinj, Fin.sum_univ_three]

theorem assignmentFunctional_badRow_iff (E : Encoded3Lin) (copies : Nat)
    (x : TaggedVar (occurrenceOfEncoded E) copies → ZMod 2)
    (e : TaggedRow (occurrenceOfEncoded E) copies) :
    BadRow (occurrenceOfEncoded E) copies
      (assignmentFunctional E copies x) e ↔
      (taggedSource (occurrenceOfEncoded E) copies).badRow x e = true := by
  unfold BadRow Finite3LinSource.badRow
  rw [assignmentFunctional_equation]
  simp

theorem assignmentFunctional_badRows_card (E : Encoded3Lin) (copies : Nat)
    (x : TaggedVar (occurrenceOfEncoded E) copies → ZMod 2) :
    (badRows (occurrenceOfEncoded E) copies
      (assignmentFunctional E copies x)).card =
      (taggedSource (occurrenceOfEncoded E) copies).violations x := by
  classical
  unfold badRows Finite3LinSource.violations
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp [assignmentFunctional_badRow_iff]

/-- A near-satisfying encoded outer assignment becomes the exact ambient
linear-map premise consumed by the common-draw Eq21 theorem, after actual
occurrence allocation and any number of disjoint copies. -/
theorem nearSatisfiable_positiveErrorAssignment (E : Encoded3Lin)
    (copies : Nat) (ε : Rat) (hε : 0 ≤ ε)
    (hnear : NearSatisfiable E ε) :
    ∃ f : TaggedAmbient (occurrenceOfEncoded E) copies →ₗ[ZMod 2] ZMod 2,
      PositiveErrorAssignment (occurrenceOfEncoded E) copies f ε := by
  obtain ⟨y, hy⟩ := hnear
  let I := occurrenceOfEncoded E
  let x := I.sourceExtension y
  let xtag := Finite3LinSource.repeatAssignment (K := copies) x
  let f := assignmentFunctional E copies xtag
  refine ⟨f, ?_⟩
  have hcount : (badRows I copies f).card = copies * E.source.violations y := by
    rw [show (badRows I copies f).card =
      (taggedSource I copies).violations xtag from
        assignmentFunctional_badRows_card E copies xtag]
    change ((Finite3LinSource.ofActual I).taggedCopy copies).violations xtag = _
    rw [Finite3LinSource.taggedCopy_repeatAssignment_violations,
      Finite3LinSource.ofActual_violations,
      occurrence_extension_violations_eq]
  have hrowsNat : E.rows ≤ Fintype.card I.RowId := by
    rw [I.rowId_card_eq_rows_length]
    exact I.rows_length_ge
  have hrows : (E.rows : Rat) ≤ (Fintype.card I.RowId : Rat) :=
    Nat.cast_le.mpr hrowsNat
  have hεrows := mul_le_mul_of_nonneg_left hrows hε
  unfold PositiveErrorAssignment
  calc
    ((badRows I copies f).card : Rat) = (copies : Rat) * E.source.violations y := by
      exact_mod_cast hcount
    _ ≤ (copies : Rat) * (ε * (E.rows : Rat)) :=
      mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg copies)
    _ ≤ (copies : Rat) * (ε * (Fintype.card I.RowId : Rat)) :=
      mul_le_mul_of_nonneg_left hεrows (Nat.cast_nonneg copies)
    _ = ε * Fintype.card (TaggedRow I copies) := by
      simp [TaggedRow, Fintype.card_prod]
      ring

/-- The late padding count is selected after the fixed source instance,
repetition count, and the arbitrary later positive completeness target. -/
theorem exists_encoded_late_padding (E : Encoded3Lin) (J : Nat)
    (τ : Rat) (hτ : 0 < τ) :
    ∃ T : Nat, 4 ≤ T ∧
      let copies := actualPaddingCopies J T
      actualTaggedBadMass (occurrenceOfEncoded E) copies J ≤ τ / 100 ∧
      actualTaggedBadMass (occurrenceOfEncoded E) copies J ≤ (1 : Rat) / 4 ∧
      actualTaggedGoodMass (occurrenceOfEncoded E) copies J =
        1 - actualTaggedBadMass (occurrenceOfEncoded E) copies J :=
  exists_late_tau_padding (occurrenceOfEncoded E) E.rows_pos τ hτ

/-- The later outer YES error exists after the fixed NO gap, block count,
repetition count, and positive target completeness error are known. -/
theorem exists_late_outer_error (M : ExternalMZOuterSource)
    (blocks J : Nat) (hJ : 0 < J) (τ : Rat) (hτ : 0 < τ) :
    ∃ ε : Rat, 0 < ε ∧ ε < 1 - M.s ∧
      ε ≤ outerYesError blocks J τ := by
  have hp : 0 < outerYesError blocks J τ := outerYesError_pos hJ hτ
  have hs : (0 : Rat) < 1 - M.s := by linarith [M.s_lt_one]
  refine ⟨min (outerYesError blocks J τ / 2) ((1 - M.s) / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · exact (min_le_right _ _).trans_lt (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

/-- An externally supplied encoded SAT YES output produces the manuscript's
concrete occurrence instance and positive-error ambient assignment for every
chosen copy count. The source hardness field remains visibly external. -/
theorem external_yes_to_copied_assignment
    (M : ExternalMZOuterSource) (ε : Rat)
    (hε : 0 < ε) (hgap : ε < 1 - M.s)
    (input : Bits) (hyes : input ∈ Complexity.SAT.ThreeSAT.language)
    (copies : Nat) :
    ∃ E : Encoded3Lin,
      M.encoding.decode ((M.reduction ε hε hgap).map.apply input []) = some E ∧
      ∃ f : TaggedAmbient (occurrenceOfEncoded E) copies →ₗ[ZMod 2] ZMod 2,
        PositiveErrorAssignment (occurrenceOfEncoded E) copies f ε := by
  obtain ⟨E, hparse, hnear⟩ := (M.reduction ε hε hgap).yes input hyes
  obtain ⟨f, hf⟩ := nearSatisfiable_positiveErrorAssignment E copies ε hε.le hnear
  exact ⟨E, hparse, f, hf⟩

/-- The external YES output, chosen after the later positive outer error,
admits actual disjoint-copy padding selected after `τ`. Its copied ambient
assignment has the exact premise needed by Eq21. -/
theorem external_yes_exists_padded_assignment
    (M : ExternalMZOuterSource) (ε : Rat)
    (hε : 0 < ε) (hgap : ε < 1 - M.s)
    (input : Bits) (hyes : input ∈ Complexity.SAT.ThreeSAT.language)
    (J : Nat) (τ : Rat) (hτ : 0 < τ) :
    ∃ (E : Encoded3Lin) (T : Nat),
      M.encoding.decode ((M.reduction ε hε hgap).map.apply input []) = some E ∧
      4 ≤ T ∧
      let copies := actualPaddingCopies J T
      actualTaggedBadMass (occurrenceOfEncoded E) copies J ≤ τ / 100 ∧
      actualTaggedBadMass (occurrenceOfEncoded E) copies J ≤ (1 : Rat) / 4 ∧
      actualTaggedGoodMass (occurrenceOfEncoded E) copies J =
        1 - actualTaggedBadMass (occurrenceOfEncoded E) copies J ∧
      ∃ f : TaggedAmbient (occurrenceOfEncoded E) copies →ₗ[ZMod 2] ZMod 2,
        PositiveErrorAssignment (occurrenceOfEncoded E) copies f ε := by
  obtain ⟨E, hparse, hnear⟩ := (M.reduction ε hε hgap).yes input hyes
  obtain ⟨T, hfour, hτbad, hquarter, hgood⟩ :=
    exists_encoded_late_padding E J τ hτ
  obtain ⟨f, hf⟩ := nearSatisfiable_positiveErrorAssignment E
    (actualPaddingCopies J T) ε hε.le hnear
  exact ⟨E, T, hparse, hfour, hτbad, hquarter, hgood, f, hf⟩

/-- The actual copied assignment from a parsed outer YES instance feeds the
declared common-draw Eq21 theorem. Its geometric fibre preconditions are
kept explicit at this exact instance/copy count. -/
theorem parsed_outer_yes_common_draw
    (M : ExternalMZOuterSource) (ε : Rat)
    (hε : 0 < ε) (hgap : ε < 1 - M.s)
    (input : Bits) (hyes : input ∈ Complexity.SAT.ThreeSAT.language)
    (E : Encoded3Lin)
    (hparse : M.encoding.decode
      ((M.reduction ε hε hgap).map.apply input []) = some E)
    (copies J t h blocks : Nat)
    [Nonempty (ActualOriginalOrderedPaddingLaw.RawOrdered
      (occurrenceOfEncoded E) copies J)]
    [Nonempty (TaggedGoodU (occurrenceOfEncoded E) copies J)]
    [Nonempty (TaggedPresentedLeaf (occurrenceOfEncoded E) copies J h)]
    (hcenter : ∀ U : TaggedGoodU (occurrenceOfEncoded E) copies J,
      Nonempty (TaggedCenterOver (occurrenceOfEncoded E) copies t U))
    (hleaf : ∀ (U : TaggedGoodU (occurrenceOfEncoded E) copies J)
      (K : TaggedCenterOver (occurrenceOfEncoded E) copies t U),
      Nonempty (TaggedLeafOver (occurrenceOfEncoded E) copies h
        (questionOf (occurrenceOfEncoded E) copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hcopies : 0 < copies) (hJ : 0 < J)
    (τ : Rat) (hτ : 0 < τ)
    (hεtarget : ε ≤ outerYesError blocks J τ)
    (hrow : 0 < Fintype.card
      (TaggedRow (occurrenceOfEncoded E) copies))
    (ha : actualTaggedBadMass (occurrenceOfEncoded E) copies J ≤ 1 / 4) :
    ∃ f : TaggedAmbient (occurrenceOfEncoded E) copies →ₗ[ZMod 2] ZMod 2,
      PositiveErrorAssignment (occurrenceOfEncoded E) copies f ε ∧
      eventMass (originalLawFromTagged (occurrenceOfEncoded E) copies
        (k := blocks) hcenter hleaf)
        (Finset.univ.filter (fun x : OriginalDraw
          (occurrenceOfEncoded E) copies J t h blocks =>
          ¬ originalAccepts (occurrenceOfEncoded E) copies
              (ActualHonestTaggedTransport.honestOriginalAssignment
                (occurrenceOfEncoded E) copies f) x)) ≤ τ / 75 := by
  obtain ⟨E', hparse', f, hf⟩ := external_yes_to_copied_assignment
    M ε hε hgap input hyes copies
  have heq : E' = E := Option.some.inj (hparse'.symm.trans hparse)
  subst E'
  refine ⟨f, hf, ?_⟩
  exact common_draw_yes_failure_le (occurrenceOfEncoded E) copies J
    hcenter hleaf ht hh hcopies E.rows_pos hJ f τ ε hτ hε.le
    hεtarget hrow hf ha

end
end ActualOuterEncodedOccurrenceYesBridge
