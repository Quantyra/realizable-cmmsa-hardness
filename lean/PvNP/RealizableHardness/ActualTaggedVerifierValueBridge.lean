import PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
import PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound

/-! The tagged copied-source verifier as an explicit ordered law and event,
and its pointwise/value comparison with the full-domain composed law. This
does not identify an independently specified untagged manuscript verifier. -/

namespace PvNP.RealizableHardness.ActualTaggedVerifierValueBridge

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
open PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound
open PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

/-- The ordered tagged copied-source verifier: draw an eligible `U`, stored
center `K`, independent leaves, then independent full-vertex representatives
and test all row-side constraints plus center agreement on fixed tables. -/
noncomputable def taggedSourceVerifierScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) : ℚ :=
  taggedPhysicalMass I copies
    (orderedStarLaw I copies J (t := t) (h := h) (k := k)
      hcenter hleaf).mass
    (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T

theorem taggedSourceVerifierScore_eq_composedScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    taggedSourceVerifierScore I copies (k := k) hcenter hleaf C T =
      composedTaggedScore I copies (k := k) hcenter hleaf C T := by
  exact (composedTaggedScore_eq_orderedPhysicalMass I copies
    hcenter hleaf C T).symm

/-- The clique-selection loss is charged for every fixed arbitrary raw
vertex table before sampling. The selected representative choice is fixed
before the verifier draw. -/
theorem taggedSourceVerifierScore_le_selected_add_collision
    {J t h k : Nat} [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    ∃ s : TaggedRepresentativeChoice I copies J h,
      taggedSourceVerifierScore I copies (k := k) hcenter hleaf C T ≤
        taggedSelectedMass I copies
          (orderedStarLaw I copies J (t := t) (h := h) (k := k)
            hcenter hleaf).mass
          (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T s +
        (1 / 2 : ℚ) ^ J := by
  obtain ⟨s, hs⟩ := tagged_sample_exists_selected_le_twoNegJ I copies
    hcenter hleaf ht hh hexp hk C T
  refine ⟨s, ?_⟩
  simpa only [taggedSourceVerifierScore,
    orderedStarLaw_eq_taggedSampleLaw] using hs

/-- The finite supremum over legal predraw assignments for the tagged
ordered verifier, with invalid raw tables assigned score zero. -/
noncomputable def taggedSourceVerifierLegalValue {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) : ℚ := by
  classical
  let F : TaggedCenterTable I copies × TaggedRawVertexTable I copies J h → ℚ :=
    fun CT => if TaggedLegalRawTable I copies CT.2 then
      taggedSourceVerifierScore I copies (k := k) hcenter hleaf CT.1 CT.2 else 0
  exact (Finset.univ : Finset
    (TaggedCenterTable I copies × TaggedRawVertexTable I copies J h)).sup'
      (by simp) F

theorem taggedSourceVerifierLegalValue_eq_composedLegalValue {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    taggedSourceVerifierLegalValue I copies (k := k) hcenter hleaf =
      composedLegalValue I copies (k := k) hcenter hleaf := by
  classical
  unfold taggedSourceVerifierLegalValue composedLegalValue
  simp only [taggedSourceVerifierScore_eq_composedScore]

end
end PvNP.RealizableHardness.ActualTaggedVerifierValueBridge
