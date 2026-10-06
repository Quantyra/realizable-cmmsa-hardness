import PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

/-! The arbitrary fixed raw tagged table is compared with one canonical
full-domain table chosen before the star draw. The numerical collision charge
is explicit. This is the input to, not a proof of, the MZ local decoder. -/

namespace PvNP.RealizableHardness.ActualTaggedCanonicalNoComparison

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

/-- For arbitrary fixed center and raw leaf tables, choose one full-domain
table before sampling. Its canonical tagged acceptance controls physical
acceptance up to the explicit class-collision loss. -/
theorem tagged_physical_le_canonical_plus_collision {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
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
    ∃ T' : TaggedLeafTable I copies,
      taggedPhysicalMass I copies
        (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T ≤
      (∑ ω : TaggedSample I copies J t h k,
        (taggedSampleLaw I copies hcenter hleaf).mass ω *
          (if taggedAccepts I copies C T' (sampledStar I copies ω).q
            (taggedConvertedLeaves I copies (sampledStar I copies ω))
           then (1 : ℚ) else 0)) + (1 / 2 : ℚ) ^ J := by
  obtain ⟨s, hs⟩ := tagged_sample_exists_selected_le_twoNegJ I copies
    hcenter hleaf ht hh hexp hk C T
  refine ⟨taggedSelectedDomainTable I copies T s, ?_⟩
  convert hs using 1
  unfold taggedSelectedMass
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [← taggedSelectedAccepts_iff_taggedAccepts I copies C T s
    (sampledStar I copies ω)]

end
end PvNP.RealizableHardness.ActualTaggedCanonicalNoComparison
