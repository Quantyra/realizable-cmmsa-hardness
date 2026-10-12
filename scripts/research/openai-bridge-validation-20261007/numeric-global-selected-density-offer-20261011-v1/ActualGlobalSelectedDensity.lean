import PvNP.RealizableHardness.ActualTaggedFixedUDensityForce
import PvNP.RealizableHardness.ActualTaggedMZSideDraw

/-! Keep the one global representative choice in the density conclusion.
This supplies the same selected table required by actual visible coherence.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualGlobalSelectedDensity

open PvNP.RealizableHardness
open ActualFiniteLaw ActualTaggedConcreteStarLaw ActualTaggedOrderedQuestionSourceBridge
open ActualTaggedOrderedFullLawForce ActualTaggedFixedCenterGeometry
open ActualTaggedFixedTableAcceptance ActualTaggedPresentedSelection
open ActualTaggedSelectedDecoderBridge ActualTaggedFixedUDensityForce
open ActualTaggedOrderedClassCollisionBound ActualTaggedMZSideDraw
open ActualTaggedComplementStarDensityBridge
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)

/-- Preserve the exact choice returned by the physical collision comparison,
and disintegrate its same canonical table under the original good-U law. -/
theorem physical_le_same_choice_mean_plus_collision {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J) (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (C : TaggedCenterTable I copies) (T : TaggedRawVertexTable I copies J h) :
    ∃ choice : TaggedRepresentativeChoice I copies J h,
      taggedPhysicalMass I copies
        (orderedStarLaw I copies J (t := t) (h := h) (k := k) hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T ≤
      (∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U *
          conditionalCanonicalDensity I copies (k := k) hcenter hleaf C
            (taggedSelectedDomainTable I copies T choice) U) + (1 / 2 : Rat) ^ J := by
  obtain ⟨choice, hchoice⟩ := tagged_sample_exists_selected_le_twoNegJ
    I copies hcenter hleaf ht hh hexp hk C T
  refine ⟨choice, ?_⟩
  rw [← ordered_canonical_eq_uniformU_mean I copies hcenter hleaf C
    (taggedSelectedDomainTable I copies T choice)]
  rw [orderedStarLaw_eq_taggedSampleLaw I copies hcenter hleaf]
  convert hchoice using 1
  unfold taggedSelectedMass
  congr 1
  apply Finset.sum_congr rfl
  intro omega _
  rw [← taggedSelectedAccepts_iff_taggedAccepts I copies C T choice
    (sampledStar I copies omega)]

private theorem density_mass_lower {U : Type*} [Fintype U]
    (mu : FiniteLaw U) (density : U → Rat)
    (hbound : ∀ u, density u ≤ 1) (S : Rat) (hS : 0 ≤ S)
    (hmean : 16 * S ≤ ∑ u, mu.mass u * density u) :
    8 * S ≤ ∑ u, mu.mass u * (if 8 * S ≤ density u then (1 : Rat) else 0) := by
  have hpoint (u : U) : mu.mass u * density u ≤
      mu.mass u * (8 * S + if 8 * S ≤ density u then (1 : Rat) else 0) := by
    apply mul_le_mul_of_nonneg_left _ (mu.nonneg u)
    by_cases hu : 8 * S ≤ density u
    · simp only [hu, if_true]
      linarith [hbound u]
    · simp only [hu, if_false, add_zero]
      exact le_of_lt (lt_of_not_ge hu)
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset U)) => hpoint u)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mu.normalized,
    one_mul] at hsum
  linarith

/-- One predraw representative choice has the required full positive mass
of high-density questions. The witness is not erased into an arbitrary table. -/
theorem physical_forces_same_choice_high_density {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J) (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (C : TaggedCenterTable I copies) (T : TaggedRawVertexTable I copies J h)
    (S alpha : Rat) (hS : 0 ≤ S)
    (hslack : (1 / 2 : Rat) ^ J + 16 * S ≤ alpha)
    (hphysical : alpha ≤ taggedPhysicalMass I copies
      (orderedStarLaw I copies J (t := t) (h := h) (k := k) hcenter hleaf).mass
      (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T) :
    ∃ choice : TaggedRepresentativeChoice I copies J h,
      8 * S ≤ ∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U *
          (if 8 * S ≤ conditionalCanonicalDensity I copies (k := k) hcenter hleaf C
            (taggedSelectedDomainTable I copies T choice) U then (1 : Rat) else 0) := by
  obtain ⟨choice, hchoice⟩ := physical_le_same_choice_mean_plus_collision
    I copies hcenter hleaf ht hh hexp hk C T
  refine ⟨choice, ?_⟩
  apply density_mass_lower (uniformLaw (TaggedGoodU I copies J))
    (conditionalCanonicalDensity I copies (k := k) hcenter hleaf C
      (taggedSelectedDomainTable I copies T choice))
    (fun U => (conditionalCanonicalDensity_nonneg_le_one I copies hcenter hleaf C
      (taggedSelectedDomainTable I copies T choice) U).2) S hS
  linarith

/-- The actual side-density input to the original decoder has the same
global raw table and representative choice as the visible prover's table. -/
theorem physical_forces_same_choice_side_density {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J) (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (C : TaggedCenterTable I copies) (T : TaggedRawVertexTable I copies J h)
    (S alpha : Rat) (hS : 0 ≤ S)
    (hslack : (1 / 2 : Rat) ^ J + 16 * S ≤ alpha)
    (hphysical : alpha ≤ taggedPhysicalMass I copies
      (orderedStarLaw I copies J (t := t) (h := h) (k := k) hcenter hleaf).mass
      (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T) :
    ∃ choice : TaggedRepresentativeChoice I copies J h,
      8 * S ≤ ∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U *
          (if 8 * S ≤ sideConditionalDensity I copies U t h k C
            (taggedSelectedDomainTable I copies T choice) then (1 : Rat) else 0) := by
  obtain ⟨choice, hchoice⟩ := physical_forces_same_choice_high_density
    I copies hcenter hleaf ht hh hexp hk C T S alpha hS hslack hphysical
  refine ⟨choice, ?_⟩
  simpa only [conditionalCanonicalDensity_eq_side] using hchoice

end
end PvNP.RealizableHardness.ActualGlobalSelectedDensity
