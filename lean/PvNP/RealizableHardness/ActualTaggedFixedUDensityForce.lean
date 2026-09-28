import PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce

/-! The fixed-table canonical acceptance in the tagged ordered star law is
disintegrated over the eligible first-prover row set. The chosen full-domain
table is fixed before the draw. This is the high-density first-question input
to the MZ local decoder, not the decoder itself. -/

namespace PvNP.RealizableHardness.ActualTaggedFixedUDensityForce

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

/-- The canonical test for a fixed eligible `U`, averaged over exactly the
conditional uniform center and independent uniform leaf tuple. -/
def conditionalCanonicalDensity {J t h k : Nat}
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (U : TaggedGoodU I copies J) : ℚ :=
  ∑ K : TaggedCenterOver I copies t U,
    ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
      (uniformLaw (TaggedCenterOver I copies t U)).mass K *
      (uniformLaw (Fin k → TaggedLeafOver I copies h
        (questionOf I copies U K))).mass Ls *
      (if taggedAccepts I copies C T'
          (sampledStar I copies (⟨U, K, Ls⟩ : TaggedSample I copies J t h k)).q
          (taggedConvertedLeaves I copies
            (sampledStar I copies (⟨U, K, Ls⟩ : TaggedSample I copies J t h k)))
       then (1 : ℚ) else 0)

private theorem conditional_kernel_normalized {J t h k : Nat}
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (U : TaggedGoodU I copies J) :
    (∑ K : TaggedCenterOver I copies t U,
      ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
        (uniformLaw (TaggedCenterOver I copies t U)).mass K *
        (uniformLaw (Fin k → TaggedLeafOver I copies h
          (questionOf I copies U K))).mass Ls) = 1 := by
  classical
  haveI : ∀ K : TaggedCenterOver I copies t U,
      Nonempty (Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :=
    fun K => ⟨fun _ => Classical.choice (hleaf U K)⟩
  calc
    _ = ∑ K : TaggedCenterOver I copies t U,
        (uniformLaw (TaggedCenterOver I copies t U)).mass K *
          (∑ Ls : Fin k → TaggedLeafOver I copies h
            (questionOf I copies U K),
            (uniformLaw (Fin k → TaggedLeafOver I copies h
              (questionOf I copies U K))).mass Ls) := by
          apply Finset.sum_congr rfl
          intro K _
          rw [Finset.mul_sum]
    _ = ∑ K : TaggedCenterOver I copies t U,
          (uniformLaw (TaggedCenterOver I copies t U)).mass K := by
          simp_rw [(uniformLaw (Fin k → TaggedLeafOver I copies h
            (questionOf I copies U _))).normalized, mul_one]
    _ = 1 := (uniformLaw (TaggedCenterOver I copies t U)).normalized

theorem conditionalCanonicalDensity_nonneg_le_one {J t h k : Nat}
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (U : TaggedGoodU I copies J) :
    0 ≤ conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U ∧
      conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U ≤ 1 := by
  classical
  letI : Nonempty (TaggedCenterOver I copies t U) := hcenter U
  letI : ∀ K : TaggedCenterOver I copies t U,
      Nonempty (Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :=
    fun K => ⟨fun _ => Classical.choice (hleaf U K)⟩
  have hkernel (K : TaggedCenterOver I copies t U)
      (Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :
      0 ≤ (uniformLaw (TaggedCenterOver I copies t U)).mass K *
        (uniformLaw (Fin k → TaggedLeafOver I copies h
          (questionOf I copies U K))).mass Ls :=
    mul_nonneg (mass_nonneg _ K) (mass_nonneg _ Ls)
  constructor
  · unfold conditionalCanonicalDensity
    apply Finset.sum_nonneg
    intro K _
    apply Finset.sum_nonneg
    intro Ls _
    exact mul_nonneg (hkernel K Ls) (by split_ifs <;> norm_num)
  · calc
      conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U ≤
        ∑ K : TaggedCenterOver I copies t U,
          ∑ Ls : Fin k → TaggedLeafOver I copies h
            (questionOf I copies U K),
            (uniformLaw (TaggedCenterOver I copies t U)).mass K *
            (uniformLaw (Fin k → TaggedLeafOver I copies h
              (questionOf I copies U K))).mass Ls := by
          unfold conditionalCanonicalDensity
          apply Finset.sum_le_sum
          intro K _
          apply Finset.sum_le_sum
          intro Ls _
          split_ifs <;> simp [hkernel K Ls]
      _ = 1 := conditional_kernel_normalized I copies hcenter hleaf U

/-- Exact disintegration of the ordered canonical test, retaining the same
fixed center table and same predraw full-domain leaf table in every fiber. -/
theorem ordered_canonical_eq_uniformU_mean {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    (∑ ω : TaggedSample I copies J t h k,
      (orderedStarLaw I copies J (t := t) (h := h) (k := k)
        hcenter hleaf).mass ω *
      (if taggedAccepts I copies C T'
        (sampledStar I copies ω).q
        (taggedConvertedLeaves I copies (sampledStar I copies ω))
       then (1 : ℚ) else 0)) =
    ∑ U : TaggedGoodU I copies J,
      (uniformLaw (TaggedGoodU I copies J)).mass U *
        conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U := by
  classical
  rw [orderedStarLaw_eq_taggedSampleLaw I copies hcenter hleaf]
  simp only [TaggedSample, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro U _
  unfold conditionalCanonicalDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Ls _
  simp only [taggedSampleLaw]
  ring

/-- A mean `≥ β` on `[0,1]` fibers places at least `β/2` of the eligible
first questions above density `β/2`. -/
private theorem high_density_mass {U : Type*} [Fintype U]
    (mu : FiniteLaw U) (δ : U → ℚ) (hδ : ∀ u, 0 ≤ δ u ∧ δ u ≤ 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (hmean : β ≤ ∑ u, mu.mass u * δ u) :
    β / 2 ≤ ∑ u, mu.mass u * (if β / 2 ≤ δ u then (1 : ℚ) else 0) := by
  classical
  have hpoint (u : U) :
      mu.mass u * δ u ≤ mu.mass u *
        (β / 2 + if β / 2 ≤ δ u then (1 : ℚ) else 0) := by
    apply mul_le_mul_of_nonneg_left _ (mu.nonneg u)
    by_cases hu : β / 2 ≤ δ u
    · simp only [hu, if_true]
      linarith [(hδ u).2]
    · simp only [hu, if_false, add_zero]
      exact le_of_lt (lt_of_not_ge hu)
  have hsum := Finset.sum_le_sum
    (fun u (_ : u ∈ (Finset.univ : Finset U)) => hpoint u)
  have hnorm := mu.normalized
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm,
    one_mul] at hsum
  linarith

/-- For every fixed arbitrary raw vertex table and center table, the one
predraw canonical table given by representative selection has a positive
mass of high-density eligible `U` whenever the physical mass clears the
explicit class-collision loss. This is the exact averaging input to the
local MZ decoder; it supplies no decoder conclusion. -/
theorem ordered_physical_forces_high_density_U {J t h k : Nat}
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
    (T : TaggedRawVertexTable I copies J h)
    (α : ℚ) (hα : (1 / 2 : ℚ) ^ J ≤ α)
    (hphysical : α ≤ taggedPhysicalMass I copies
      (orderedStarLaw I copies J (t := t) (h := h) (k := k)
        hcenter hleaf).mass
      (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T) :
    ∃ T' : TaggedLeafTable I copies,
      (α - (1 / 2 : ℚ) ^ J) / 2 ≤
        ∑ U : TaggedGoodU I copies J,
          (uniformLaw (TaggedGoodU I copies J)).mass U *
            (if (α - (1 / 2 : ℚ) ^ J) / 2 ≤
              conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U
             then (1 : ℚ) else 0) := by
  obtain ⟨T', hcomp⟩ := ordered_physical_le_canonical_plus_collision
    I copies hcenter hleaf ht hh hexp hk C T
  refine ⟨T', ?_⟩
  apply high_density_mass (uniformLaw (TaggedGoodU I copies J))
    (conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T')
    (fun U => conditionalCanonicalDensity_nonneg_le_one I copies
      hcenter hleaf C T' U) (α - (1 / 2 : ℚ) ^ J)
  · linarith
  · rw [← ordered_canonical_eq_uniformU_mean I copies hcenter hleaf C T']
    linarith

end
end PvNP.RealizableHardness.ActualTaggedFixedUDensityForce
