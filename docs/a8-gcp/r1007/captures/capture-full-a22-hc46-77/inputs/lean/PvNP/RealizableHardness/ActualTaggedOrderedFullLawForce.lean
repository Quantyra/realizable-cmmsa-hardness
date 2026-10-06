import PvNP.RealizableHardness.ActualTaggedCanonicalNoComparison

namespace PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedCanonicalNoComparison
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem dependent_kernel_pushforward
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (muA : FiniteLaw A) (muB : FiniteLaw B)
    (hf : pushforward f muA = muB)
    {C : B → Type*} [∀ b, Fintype (C b)]
    (w : ∀ b, C b → ℚ)
    (jointA : FiniteLaw (Σ a : A, C (f a)))
    (jointB : FiniteLaw (Σ b : B, C b))
    (hA : ∀ p, jointA.mass p = muA.mass p.1 * w (f p.1) p.2)
    (hB : ∀ p, jointB.mass p = muB.mass p.1 * w p.1 p.2) :
    pushforward (fun p : Σ a : A, C (f a) => ⟨f p.1, p.2⟩) jointA = jointB := by
  classical
  apply FiniteLaw.ext
  intro x
  let g : B → ℚ := fun b =>
    ∑ c : C b, if (⟨b, c⟩ : Σ b : B, C b) = x then w b c else 0
  have htransport : (∑ a : A, muA.mass a * g (f a)) =
      ∑ b : B, muB.mass b * g b := by
    calc
      _ = ∑ b : B, (pushforward f muA).mass b * g b := by
        simp only [pushforward_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        simp
      _ = _ := by rw [hf]
  calc
    (pushforward (fun p : Σ a : A, C (f a) => ⟨f p.1, p.2⟩) jointA).mass x =
        ∑ a : A, muA.mass a * g (f a) := by
      rw [pushforward_apply]
      simp only [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [hA]
      by_cases he : (⟨f a, c⟩ : Σ b : B, C b) = x <;>
        simp [he]
    _ = ∑ b : B, muB.mass b * g b := htransport
    _ = jointB.mass x := by
      calc
        _ = ∑ b : B, ∑ c : C b,
              if (⟨b, c⟩ : Σ b : B, C b) = x then
                muB.mass b * w b c else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [g, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          split_ifs <;> simp
        _ = ∑ p : Σ b : B, C b, if p = x then jointB.mass p else 0 := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          rw [hB]
        _ = jointB.mass x := by simp

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat)

/-- The complete ordered eligible-row experiment has exactly the same
conditional K and independent leaf law after forgetting row order. -/
theorem orderedStarLaw_eq_taggedSampleLaw {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
        (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    orderedStarLaw I copies J (t := t) (h := h) (k := k) hcenter hleaf =
      taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
        hcenter hleaf := by
  classical
  let w : ∀ U : TaggedGoodU I copies J,
      (Σ K : TaggedCenterOver I copies t U,
        Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) → ℚ :=
    fun U p =>
      ((1 : ℚ) / Fintype.card (TaggedCenterOver I copies t U)) *
      ((1 : ℚ) / Fintype.card
        (Fin k → TaggedLeafOver I copies h (questionOf I copies U p.1)))
  have hA (p : TaggedOrderedSample I copies J t h k) :
      (taggedOrderedSampleLaw I copies J hcenter hleaf).mass p =
        (orderedGoodLaw I copies J).mass p.1 *
          w (orderedToGoodU I copies J p.1) p.2 := by
    simp only [taggedOrderedSampleLaw, w, uniformLaw_apply]
    ring
  have hB (p : TaggedSample I copies J t h k) :
      (taggedSampleLaw I copies hcenter hleaf).mass p =
        (uniformLaw (TaggedGoodU I copies J)).mass p.1 * w p.1 p.2 := by
    simp only [taggedSampleLaw, w, uniformLaw_apply]
    ring
  have heq := dependent_kernel_pushforward
    (orderedToGoodU I copies J)
    (orderedGoodLaw I copies J)
    (uniformLaw (TaggedGoodU I copies J))
    (orderedGood_pushforward I copies J)
    w (taggedOrderedSampleLaw I copies J hcenter hleaf)
    (taggedSampleLaw I copies hcenter hleaf) hA hB
  exact heq

/-- The fixed arbitrary raw table in the actual ordered source has a single
predraw canonical table controlling physical acceptance at the numerical
class-collision charge. -/
theorem ordered_physical_le_canonical_plus_collision {J t h k : Nat}
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
        (orderedStarLaw I copies J (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T ≤
      (∑ ω : TaggedSample I copies J t h k,
        (orderedStarLaw I copies J (t := t) (h := h) (k := k)
          hcenter hleaf).mass ω *
          (if taggedAccepts I copies C T'
            (sampledStar I copies (J := J) (t := t) (h := h) (k := k) ω).q
            (taggedConvertedLeaves I copies
              (sampledStar I copies (J := J) (t := t) (h := h) (k := k) ω))
           then (1 : ℚ) else 0)) + (1 / 2 : ℚ) ^ J := by
  rw [orderedStarLaw_eq_taggedSampleLaw I copies hcenter hleaf]
  exact tagged_physical_le_canonical_plus_collision I copies hcenter hleaf
    ht hh hexp hk C T

end
end PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
