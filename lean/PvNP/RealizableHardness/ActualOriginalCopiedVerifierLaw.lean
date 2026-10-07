import PvNP.RealizableHardness.ActualTaggedVerifierValueBridge

/-! The copied source verifier as one joint finite experiment.  A draw stores
the eligible copied row set, its transverse center, the ordered conditional
leaves, and one independently uniform full-vertex representative per leaf.
This is a joint-law presentation of the manuscript's post-padding verifier;
the separate bridge below checks it against the previously nested score. -/

namespace PvNP.RealizableHardness.ActualOriginalCopiedVerifierLaw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
open PvNP.RealizableHardness.ActualTaggedVerifierValueBridge
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

def SourceDraw (J t h k : Nat) :=
  Σ p : TaggedSample I copies J t h k,
    TaggedIndependentChoice I copies (sampledStar I copies p).leaves

noncomputable instance sourceDrawFintype (J t h k : Nat) :
    Fintype (SourceDraw I copies J t h k) := by
  unfold SourceDraw
  infer_instance

/-- A normalized joint law, with the representative choice sampled *after*
the ordered leaves, independently in each queried full-vertex class. -/
def sourceDrawLaw {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (SourceDraw I copies J t h k) := by
  classical
  let μ := orderedStarLaw I copies J (t := t) (h := h) (k := k) hcenter hleaf
  let ν (p : TaggedSample I copies J t h k) :=
    uniformLaw (TaggedIndependentChoice I copies (sampledStar I copies p).leaves)
  refine ⟨fun x => μ.mass x.1 * (ν x.1).mass x.2, ?_, ?_⟩
  · intro x
    exact mul_nonneg (μ.nonneg x.1) ((ν x.1).nonneg x.2)
  · change ∑ x : SourceDraw I copies J t h k,
      μ.mass x.1 * (ν x.1).mass x.2 = 1
    simp only [SourceDraw, Fintype.sum_sigma]
    calc
      _ = ∑ p : TaggedSample I copies J t h k,
          μ.mass p * (∑ r, (ν p).mass r) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.mul_sum]
      _ = ∑ p : TaggedSample I copies J t h k, μ.mass p := by
            simp [FiniteLaw.normalized]
      _ = 1 := μ.normalized

/-- The manuscript test reads one fixed legal leaf table at each sampled
representative, transports to the presented leaf, and checks the stored K. -/
def sourceAccepts {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (x : SourceDraw I copies J t h k) : Prop :=
  taggedPhysicalAccepts I copies C T (sampledStar I copies x.1) x.2

def sourceScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) : ℚ :=
  eventMass (sourceDrawLaw I copies (k := k) hcenter hleaf)
    (Finset.univ.filter (sourceAccepts I copies (k := k) C T))

/-- Equality of the independently defined joint-law score and the nested
tagged copied-source score, for every fixed predraw table pair. -/
theorem sourceScore_eq_taggedSourceVerifierScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    sourceScore I copies (k := k) hcenter hleaf C T =
      taggedSourceVerifierScore I copies (k := k) hcenter hleaf C T := by
  classical
  unfold sourceScore eventMass
  simp only [Finset.sum_filter, Finset.mem_univ, true_and]
  simp only [SourceDraw, Fintype.sum_sigma]
  unfold sourceDrawLaw sourceAccepts taggedSourceVerifierScore taggedPhysicalMass
  apply Finset.sum_congr rfl
  intro p _
  simp [uniformLaw_apply, uniformMean, Finset.mul_sum, Finset.sum_div,
    mul_assoc, mul_comm, mul_left_comm]

end
end PvNP.RealizableHardness.ActualOriginalCopiedVerifierLaw
