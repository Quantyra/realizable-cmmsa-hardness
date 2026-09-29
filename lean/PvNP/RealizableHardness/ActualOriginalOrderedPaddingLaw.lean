import PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier
import PvNP.RealizableHardness.ActualLateTauPadding

/-! The copied-row verifier samples an eligible question after conditioning.
This module keeps its raw ordered-question law and retained probability
explicit, so the late-tau padding bound applies at the correct stage. -/

namespace PvNP.RealizableHardness.ActualOriginalOrderedPaddingLaw

open ActualFiniteLaw
open ActualQuestionMassBridge
open ActualTaggedOrderedQuestionSourceBridge
open ActualOriginalPostPaddingVerifier
open ActualOccurrenceAllocation
open ActualTaggedConcreteStarLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : Instance N m) (copies J : Nat)

abbrev RawOrdered := Fin J → Fin copies × I.RowId

noncomputable instance rawOrderedFintype : Fintype (RawOrdered I copies J) := by
  classical
  unfold RawOrdered
  infer_instance

/-- The exact support of the already committed eligible ordered-question type. -/
def legitimate : Finset (RawOrdered I copies J) :=
  Finset.univ.image (fun u : TaggedOrderedGood I copies J => u.1)

theorem legitimate_card :
    (legitimate I copies J).card =
      Fintype.card (TaggedOrderedGood I copies J) := by
  classical
  unfold legitimate
  rw [Finset.card_image_of_injective]
  · exact Finset.card_univ
  · exact Subtype.val_injective

theorem legitimate_eq_actual_good :
    legitimate I copies J = actualTaggedGoodQuestions I copies J := by
  classical
  ext u
  simp only [legitimate, Finset.mem_image, Finset.mem_univ, true_and,
    actualTaggedGoodQuestions, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv⟩
    subst u
    exact v.2
  · intro hu
    exact ⟨⟨u, hu⟩, rfl⟩

theorem raw_legitimate_mass [Nonempty (RawOrdered I copies J)] :
    eventMass (uniformLaw (RawOrdered I copies J))
      (legitimate I copies J) =
      (Fintype.card (TaggedOrderedGood I copies J) : ℚ) /
        Fintype.card (RawOrdered I copies J) := by
  classical
  simp only [eventMass, uniformLaw_apply, Finset.sum_const, nsmul_eq_mul]
  rw [legitimate_card]
  ring

theorem raw_legitimate_mass_eq_actual_good
    [Nonempty (RawOrdered I copies J)] :
    eventMass (uniformLaw (RawOrdered I copies J))
      (legitimate I copies J) = actualTaggedGoodMass I copies J := by
  rw [raw_legitimate_mass I copies J]
  unfold actualTaggedGoodMass
  rw [← legitimate_eq_actual_good I copies J, legitimate_card I copies J]

theorem raw_legitimate_mass_eq_one_sub_bad
    [Nonempty (RawOrdered I copies J)]
    (hcopies : 0 < copies) (hm : 0 < m) :
    eventMass (uniformLaw (RawOrdered I copies J))
      (legitimate I copies J) = 1 - actualTaggedBadMass I copies J := by
  rw [raw_legitimate_mass_eq_actual_good I copies J]
  exact actual_tagged_good_mass_eq_one_sub_bad_mass I copies J hcopies hm

/-- Conditioning uniform raw ordered rows on the exact legitimate support
gives the uniform ordered-good law pointwise. -/
theorem conditioned_ordered_point
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (u : TaggedOrderedGood I copies J) :
    (uniformLaw (RawOrdered I copies J)).mass u.1 /
        eventMass (uniformLaw (RawOrdered I copies J))
          (legitimate I copies J) =
      (orderedGoodLaw I copies J).mass u := by
  classical
  have hraw : (Fintype.card (RawOrdered I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (RawOrdered I copies J) ≠ 0)
  have hgood : (Fintype.card (TaggedOrderedGood I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedOrderedGood I copies J) ≠ 0)
  rw [raw_legitimate_mass I copies J]
  change (1 : ℚ) / Fintype.card (RawOrdered I copies J) /
      ((Fintype.card (TaggedOrderedGood I copies J) : ℚ) /
        Fintype.card (RawOrdered I copies J)) =
      (1 : ℚ) / Fintype.card (TaggedOrderedGood I copies J)
  field_simp

/-- Exact U marginal of the raw ordered row experiment conditioned on
legitimacy. The sum ranges over the actual eligible raw tuple type, and the
projection forgets ordering only after conditioning. -/
theorem conditioned_taggedU_mass
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (U : TaggedGoodU I copies J) :
    (∑ u : TaggedOrderedGood I copies J,
      if orderedToGoodU I copies J u = U then
        (uniformLaw (RawOrdered I copies J)).mass u.1 /
          eventMass (uniformLaw (RawOrdered I copies J))
            (legitimate I copies J)
      else 0) = (uniformLaw (TaggedGoodU I copies J)).mass U := by
  classical
  have h := congrArg (fun μ : FiniteLaw (TaggedGoodU I copies J) => μ.mass U)
    (orderedGood_pushforward I copies J)
  rw [pushforward_apply] at h
  calc
    _ = ∑ u : TaggedOrderedGood I copies J,
        if orderedToGoodU I copies J u = U then
          (orderedGoodLaw I copies J).mass u else 0 := by
          apply Finset.sum_congr rfl
          intro u _
          split_ifs <;> simp [conditioned_ordered_point I copies J u]
    _ = (uniformLaw (TaggedGoodU I copies J)).mass U := h

instance originalUNonempty [Nonempty (TaggedGoodU I copies J)] :
    Nonempty (OriginalU I copies J) :=
  Nonempty.map (originalUEquiv I copies J).symm ‹_›

theorem originalU_uniform_mass
    [Nonempty (TaggedGoodU I copies J)]
    (U : OriginalU I copies J) :
    (uniformLaw (OriginalU I copies J)).mass U =
      (uniformLaw (TaggedGoodU I copies J)).mass
        (U.toTagged I copies) := by
  classical
  rw [uniformLaw_apply, uniformLaw_apply]
  congr 1
  exact_mod_cast Fintype.card_congr (originalUEquiv I copies J)

/-- The conditional raw U mass equals the U sampler used as the first step
of the independent original post-padding verifier draw. -/
theorem conditioned_originalU_mass
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (U : OriginalU I copies J) :
    (∑ u : TaggedOrderedGood I copies J,
      if orderedToGoodU I copies J u = U.toTagged I copies then
        (uniformLaw (RawOrdered I copies J)).mass u.1 /
          eventMass (uniformLaw (RawOrdered I copies J))
            (legitimate I copies J)
      else 0) = (uniformLaw (OriginalU I copies J)).mass U := by
  rw [conditioned_taggedU_mass I copies J]
  exact (originalU_uniform_mass I copies J U).symm

/-- The U coordinate of the full post-padding draw has its declared uniform
first-stage marginal, after all center, leaf, and representative draws. -/
theorem originalLaw_U_marginal {t h k : Nat}
    [Nonempty (OriginalU I copies J)]
    (hcenter : ∀ U : OriginalU I copies J,
      Nonempty (OriginalK I copies t U))
    (hleaf : ∀ (U : OriginalU I copies J)
      (K : OriginalK I copies t U),
      Nonempty (OriginalLeaf I copies h U K))
    (U : OriginalU I copies J) :
    (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
      (originalLaw I copies hcenter hleaf)).mass U =
      (uniformLaw (OriginalU I copies J)).mass U := by
  classical
  let μU := uniformLaw (OriginalU I copies J)
  let μK (u : OriginalU I copies J) : FiniteLaw (OriginalK I copies t u) :=
    @uniformLaw _ inferInstance (hcenter u)
  let μL (u : OriginalU I copies J) (K : OriginalK I copies t u) :
      FiniteLaw (Fin k → OriginalLeaf I copies h u K) :=
    @uniformLaw _ inferInstance ⟨fun _ => Classical.choice (hleaf u K)⟩
  let μR (u : OriginalU I copies J) (K : OriginalK I copies t u)
      (Ls : Fin k → OriginalLeaf I copies h u K) :
      FiniteLaw ((i : Fin k) → ActualTaggedPresentedSelection.TaggedClassRepresentative I copies
        (ActualTaggedPresentedSelection.taggedClassOf I copies
          ((Ls i).toTagged I copies).1)) := uniformLaw _
  rw [pushforward_apply]
  change (∑ x : OriginalDraw I copies J t h k,
    if x.U = U then
      μU.mass x.U * (μK x.U).mass x.K *
        (μL x.U x.K).mass x.leaves *
        (μR x.U x.K x.leaves).mass x.representatives else 0) = μU.mass U
  have hsum (u : OriginalU I copies J) :
      (∑ K : OriginalK I copies t u,
        ∑ Ls : Fin k → OriginalLeaf I copies h u K,
          ∑ reps : (i : Fin k) → ActualTaggedPresentedSelection.TaggedClassRepresentative I copies
            (ActualTaggedPresentedSelection.taggedClassOf I copies
              ((Ls i).toTagged I copies).1),
            μU.mass u * (μK u).mass K * (μL u K).mass Ls *
              (μR u K Ls).mass reps) = μU.mass u := by
    calc
      _ = ∑ K : OriginalK I copies t u,
          ∑ Ls : Fin k → OriginalLeaf I copies h u K,
            μU.mass u * (μK u).mass K * (μL u K).mass Ls := by
              apply Finset.sum_congr rfl; intro K _
              apply Finset.sum_congr rfl; intro Ls _
              rw [← Finset.mul_sum, (μR u K Ls).normalized, mul_one]
      _ = ∑ K : OriginalK I copies t u,
            μU.mass u * (μK u).mass K := by
              apply Finset.sum_congr rfl; intro K _
              rw [← Finset.mul_sum, (μL u K).normalized, mul_one]
      _ = μU.mass u := by
              rw [← Finset.mul_sum, (μK u).normalized, mul_one]
  have heq := Fintype.sum_equiv (originalFieldsEquiv I copies)
    (fun x : OriginalDraw I copies J t h k =>
      if x.U = U then μU.mass x.U * (μK x.U).mass x.K *
        (μL x.U x.K).mass x.leaves *
          (μR x.U x.K x.leaves).mass x.representatives else 0)
    (fun x : OriginalFields I copies J t h k =>
      if x.1 = U then μU.mass x.1 * (μK x.1).mass x.2.1 *
        (μL x.1 x.2.1).mass x.2.2.1 *
          (μR x.1 x.2.1 x.2.2.1).mass x.2.2.2 else 0)
    (by intro x; rfl)
  rw [heq]
  simp only [OriginalFields, Fintype.sum_sigma]
  calc
    _ = ∑ u : OriginalU I copies J,
        if u = U then μU.mass u else 0 := by
          apply Finset.sum_congr rfl
          intro u _
          split_ifs with hu
          · exact hsum u
          · simp
    _ = μU.mass U := by simp

theorem originalLawFromTagged_U_marginal {t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (U : OriginalU I copies J) :
    (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
      (originalLawFromTagged I copies hcenter hleaf)).mass U =
      (uniformLaw (OriginalU I copies J)).mass U := by
  let hc (u : OriginalU I copies J) : Nonempty (OriginalK I copies t u) :=
    Nonempty.map (originalKEquiv I copies t u).symm
      (hcenter (u.toTagged I copies))
  let hl (u : OriginalU I copies J) (K : OriginalK I copies t u) :
      Nonempty (OriginalLeaf I copies h u K) :=
    Nonempty.map (originalLeafEquiv I copies h u K).symm
      (hleaf (u.toTagged I copies) (K.toTagged I copies))
  change (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
    (originalLaw I copies hc hl)).mass U =
      (uniformLaw (OriginalU I copies J)).mass U
  exact originalLaw_U_marginal I copies J hc hl U

/-- The full verifier's U marginal is exactly the U law obtained by
conditioning raw ordered copied rows on legitimacy. -/
theorem conditional_raw_eq_originalDraw_U {t h k : Nat}
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (U : OriginalU I copies J) :
    (∑ u : TaggedOrderedGood I copies J,
      if orderedToGoodU I copies J u = U.toTagged I copies then
        (uniformLaw (RawOrdered I copies J)).mass u.1 /
          eventMass (uniformLaw (RawOrdered I copies J))
            (legitimate I copies J)
      else 0) =
      (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
        (originalLawFromTagged I copies hcenter hleaf)).mass U := by
  rw [conditioned_originalU_mass I copies J U,
    originalLawFromTagged_U_marginal I copies J hcenter hleaf U]

end
end PvNP.RealizableHardness.ActualOriginalOrderedPaddingLaw
