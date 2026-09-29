import PvNP.RealizableHardness.ActualOriginalOrderedPaddingLaw
import PvNP.RealizableHardness.ActualHonestTaggedTransport
import PvNP.RealizableHardness.ActualTaggedFailureTransport

/-! The original block of the manuscript's late-tau YES comparison. The
positive-error assignment is an explicit hypothesis, chosen only after the
late outer YES error. The conclusion is a joint raw-legitimate numerator. -/

namespace PvNP.RealizableHardness.ActualOriginalBlockYesJoint

open ActualFiniteLaw
open ActualOriginalOrderedPaddingLaw
open ActualOriginalPostPaddingVerifier
open ActualHonestTaggedTransport
open ActualTaggedFixedCenterGeometry
open ActualTaggedConcreteStarLaw
open ActualOccurrenceAllocation
open ActualStarQuestionSupport
open ActualStarSpanIntersection
open ActualQuestionMassBridge
open ActualTaggedOrderedQuestionSourceBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : Instance N m) (copies J : Nat)
local instance (I : Instance N m) : DecidableEq I.RowId := Classical.decEq _
local instance (I : Instance N m) : DecidableEq I.GlobalVar := inferInstance

def BadRow (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (e : TaggedRow I copies) : Prop :=
  f (equationVector (taggedSource I copies).support e) ≠
    (taggedSource I copies).rhs e

def badRows (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    Finset (TaggedRow I copies) :=
  Finset.univ.filter (BadRow I copies f)

/-- Exact positive-error assignment premise on the copied 3-Lin source. Its
existence from the encoded outer YES contract remains a separate obligation. -/
def PositiveErrorAssignment
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) (ε₁ : ℚ) : Prop :=
  ((badRows I copies f).card : ℚ) ≤
    ε₁ * Fintype.card (TaggedRow I copies)

def badOriginalRaw
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    Finset (RawOrdered I copies J) :=
  Finset.univ.filter (fun u => ∃ j : Fin J, BadRow I copies f (u j))

def badOriginalU
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    Finset (OriginalU I copies J) :=
  Finset.univ.filter (fun U => ∃ e ∈ U.rows, BadRow I copies f e)

def orderedToOriginalU (u : TaggedOrderedGood I copies J) :
    OriginalU I copies J :=
  (originalUEquiv I copies J).symm (orderedToGoodU I copies J u)

theorem badOriginalU_iff_ordered
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (u : TaggedOrderedGood I copies J) :
    (⟨(orderedToGoodU I copies J u).1,
      (orderedToGoodU I copies J u).2.1,
      (orderedToGoodU I copies J u).2.2⟩ : OriginalU I copies J) ∈
        badOriginalU I copies J f ↔
      ∃ j : Fin J, BadRow I copies f (u.1 j) := by
  classical
  simp only [badOriginalU, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hbad⟩
    rcases Finset.mem_image.mp he with ⟨j, _, hj⟩
    exact ⟨j, by simpa [hj] using hbad⟩
  · rintro ⟨j, hj⟩
    exact ⟨u.1 j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩

theorem orderedToOriginalU_tagged (u : TaggedOrderedGood I copies J) :
    (orderedToOriginalU I copies J u).toTagged I copies =
      orderedToGoodU I copies J u := by
  rfl

theorem badOriginalU_ordered_iff
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (u : TaggedOrderedGood I copies J) :
    orderedToOriginalU I copies J u ∈ badOriginalU I copies J f ↔
      ∃ j : Fin J, BadRow I copies f (u.1 j) := by
  exact badOriginalU_iff_ordered I copies J f u

theorem orderedToOriginalU_pushforward {t h k : Nat}
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    pushforward (orderedToOriginalU I copies J)
      (orderedGoodLaw I copies J) =
    pushforward (fun x : OriginalDraw I copies J t h k => x.U)
      (originalLawFromTagged I copies hcenter hleaf) := by
  classical
  apply FiniteLaw.ext
  intro U
  rw [pushforward_apply]
  have hiff (u : TaggedOrderedGood I copies J) :
      orderedToOriginalU I copies J u = U ↔
        orderedToGoodU I copies J u = U.toTagged I copies := by
    constructor
    · intro hu
      rw [← orderedToOriginalU_tagged I copies J u, hu]
    · intro hu
      apply (originalUEquiv I copies J).injective
      change (orderedToOriginalU I copies J u).toTagged I copies =
        U.toTagged I copies
      exact (orderedToOriginalU_tagged I copies J u).trans hu
  calc
    (∑ u : TaggedOrderedGood I copies J,
      if orderedToOriginalU I copies J u = U then
        (orderedGoodLaw I copies J).mass u else 0) =
      ∑ u : TaggedOrderedGood I copies J,
        if orderedToGoodU I copies J u = U.toTagged I copies then
          (orderedGoodLaw I copies J).mass u else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            simp only [hiff u]
    _ = ∑ u : TaggedOrderedGood I copies J,
        if orderedToGoodU I copies J u = U.toTagged I copies then
          (uniformLaw (RawOrdered I copies J)).mass u.1 /
            eventMass (uniformLaw (RawOrdered I copies J))
              (legitimate I copies J) else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            split_ifs
            · exact (conditioned_ordered_point I copies J u).symm
            · rfl
    _ = (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
        (originalLawFromTagged I copies hcenter hleaf)).mass U :=
          (conditional_raw_eq_originalDraw_U I copies J hcenter hleaf U)

theorem eligible_bad_image
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    (preimageEvent (orderedToOriginalU I copies J)
      (badOriginalU I copies J f)).image
        (fun u : TaggedOrderedGood I copies J => u.1) =
      legitimate I copies J ∩ badOriginalRaw I copies J f := by
  classical
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨u, hu, hq⟩
    subst q
    have hbad : ∃ j : Fin J, BadRow I copies f (u.1 j) :=
      (badOriginalU_ordered_iff I copies J f u).mp
        (Finset.mem_filter.mp hu).2
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
  · intro hq
    have hg := (Finset.mem_inter.mp hq).1
    have hb := (Finset.mem_inter.mp hq).2
    rcases Finset.mem_image.mp hg with ⟨u, _, hq⟩
    subst q
    have hbad : ∃ j : Fin J, BadRow I copies f (u.1 j) :=
      (Finset.mem_filter.mp hb).2
    apply Finset.mem_image.mpr
    refine ⟨u, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (badOriginalU_ordered_iff I copies J f u).mpr hbad⟩

theorem conditioned_badU_joint_eq_raw
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    eventMass
        (pushforward (orderedToOriginalU I copies J)
          (orderedGoodLaw I copies J))
        (badOriginalU I copies J f) *
      eventMass (uniformLaw (RawOrdered I copies J))
        (legitimate I copies J) =
      eventMass (uniformLaw (RawOrdered I copies J))
        (legitimate I copies J ∩ badOriginalRaw I copies J f) := by
  classical
  let S := preimageEvent (orderedToOriginalU I copies J)
    (badOriginalU I copies J f)
  let R := legitimate I copies J ∩ badOriginalRaw I copies J f
  have hcard : S.card = R.card := by
    have himage : S.image (fun u : TaggedOrderedGood I copies J => u.1) = R :=
      eligible_bad_image I copies J f
    rw [← himage, Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hgood : (Fintype.card (TaggedOrderedGood I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedOrderedGood I copies J) ≠ 0)
  have hraw : (Fintype.card (RawOrdered I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (RawOrdered I copies J) ≠ 0)
  rw [eventMass_pushforward]
  have hS : eventMass (orderedGoodLaw I copies J) S =
      (S.card : ℚ) / Fintype.card (TaggedOrderedGood I copies J) := by
    simp [eventMass, orderedGoodLaw, uniformLaw_apply, div_eq_mul_inv]
  have hR : eventMass (uniformLaw (RawOrdered I copies J)) R =
      (R.card : ℚ) / Fintype.card (RawOrdered I copies J) := by
    simp [eventMass, uniformLaw_apply, div_eq_mul_inv]
  change eventMass (orderedGoodLaw I copies J) S *
      eventMass (uniformLaw (RawOrdered I copies J))
        (legitimate I copies J) =
      eventMass (uniformLaw (RawOrdered I copies J)) R
  rw [hS, raw_legitimate_mass I copies J, hR]
  rw [hcard]
  field_simp

private theorem sum_eval_rat {E : Type*} [Fintype E] [DecidableEq E]
    (j : Fin J) (g : E → ℚ) :
    (∑ u : Fin J → E, g (u j)) =
      (Fintype.card E : ℚ) ^ (J - 1) * ∑ e : E, g e := by
  have hr := sum_eval_eq_card_pow_mul_sum j (fun e : E => (g e : ℝ))
  exact_mod_cast hr

theorem originalRejects_implies_badU {t h k : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (x : OriginalDraw I copies J t h k)
    (hreject : ¬ originalAccepts I copies
      (honestOriginalAssignment I copies f) x) :
    ∃ e ∈ x.U.rows, BadRow I copies f e := by
  classical
  by_contra hn
  push Not at hn
  apply hreject
  exact honestOriginalAccepts_of_goodU I copies f x (by
    intro e he
    exact not_not.mp (hn e he))

theorem originalRejectMass_le_badU {t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    eventMass (originalLawFromTagged I copies hcenter hleaf)
      (Finset.univ.filter (fun x : OriginalDraw I copies J t h k =>
        ¬ originalAccepts I copies (honestOriginalAssignment I copies f) x)) ≤
      eventMass
        (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
          (originalLawFromTagged I copies hcenter hleaf))
        (badOriginalU I copies J f) := by
  classical
  rw [eventMass_pushforward]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    have hre : ¬ originalAccepts I copies
        (honestOriginalAssignment I copies f) x :=
      (Finset.mem_filter.mp hx).2
    obtain ⟨e, he, hbad⟩ := originalRejects_implies_badU I copies J f x hre
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, hbad⟩⟩
  · intro x _ _
    exact (originalLawFromTagged I copies hcenter hleaf).nonneg x

/-- The source occurrence-level error budget implies the *joint* bound
needed for the original block, before conditioning on the eligible rows. -/
theorem raw_original_joint_le
    [Nonempty (RawOrdered I copies J)]
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (ε₁ : ℚ) (_hε : 0 ≤ ε₁)
    (hrow : 0 < Fintype.card (TaggedRow I copies))
    (herror : PositiveErrorAssignment I copies f ε₁) :
    eventMass (uniformLaw (RawOrdered I copies J))
      (legitimate I copies J ∩ badOriginalRaw I copies J f) ≤
      (J : ℚ) * ε₁ := by
  classical
  let E := TaggedRow I copies
  let μ := uniformLaw (RawOrdered I copies J)
  let countBad : ℚ := (badRows I copies f).card
  have hrowQ : (0 : ℚ) < Fintype.card E := by exact_mod_cast hrow
  have hcountRows :
      (∑ e : E, if BadRow I copies f e then (1 : ℚ) else 0) = countBad := by
    simp only [← Finset.sum_filter]
    simp [countBad, badRows]
  have hpoint (u : RawOrdered I copies J) :
      (if ∃ j : Fin J, BadRow I copies f (u j) then (1 : ℚ) else 0) ≤
        ∑ j : Fin J, if BadRow I copies f (u j) then (1 : ℚ) else 0 := by
    by_cases hb : ∃ j : Fin J, BadRow I copies f (u j)
    · simp only [hb, if_true]
      obtain ⟨j, hj⟩ := hb
      have hsingle : (1 : ℚ) ≤
          ∑ i : Fin J, if BadRow I copies f (u i) then (1 : ℚ) else 0 := by
        simpa [hj] using (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin J)))
          (f := fun i => if BadRow I copies f (u i) then (1 : ℚ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j))
      exact hsingle
    · simp only [hb, if_false]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have hcoord (j : Fin J) :
      (∑ u : RawOrdered I copies J,
        if BadRow I copies f (u j) then (1 : ℚ) else 0) =
      (Fintype.card E : ℚ) ^ (J - 1) * countBad := by
    simpa only [RawOrdered, E, hcountRows] using
      sum_eval_rat (J := J) j
        (fun e : E => if BadRow I copies f e then (1 : ℚ) else 0)
  have hcount :
      (∑ u : RawOrdered I copies J,
        if ∃ j : Fin J, BadRow I copies f (u j) then (1 : ℚ) else 0) ≤
      (J : ℚ) * ((Fintype.card E : ℚ) ^ (J - 1) * countBad) := by
    calc
      _ ≤ ∑ u : RawOrdered I copies J,
            ∑ j : Fin J, if BadRow I copies f (u j) then (1 : ℚ) else 0 :=
          Finset.sum_le_sum (fun u _ => hpoint u)
      _ = ∑ j : Fin J,
            ∑ u : RawOrdered I copies J,
              if BadRow I copies f (u j) then (1 : ℚ) else 0 := Finset.sum_comm
      _ = _ := by simp [hcoord]
  have hsubset :
      eventMass μ (legitimate I copies J ∩ badOriginalRaw I copies J f) ≤
      eventMass μ (badOriginalRaw I copies J f) := by
    unfold eventMass
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intro u _ _
    exact μ.nonneg u
  have hbadMass :
      eventMass μ (badOriginalRaw I copies J f) =
        (∑ u : RawOrdered I copies J,
          if ∃ j : Fin J, BadRow I copies f (u j) then (1 : ℚ) else 0) /
            Fintype.card (RawOrdered I copies J) := by
    simp [eventMass, badOriginalRaw, μ, uniformLaw_apply, div_eq_mul_inv]
  by_cases hJ : J = 0
  · subst J
    have hzero : badOriginalRaw I copies 0 f = ∅ := by
      ext u
      simp [badOriginalRaw]
    simp [hzero, eventMass, μ] at hsubset ⊢
  · have hcard : (Fintype.card (RawOrdered I copies J) : ℚ) =
        (Fintype.card E : ℚ) ^ J := by
        simp [RawOrdered, E, Fintype.card_fin]
    have hpow : (Fintype.card E : ℚ) ^ J =
        (Fintype.card E : ℚ) ^ (J - 1) * Fintype.card E := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ)]
    have hden : (0 : ℚ) < (Fintype.card E : ℚ) ^ J := pow_pos hrowQ _
    calc
      eventMass μ (legitimate I copies J ∩ badOriginalRaw I copies J f) ≤
          eventMass μ (badOriginalRaw I copies J f) := hsubset
      _ = (∑ u : RawOrdered I copies J,
          if ∃ j : Fin J, BadRow I copies f (u j) then (1 : ℚ) else 0) /
            ((Fintype.card E : ℚ) ^ J) := by rw [hbadMass, hcard]
      _ ≤ (J : ℚ) * (((Fintype.card E : ℚ) ^ (J - 1)) * countBad) /
            ((Fintype.card E : ℚ) ^ J) :=
          div_le_div_of_nonneg_right hcount hden.le
      _ = (J : ℚ) * (countBad / Fintype.card E) := by
          rw [hpow]
          field_simp
      _ ≤ (J : ℚ) * ε₁ := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J)
          exact (div_le_iff₀ hrowQ).2 herror

/-- The actual original block has the manuscript's joint numerator bound:
the post-padding draw's rejection probability is multiplied by the *raw*
legitimate-question mass. The full joint `m+1` draw still needs resampling
marginals before this can be passed to `conditioned_yes_failure_le`. -/
theorem original_block_joint_rejection_le {t h k : Nat}
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (ε₁ : ℚ) (hε : 0 ≤ ε₁)
    (hrow : 0 < Fintype.card (TaggedRow I copies))
    (herror : PositiveErrorAssignment I copies f ε₁) :
    eventMass (originalLawFromTagged I copies hcenter hleaf)
        (Finset.univ.filter (fun x : OriginalDraw I copies J t h k =>
          ¬ originalAccepts I copies
            (honestOriginalAssignment I copies f) x)) *
      eventMass (uniformLaw (RawOrdered I copies J))
        (legitimate I copies J) ≤ (J : ℚ) * ε₁ := by
  let μraw := uniformLaw (RawOrdered I copies J)
  let μdraw := originalLawFromTagged I copies (k := k) hcenter hleaf
  let rawLegit := eventMass μraw (legitimate I copies J)
  have hden : 0 ≤ rawLegit := by
    unfold rawLegit eventMass
    exact Finset.sum_nonneg (fun u _ => μraw.nonneg u)
  have hreject := originalRejectMass_le_badU I copies J (k := k)
    hcenter hleaf f
  have hpush := orderedToOriginalU_pushforward I copies J (k := k)
    hcenter hleaf
  have heq := conditioned_badU_joint_eq_raw I copies J f
  rw [hpush] at heq
  calc
    eventMass μdraw
        (Finset.univ.filter (fun x : OriginalDraw I copies J t h k =>
          ¬ originalAccepts I copies
            (honestOriginalAssignment I copies f) x)) * rawLegit ≤
      eventMass (pushforward (fun x : OriginalDraw I copies J t h k => x.U)
        μdraw) (badOriginalU I copies J f) * rawLegit :=
          mul_le_mul_of_nonneg_right hreject hden
    _ = eventMass μraw
        (legitimate I copies J ∩ badOriginalRaw I copies J f) := heq
    _ ≤ (J : ℚ) * ε₁ :=
      raw_original_joint_le I copies J f ε₁ hε hrow herror

end
end PvNP.RealizableHardness.ActualOriginalBlockYesJoint
