import PvNP.RealizableHardness.ActualResampledQuestionMarginal
import PvNP.RealizableHardness.ActualLateTauYesComposition

/-!
All `m+1` equation-block events on one declared `OriginalDraw`: its original
question and each actual class-resampled representative question. The law is
already conditioned on eligible original U. Multiplying its block mass by
raw legitimacy is a scalar identity; no common raw joint event is asserted.
-/

namespace PvNP.RealizableHardness.ActualCommonBlockYesComposition

open PvNP.RealizableHardness
open ActualFiniteLaw
open ActualOriginalPostPaddingVerifier
open ActualOriginalBlockYesJoint
open ActualOriginalOrderedPaddingLaw
open ActualResampledQuestionMarginal
open ActualLateTauYesComposition
open ActualHonestTaggedTransport
open ActualTaggedOrderedQuestionSourceBridge
open ActualTaggedFixedCenterGeometry
open ActualTaggedConcreteStarLaw
open ActualTaggedPresentedSelection
open ActualQuestionMassBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N degree : Nat} (I : ActualOccurrenceAllocation.Instance N degree)
  (copies J : Nat)

/-- The original question is coordinate zero; coordinates `i+1` are the
actual class-resampled questions already present in the same draw. -/
def blockQuestion {t h m : Nat}
    (x : OriginalDraw I copies J t h m) :
    Fin (m + 1) → OriginalU I copies J :=
  Fin.cases x.U (fun i =>
    (originalUEquiv I copies J).symm
      (presentedU I copies (x.representatives i).1))

def badBlock {t h m : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (i : Fin (m + 1)) : Finset (OriginalDraw I copies J t h m) :=
  Finset.univ.filter (fun x => blockQuestion I copies J x i ∈
    badOriginalU I copies J f)

def anyBadBlock {t h m : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    Finset (OriginalDraw I copies J t h m) :=
  badBlocks m (badBlock I copies J f)

/-- One fixed legal predraw table accepts if all source equation blocks in
the actual common draw are good. The original block suffices for this event. -/
theorem honest_accepts_of_all_good {t h m : Nat}
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (x : OriginalDraw I copies J t h m)
    (hgood : x ∉ anyBadBlock I copies J f) :
    originalAccepts I copies (honestOriginalAssignment I copies f) x := by
  apply honestOriginalAccepts_of_goodU I copies f x
  intro e he
  by_contra hbad
  apply hgood
  unfold anyBadBlock badBlocks
  apply Finset.mem_biUnion.mpr
  refine ⟨0, Finset.mem_univ _, ?_⟩
  simp only [badBlock, blockQuestion, Fin.cases_zero, badOriginalU,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, hbad⟩

/-- The all-block event is on the single declared post-padding draw. Each
coordinate's known numerator bound is summed without an independence claim. -/
theorem all_bad_blocks_scaled_le {t h m : Nat}
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (ε₁ : Rat) (hε : 0 ≤ ε₁)
    (hrow : 0 < Fintype.card (TaggedRow I copies))
    (herror : PositiveErrorAssignment I copies f ε₁) :
    eventMass (originalLawFromTagged I copies (k := m) hcenter hleaf)
        (anyBadBlock I copies J (t := t) (h := h) (m := m) f) *
      eventMass (uniformLaw (RawOrdered I copies J))
        (legitimate I copies J) ≤
      ((m + 1 : Nat) : Rat) * (J : Rat) * ε₁ := by
  let μ := originalLawFromTagged I copies (k := m) hcenter hleaf
  let q := eventMass (uniformLaw (RawOrdered I copies J))
    (legitimate I copies J)
  have hq : 0 ≤ q := by
    unfold q eventMass
    exact Finset.sum_nonneg (fun u _ => (uniformLaw (RawOrdered I copies J)).nonneg u)
  have hblock : ∀ i : Fin (m + 1),
      eventMass μ (badBlock I copies J f i) * q ≤ (J : Rat) * ε₁ := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hpush := conditioned_badU_joint_eq_raw I copies J f
      have hbound := raw_original_joint_le I copies J f ε₁ hε hrow herror
      rw [← hpush] at hbound
      have hmarg := orderedToOriginalU_pushforward I copies J (k := m)
        hcenter hleaf
      rw [hmarg] at hbound
      have hset : badBlock I copies J f (0 : Fin (m + 1)) =
          preimageEvent (fun x : OriginalDraw I copies J t h m => x.U)
            (badOriginalU I copies J f) := by
        ext x
        simp only [badBlock, preimageEvent, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      have hevent : eventMass μ (badBlock I copies J f 0) =
          eventMass (pushforward
            (fun x : OriginalDraw I copies J t h m => x.U) μ)
            (badOriginalU I copies J f) := by
        rw [hset, eventMass_pushforward]
      rw [hevent]
      exact hbound
    · have hbound := resampledU_badRow_joint_le I copies
        hcenter hleaf ht hh f ε₁ hε hrow herror j
      have hset : badBlock I copies J f (Fin.succ j) =
          preimageEvent (fun x : OriginalDraw I copies J t h m =>
            (originalUEquiv I copies J).symm
              (presentedU I copies (x.representatives j).1))
            (badOriginalU I copies J f) := by
        ext x
        simp only [badBlock, preimageEvent, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      have hevent : eventMass μ (badBlock I copies J f (Fin.succ j)) =
          eventMass (pushforward (fun x : OriginalDraw I copies J t h m =>
            (originalUEquiv I copies J).symm
              (presentedU I copies (x.representatives j).1)) μ)
            (badOriginalU I copies J f) := by
        rw [hset, eventMass_pushforward]
      rw [hevent]
      exact hbound
  have hunion := badBlocks_mass_le μ m (badBlock I copies J f)
  have hscaled := mul_le_mul_of_nonneg_right hunion hq
  calc
    eventMass μ (anyBadBlock I copies J f) * q ≤
        (∑ i : Fin (m + 1), eventMass μ (badBlock I copies J f i)) * q :=
      hscaled
    _ = ∑ i : Fin (m + 1),
        eventMass μ (badBlock I copies J f i) * q := by rw [Finset.sum_mul]
    _ ≤ ∑ _i : Fin (m + 1), (J : Rat) * ε₁ :=
      Finset.sum_le_sum (fun i _ => hblock i)
    _ = ((m + 1 : Nat) : Rat) * (J : Rat) * ε₁ := by simp [mul_assoc]

/-- Equation (21) for the declared common draw, after the late positive
outer YES error is chosen. This is conditional on the copied-row assignment
and on the actual finite fibres; no encoded outer reduction is inferred. -/
theorem common_draw_yes_failure_le {t h m : Nat}
    [Nonempty (RawOrdered I copies J)]
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hcopies : 0 < copies) (hdegree : 0 < degree) (hJ : 0 < J)
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (τ ε₁ : Rat) (hτ : 0 < τ) (hε₀ : 0 ≤ ε₁)
    (hε : ε₁ ≤ ActualConditionalTheorem1Core.outerYesError m J τ)
    (hrow : 0 < Fintype.card (TaggedRow I copies))
    (herror : PositiveErrorAssignment I copies f ε₁)
    (ha : actualTaggedBadMass I copies J ≤ 1 / 4) :
    eventMass (originalLawFromTagged I copies (k := m) hcenter hleaf)
        (Finset.univ.filter (fun x : OriginalDraw I copies J t h m =>
          ¬ originalAccepts I copies (honestOriginalAssignment I copies f) x)) ≤
      τ / 75 := by
  let μ := originalLawFromTagged I copies (k := m) hcenter hleaf
  let q := eventMass (uniformLaw (RawOrdered I copies J))
    (legitimate I copies J)
  have hqEq : q = 1 - actualTaggedBadMass I copies J :=
    raw_legitimate_mass_eq_one_sub_bad I copies J hcopies hdegree
  have hqPos : 0 < q := by rw [hqEq]; linarith
  have hscaled := all_bad_blocks_scaled_le I copies J (m := m) hcenter hleaf
    ht hh f ε₁ hε₀ hrow herror
  have hbad : eventMass μ (anyBadBlock I copies J f) ≤
      (((m + 1 : Nat) : Rat) * (J : Rat) * ε₁) / q := by
    apply (le_div_iff₀ hqPos).2
    simpa [μ, q] using hscaled
  have hnum := ActualConditionalTheorem1Core.conditioned_honest_failure_lt
    hJ hτ ha hε
  have hbad' : eventMass μ (anyBadBlock I copies J f) ≤ τ / 75 := by
    calc
      _ ≤ (((m + 1 : Nat) : Rat) * (J : Rat) * ε₁) / q := hbad
      _ = (((m + 1 : Nat) : Rat) * (J : Rat) * ε₁) /
          (1 - actualTaggedBadMass I copies J) := by rw [hqEq]
      _ ≤ τ / 75 := hnum
  have hsubset :
      Finset.univ.filter (fun x : OriginalDraw I copies J t h m =>
        ¬ originalAccepts I copies (honestOriginalAssignment I copies f) x) ⊆
      anyBadBlock I copies J f := by
    intro x hx
    have hre : ¬ originalAccepts I copies
        (honestOriginalAssignment I copies f) x := (Finset.mem_filter.mp hx).2
    by_contra hn
    exact hre (honest_accepts_of_all_good I copies J f x hn)
  have hmono : eventMass μ
      (Finset.univ.filter (fun x : OriginalDraw I copies J t h m =>
        ¬ originalAccepts I copies (honestOriginalAssignment I copies f) x)) ≤
      eventMass μ (anyBadBlock I copies J f) := by
    unfold eventMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun x _ _ => μ.nonneg x)
  exact hmono.trans hbad'

end
end ActualCommonBlockYesComposition
