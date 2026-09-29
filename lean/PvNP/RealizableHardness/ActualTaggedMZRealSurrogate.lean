import PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
import PvNP.RealizableHardness.ActualTaggedMZThresholdArithmetic

/-! Rational surrogate thresholds for nonintegral manuscript exponents.
The finite tagged test has rational mass; the decoder threshold has a real
exponent. A lower integer exponent for `S` and upper integer exponent for
`Δ` make the rational conclusion stronger than the real threshold. -/

namespace PvNP.RealizableHardness.ActualTaggedMZRealSurrogate

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedFixedUDensityForce
open PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The required rational exponent witnesses exist whenever the real
manuscript exponents are nonnegative. -/
theorem surrogate_exponents_exist (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    ∃ p q : Nat, (p : ℝ) ≤ P ∧ P ≤ p + 1 ∧
      Q ≤ q ∧ (q : ℝ) ≤ Q + 1 := by
  refine ⟨⌊P⌋₊, ⌈Q⌉₊, Nat.floor_le hP,
    (Nat.lt_floor_add_one P).le, Nat.le_ceil Q, ?_⟩
  exact (Nat.ceil_lt_add_one hQ).le

/-- The exact floor/ceiling witness inequalities needed to retain the
collision margin. Existence of these integer witnesses is separate. -/
theorem surrogate_exponent_gap {p q J : Nat} {P Q : ℝ}
    (hqlo : Q ≤ q) (hqhi : (q : ℝ) ≤ Q + 1)
    (hplo : (p : ℝ) ≤ P) (hphi : P ≤ p + 1)
    (hgap : Q + 8 ≤ P) (hJ : P ≤ J) :
    q + 6 ≤ p ∧ p ≤ J := by
  constructor
  · exact_mod_cast (show (q : ℝ) + 6 ≤ p by linarith)
  · exact_mod_cast (show (p : ℝ) ≤ J by linarith)

theorem surrogate_real_density_le_rational {p : Nat} {P : ℝ}
    (hplo : (p : ℝ) ≤ P) :
    8 * (1 / 2 : ℝ) ^ P ≤ (8 * (1 / 2 : ℚ) ^ p : ℚ) := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hplo
  rw [Real.rpow_natCast] at h
  have hcast : ((8 * (1 / 2 : ℚ) ^ p : ℚ) : ℝ) =
      8 * (1 / 2 : ℝ) ^ p := by
    norm_num [Rat.cast_mul, Rat.cast_pow, Rat.cast_div]
  rw [hcast]
  nlinarith

theorem surrogate_rational_value_le_real {q : Nat} {Q : ℝ}
    (hqlo : Q ≤ q) :
    ((1 / 2 : ℚ) ^ q : ℝ) ≤ (1 / 2 : ℝ) ^ Q := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hqlo
  rw [Real.rpow_natCast] at h
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

/-- For every fixed arbitrary table, a composed tagged score above the
real manuscript `Δ` forces a single predraw table and rational threshold
mass at least `8·2⁻ᵖ`. This rational threshold dominates real `8S`.
The floor/ceiling witness bounds are explicit assumptions. -/
theorem composedScore_realThreshold_forces_rational_MZ_U
    {J t h k p q : Nat} {P Q : ℝ}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (hqlo : Q ≤ q) (hqhi : (q : ℝ) ≤ Q + 1)
    (hplo : (p : ℝ) ≤ P) (hphi : P ≤ p + 1)
    (hgap : Q + 8 ≤ P) (hJ : P ≤ J)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (hscore : (1 / 2 : ℝ) ^ Q <
      (composedTaggedScore I copies (k := k) hcenter hleaf C T : ℝ)) :
    ∃ T' : TaggedLeafTable I copies,
      8 * (1 / 2 : ℚ) ^ p ≤
        ∑ U : TaggedGoodU I copies J,
          (uniformLaw (TaggedGoodU I copies J)).mass U *
            (if 8 * (1 / 2 : ℚ) ^ p ≤
              conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U
             then (1 : ℚ) else 0) := by
  obtain ⟨hgapNat, hpJ⟩ := surrogate_exponent_gap hqlo hqhi hplo hphi hgap hJ
  have hscoreRat : (1 / 2 : ℚ) ^ q <
      composedTaggedScore I copies (k := k) hcenter hleaf C T := by
    have hq := surrogate_rational_value_le_real hqlo
    exact_mod_cast lt_of_le_of_lt hq hscore
  have hphysical : (1 / 2 : ℚ) ^ (q + 1) ≤
      taggedPhysicalMass I copies
        (orderedStarLaw I copies J (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T := by
    rw [← composedTaggedScore_eq_orderedPhysicalMass I copies
      hcenter hleaf C T]
    rw [pow_add]
    norm_num
    have hnonneg : 0 ≤ (1 / 2 : ℚ) ^ q := by positivity
    linarith
  exact ordered_half_value_forces_MZ_threshold_U I copies hcenter hleaf
    ht hh hexp hk hgapNat hpJ C T hphysical

end
end PvNP.RealizableHardness.ActualTaggedMZRealSurrogate
