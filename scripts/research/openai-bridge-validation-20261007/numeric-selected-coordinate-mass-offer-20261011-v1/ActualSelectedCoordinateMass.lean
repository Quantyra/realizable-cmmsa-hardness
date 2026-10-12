import PvNP.RealizableHardness.ActualFixedScoreVisibleApplication
import PvNP.RealizableHardness.ActualOriginalDecoderSelection
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.ActualGlobalSelectedDensity

/-! Original favorable advice mass in the actual row frame, followed by
one dimension selected across the original good-question law. This does
not yet identify the game acceptance score. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualSelectedCoordinateMass

open scoped BigOperators
open ActualFixedScoreConditionalAgreement ActualFixedScoreVisibleApplication
open ActualOriginalDecoderSelection ActualTaggedRowDeletion
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedSelectedDecoderBridge ActualTaggedMZSideDraw
open ActualNumericSourceHeight ActualNumericExplicitHeight ActualNumericRobustReal
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualStarAcceptedGoodMass ActualStarFixedRhoDimensionGuard
open ActualFiniteLaw GrassmannCounting GrassmannIncidence
open ActualGlobalSelectedDensity ActualTaggedOrderedQuestionSourceBridge
open ActualTaggedOrderedFullLawForce ActualTaggedFixedTableAcceptance
open ActualTaggedPresentedSelection ActualTaggedFixedUDensityForce
open TripleRestrictionRank PosteriorDensity PosteriorReweighting SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat)

/-- Reindex the whole uniform advice law, with the same favorable predicate
and original selected table. The zero convention needs no dimension guard. -/
theorem selected_coordinate_mass_eq_original {J a h : Nat}
    (U : TaggedGoodU I copies J) (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) :
    mass (ambientMass : Advice J a → ℚ)
      (selectedCoordinateFavorable I copies U e r T choice) =
    mass (originalAdviceMass I copies U :
        Grass (ActualCoordinateSpace I copies U) a → ℚ)
      (favorable I copies U e r T choice) := by
  let phi := actualRowGrassEquiv I copies U a
  have hcard := Fintype.card_congr phi
  unfold mass
  apply Fintype.sum_equiv phi.symm
  intro Q
  simp only [selectedCoordinateFavorable, ambientMass, originalAdviceMass,
    one_div, hcard]

/-- The selected original decoder supplies its actual mass in the precise
coordinate law consumed by the posterior application. -/
theorem selected_coordinate_decoder_mass {L m A : Nat}
    (base : Nat → Nat) (cutoff : ℝ → Nat) (hA : 1 ≤ A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (U : TaggedGoodU I copies (blocks A (hBlock L m)))
    (center : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies (blocks A (hBlock L m)) (hBlock L m))
    (choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m))
    (hside : 8 * successMargin (badExponent m (hBlock L m)) ≤
      sideConditionalDensity I copies U (leafT m (hBlock L m))
        (hBlock L m) m center (taggedSelectedDomainTable I copies T choice)) :
    ∃ a : Fin (numericRankThreshold m + 1),
      (1 : ℚ) / (2 : ℚ) ^ (6 * (hBlock L m) ^ 2) ≤
        mass (ambientMass : Advice (blocks A (hBlock L m)) a.val → ℚ)
          (selectedCoordinateFavorable I copies U
            (refreshThreshold m (hBlock L m)) (numericRankThreshold m) T choice) := by
  obtain ⟨a, ha⟩ := selected_original_decoder_mass
    I copies base cutoff hA hsel U center T choice hside
  refine ⟨a, ?_⟩
  rw [selected_coordinate_mass_eq_original]
  exact ha

/-- The dimension is fixed after averaging over all original good questions.
Only the actual high-side-density event contributes the lower bound; the
same raw table and representative choice are used for every question. -/
theorem selected_coordinate_global_dimension {L m A : Nat}
    (base : Nat → Nat) (cutoff : ℝ → Nat) (hA : 1 ≤ A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I copies (blocks A (hBlock L m)))]
    (center : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies (blocks A (hBlock L m)) (hBlock L m))
    (choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m)) :
    ∃ a : Fin (numericRankThreshold m + 1),
      ((1 : ℚ) / (2 : ℚ) ^ (6 * (hBlock L m) ^ 2) /
          (numericRankThreshold m + 1)) *
        (∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
          (uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U *
            (if 8 * successMargin (badExponent m (hBlock L m)) ≤
              sideConditionalDensity I copies U (leafT m (hBlock L m))
                (hBlock L m) m center (taggedSelectedDomainTable I copies T choice)
              then (1 : ℚ) else 0)) ≤
      ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
        (uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U *
          mass (ambientMass : Advice (blocks A (hBlock L m)) a.val → ℚ)
            (selectedCoordinateFavorable I copies U
              (refreshThreshold m (hBlock L m)) (numericRankThreshold m) T choice) := by
  classical
  let mu := uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))
  let D : ℚ := 1 / (2 : ℚ) ^ (6 * (hBlock L m) ^ 2)
  let high : TaggedGoodU I copies (blocks A (hBlock L m)) → Prop := fun U =>
    8 * successMargin (badExponent m (hBlock L m)) ≤
      sideConditionalDensity I copies U (leafT m (hBlock L m))
        (hBlock L m) m center (taggedSelectedDomainTable I copies T choice)
  let F : TaggedGoodU I copies (blocks A (hBlock L m)) →
      Fin (numericRankThreshold m + 1) → ℚ := fun U a =>
    mass (ambientMass : Advice (blocks A (hBlock L m)) a.val → ℚ)
      (selectedCoordinateFavorable I copies U
        (refreshThreshold m (hBlock L m)) (numericRankThreshold m) T choice)
  have hF (U) (a) : 0 ≤ F U a := by
    unfold F mass
    apply Finset.sum_nonneg
    intro Q _
    split
    · unfold ambientMass
      positivity
    · exact le_rfl
  have hpoint (U) : D * (if high U then (1 : ℚ) else 0) ≤ ∑ a, F U a := by
    by_cases hU : high U
    · obtain ⟨a, ha⟩ := selected_coordinate_decoder_mass
        I copies base cutoff hA hsel U center T choice hU
      simp only [hU, if_true, mul_one]
      exact ha.trans (Finset.single_le_sum (fun b _ => hF U b) (Finset.mem_univ a))
    · simp only [hU, if_false, mul_zero]
      exact Finset.sum_nonneg (fun a _ => hF U a)
  let G : ℚ := ∑ U, mu.mass U * (if high U then (1 : ℚ) else 0)
  let Y : Fin (numericRankThreshold m + 1) → ℚ := fun a => ∑ U, mu.mass U * F U a
  have hsum : D * G ≤ ∑ a, Y a := by
    calc
      D * G = ∑ U, mu.mass U * (D * (if high U then (1 : ℚ) else 0)) := by
        simp only [G, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U _
        ring
      _ ≤ ∑ U, mu.mass U * (∑ a, F U a) :=
        Finset.sum_le_sum (fun U _ => mul_le_mul_of_nonneg_left (hpoint U) (mu.nonneg U))
      _ = ∑ a, Y a := by
        simp only [Y, Finset.mul_sum]
        rw [Finset.sum_comm]
  let B : ℚ := D / (numericRankThreshold m + 1) * G
  have hden : (numericRankThreshold m + 1 : ℚ) ≠ 0 := by positivity
  have havg : ∑ _a : Fin (numericRankThreshold m + 1), B ≤ ∑ a, Y a := by
    calc
      (∑ _a : Fin (numericRankThreshold m + 1), B) = D * G := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [B]
        push_cast
        field_simp [hden] <;> ring
      _ ≤ ∑ a, Y a := hsum
  obtain ⟨a, _ha, ha⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (numericRankThreshold m + 1))).Nonempty)
    havg
  exact ⟨a, ha⟩

/-- The original physical score forces one global representative choice and
one global advice dimension with quantitative actual favorable mass. -/
theorem physical_forces_global_coordinate_dimension {L m A : Nat}
    (base : Nat → Nat) (cutoff : ℝ → Nat) (hA : 1 ≤ A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    [Nonempty (TaggedGoodU I copies (blocks A (hBlock L m)))]
    (hcenter : ∀ U : TaggedGoodU I copies (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I copies (leafT m (hBlock L m)) U))
    (hleaf : ∀ (U : TaggedGoodU I copies (blocks A (hBlock L m)))
        (K : TaggedCenterOver I copies (leafT m (hBlock L m)) U),
      Nonempty (TaggedLeafOver I copies (hBlock L m) (questionOf I copies U K)))
    (ht : leafT m (hBlock L m) ≤ 2 * (hBlock L m))
    (hh : hBlock L m ≤ blocks A (hBlock L m))
    (hexp : 2 * blocks A (hBlock L m) ≤
      (2 * (hBlock L m) - leafT m (hBlock L m)) *
        (2 * blocks A (hBlock L m) - 2 * (hBlock L m)))
    (hk : m ^ 2 ≤ 2 ^ blocks A (hBlock L m))
    (center : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies (blocks A (hBlock L m)) (hBlock L m))
    (alpha : ℚ)
    (hslack : (1 / 2 : ℚ) ^ blocks A (hBlock L m) +
      16 * successMargin (badExponent m (hBlock L m)) ≤ alpha)
    (hphysical : alpha ≤ taggedPhysicalMass I copies
      (orderedStarLaw I copies (blocks A (hBlock L m))
        (t := leafT m (hBlock L m)) (h := hBlock L m) (k := m) hcenter hleaf).mass
      (sampledStar I copies (J := blocks A (hBlock L m))
        (t := leafT m (hBlock L m)) (h := hBlock L m) (k := m)) center T) :
    ∃ choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m),
      ∃ a : Fin (numericRankThreshold m + 1),
        ((1 : ℚ) / (2 : ℚ) ^ (6 * (hBlock L m) ^ 2) /
            (numericRankThreshold m + 1)) *
          (8 * successMargin (badExponent m (hBlock L m))) ≤
        ∑ U : TaggedGoodU I copies (blocks A (hBlock L m)),
          (uniformLaw (TaggedGoodU I copies (blocks A (hBlock L m)))).mass U *
            mass (ambientMass : Advice (blocks A (hBlock L m)) a.val → ℚ)
              (selectedCoordinateFavorable I copies U
                (refreshThreshold m (hBlock L m)) (numericRankThreshold m) T choice) := by
  have hS : 0 ≤ successMargin (badExponent m (hBlock L m)) := by
    unfold successMargin
    positivity
  obtain ⟨choice, hchoice⟩ := physical_forces_same_choice_side_density I copies
    hcenter hleaf ht hh hexp hk center T
    (successMargin (badExponent m (hBlock L m))) alpha hS hslack hphysical
  obtain ⟨a, ha⟩ := selected_coordinate_global_dimension
    I copies base cutoff hA hsel center T choice
  refine ⟨choice, a, ?_⟩
  exact (mul_le_mul_of_nonneg_left hchoice (by positivity)).trans ha

end
end PvNP.RealizableHardness.ActualSelectedCoordinateMass
