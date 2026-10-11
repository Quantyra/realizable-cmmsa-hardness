import PvNP.RealizableHardness.ActualOriginalLawFullDecoderIntegration
import PvNP.RealizableHardness.ActualTaggedRowDeletion
import PvNP.RealizableHardness.PosteriorReweighting

/-! A total original-pair selection and actual favorable-advice mass.
The original table and advice determine the pair before the deletion draw.
Only favorable advice carries the asserted equation and agreement properties.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOriginalDecoderSelection
open scoped BigOperators
open PvNP.RealizableHardness
open ActualOriginalLawFullDecoderIntegration ActualTaggedRowDeletion
open ActualNumericSideExtension ActualHSideFullZoom ActualMaximalPairLadder
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedSelectedDecoderBridge ActualStarSpanIntersection
open ActualNumericRobustReal ActualNumericExplicitHeight ActualNumericSourceHeight
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualStarAcceptedGoodMass ActualTaggedComplementStarDensityBridge
open GrassmannCounting SamplerParameters PosteriorReweighting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

/-- Total default outside the favorable event, with no claimed success there. -/
def defaultPair {a d : Nat} (Q : Grass (E I copies U) a) : DecodedPair Q d where
  W := ⊤
  hQW := le_top
  g := 0

def selectedPair {a h : Nat} (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a) : DecodedPair Q (2 * h) :=
  if hf : actualFullDecoderFavorable I copies U e r T choice Q then
    Classical.choose (actualFullDecoderFavorable_exists_actualDecodedPair
      I copies U e r T choice Q hf)
  else defaultPair I copies U Q

/-- On the actual favorable event the chosen pair has the actual RHS and
full canonical-table agreement; the choice does not take a draw as input. -/
theorem selectedPair_properties {a h : Nat} (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a)
    (hf : actualFullDecoderFavorable I copies U e r T choice Q) :
    codim (selectedPair I copies U e r T choice Q).W ≤ r ∧
    ∃ hHW : H I copies U ≤ (selectedPair I copies U e r T choice Q).W,
      (selectedPair I copies U e r T choice Q).g.comp (Submodule.inclusion hHW) =
        sideCanonicalRhs I copies U ∧
      e / 3 < (agreement (totalHLeafTable I copies U T choice) Q
        (selectedPair I copies U e r T choice Q) : ℝ) := by
  unfold selectedPair
  rw [dif_pos hf]
  exact Classical.choose_spec (actualFullDecoderFavorable_exists_actualDecodedPair
    I copies U e r T choice Q hf)

def favorable {a h : Nat} (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a) : Bool :=
  decide (Q.val ⊓ H I copies U = ⊥ ∧
    actualFullDecoderFavorable I copies U e r T choice Q)

/-- The uniform original advice weights, using the zero convention on an
empty carrier. Normalization is proved below for the actual dimension guard. -/
def originalAdviceMass {a : Nat} (_Q : Grass (E I copies U) a) : ℚ :=
  1 / Fintype.card (Grass (E I copies U) a)

private theorem original_finrank : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by
  simpa [TripleRestrictionRank.Vector, TripleRestrictionRank.Coord,
    Module.finrank_pi, Nat.mul_comm] using (actualRowCoordinateEquiv I copies U).finrank_eq

theorem originalAdviceMass_normalized {a : Nat} (ha : a ≤ 3 * J) :
    ∑ Q : Grass (E I copies U) a, originalAdviceMass I copies U Q = 1 := by
  have hcard : Fintype.card (Grass (E I copies U) a) ≠ 0 := by
    rw [card_grass, original_finrank I copies U]
    exact Nat.ne_of_gt (GaussianRatio.gaussian_pos ha)
  have hcardQ : (Fintype.card (Grass (E I copies U) a) : ℚ) ≠ 0 := by exact_mod_cast hcard
  simp [originalAdviceMass, hcardQ]

/-- Actual event mass is the precise full-Grassmann ratio, with no change
to the favorable predicate or its original canonical table. -/
theorem favorable_mass_eq_ratio {a h : Nat} (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h) :
    mass (originalAdviceMass I copies U : Grass (E I copies U) a → ℚ)
      (favorable I copies U e r T choice) =
        ((Finset.univ.filter (fun Q : Grass (E I copies U) a =>
          Q.val ⊓ H I copies U = ⊥ ∧
          actualFullDecoderFavorable I copies U e r T choice Q)).card : ℚ) /
          gaussian (3 * J) a := by
  unfold mass originalAdviceMass favorable
  simp only [decide_eq_true_eq]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, one_div]
  rw [card_grass, original_finrank I copies U]
  simp only [div_eq_mul_inv]

/-- The actual original-law amplification supplies the favorable mass;
it is not an input to this theorem. -/
theorem selected_original_decoder_mass
    {L m A : Nat} (base : Nat → Nat) (cutoff : ℝ → Nat)
    (hA : 1 ≤ A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (U' : TaggedGoodU I copies (blocks A (hBlock L m)))
    (center : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies (blocks A (hBlock L m)) (hBlock L m))
    (choice : TaggedRepresentativeChoice I copies (blocks A (hBlock L m)) (hBlock L m))
    (hside : 8 * successMargin (badExponent m (hBlock L m)) ≤
      sideConditionalDensity I copies U' (leafT m (hBlock L m))
        (hBlock L m) m center (taggedSelectedDomainTable I copies T choice)) :
    ∃ a : Fin (numericRankThreshold m + 1),
      (1 : ℚ) / (2 : ℚ) ^ (6 * (hBlock L m) ^ 2) ≤
        mass (originalAdviceMass I copies U' : Grass (E I copies U') a.val → ℚ)
          (favorable I copies U' (refreshThreshold m (hBlock L m))
            (numericRankThreshold m) T choice) := by
  obtain ⟨a, ha⟩ := actual_original_law_full_decoder_probability_lower
    I copies base cutoff hA hsel U' center T choice hside
  refine ⟨a, ?_⟩
  rw [favorable_mass_eq_ratio]
  exact ha

/-- The single rational threshold is met by every actual chosen favorable
pair, preserving original-H transversality and the codimension bound. -/
theorem favorable_selectedPair_agreement {a h : Nat} (e : ℝ) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a)
    (hf : favorable I copies U e r T choice Q = true)
    (C : ℚ) (hC : (C : ℝ) < e / 3) :
    Q.val ⊓ H I copies U = ⊥ ∧
      codim (selectedPair I copies U e r T choice Q).W ≤ r ∧
      C ≤ agreement (totalHLeafTable I copies U T choice) Q
        (selectedPair I copies U e r T choice Q) := by
  have hs : Q.val ⊓ H I copies U = ⊥ ∧
      actualFullDecoderFavorable I copies U e r T choice Q := by simpa [favorable] using hf
  have hp := selectedPair_properties I copies U e r T choice Q hs.2
  obtain ⟨_hHW, _hRHS, hagree⟩ := hp.2
  refine ⟨hs.1, hp.1, ?_⟩
  have hR : (C : ℝ) ≤ (agreement (totalHLeafTable I copies U T choice) Q
      (selectedPair I copies U e r T choice Q) : ℝ) := (hC.trans hagree).le
  exact_mod_cast hR

end
end PvNP.RealizableHardness.ActualOriginalDecoderSelection
