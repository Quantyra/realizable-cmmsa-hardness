import PvNP.RealizableHardness.ActualVisibleAmbientLadder
import PvNP.RealizableHardness.ActualVisibleListStrategy
import PvNP.RealizableHardness.ActualVisibleOutputTransport
import PvNP.RealizableHardness.ActualRestrictedVisiblePair
import PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance
import PvNP.RealizableHardness.ActualRandomExtensionSuccess
import PvNP.RealizableHardness.SubmoduleFunctionalGluing
import PvNP.RealizableHardness.ActualOriginalDecoderSelection

/-! Actual visible matching after restricting the original decoder window.
This version uses codimension monotonicity for W ∩ V and does not assume
rank stability or W + V = E. Candidate source; uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisibleActualMatch

open PvNP.RealizableHardness
open ActualVisibleAmbientLadder ActualVisibleListStrategy ActualVisibleOutputTransport
open ActualRestrictedVisiblePair ActualFunctionalAssignmentAcceptance
open ActualRandomExtensionSuccess SubmoduleFunctionalGluing GrassmannCounting
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedRowDeletion ActualVisibleQuestionCompletion
open ActualFiniteLaw ActualMaximalPairLadder ActualStarAffineFunctionalSelection
open ActualOriginalLawFullDecoderIntegration ActualNumericSideExtension
open ActualVisibleLeafAgreementLoss TripleRestrictionRank
open ActualOriginalDecoderSelection
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {E : Type*}
variable [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]

local instance ambientFiniteModule : Module.Finite (ZMod 2) E := Module.Finite.of_finite

private def comapSubtypeInfEquiv (W V : Submodule (ZMod 2) E) :
    (W.comap V.subtype) ≃ₗ[ZMod 2] (W ⊓ V) where
  toFun x := ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

private theorem finite_event_nonneg {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (A : Finset Omega) : 0 ≤ eventMass mu A := by
  exact Finset.sum_nonneg (fun x _ => mu.nonneg x)

abbrev OriginalCoord {N rows J : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J) : Type _ :=
  coordinateSpace (taggedSource I copies).support U.1

private def restriction_event_fiber_equiv
    (W V : Submodule (ZMod 2) E)
    (g : Module.Dual (ZMod 2) W) (f : Module.Dual (ZMod 2) V)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    restrictionSuccessEvent W V g f ≃
      FunctionalExtensionFiber (W ⊔ V)
        (Classical.choose (existsUnique_glue_on_sup W V g f hagree)) := by
  classical
  let glue := Classical.choose (existsUnique_glue_on_sup W V g f hagree)
  have hspec := Classical.choose_spec (existsUnique_glue_on_sup W V g f hagree)
  have hglueW := hspec.1.1
  have hglueV := hspec.1.2
  have hglueUnique := hspec.2
  let toSup : restrictionSuccessEvent W V g f →
      FunctionalExtensionFiber (W ⊔ V) glue := fun F => by
    refine ⟨F.1.1, ?_⟩
    apply hglueUnique (F.1.1.comp (W ⊔ V).subtype)
    constructor
    · ext x
      have hx := LinearMap.congr_fun F.1.2 x
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.inclusion_apply] using hx
    · ext x
      have hFV := (Finset.mem_filter.mp F.2).2
      have hx := LinearMap.congr_fun hFV x
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.inclusion_apply] using hx
  let fromSup : FunctionalExtensionFiber (W ⊔ V) glue →
      restrictionSuccessEvent W V g f := fun G => by
    refine ⟨⟨G.1, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · ext x
      have hx := LinearMap.congr_fun G.2 ⟨x, le_sup_left x.property⟩
      have hy := LinearMap.congr_fun hglueW x
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.inclusion_apply] using hx.trans hy
    · ext x
      have hx := LinearMap.congr_fun G.2 ⟨x, le_sup_right x.property⟩
      have hy := LinearMap.congr_fun hglueV x
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.inclusion_apply] using hx.trans hy
  exact {
    toFun := toSup
    invFun := fromSup
    left_inv := by intro F; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro G; apply Subtype.ext; rfl }

/-- The unrestricted extension law gives a compatible visible label exact
mass 2^(-codim_V(W ∩ V)); no spanning hypothesis is required. -/
theorem restriction_success_mass_eq_intersection_codim
    (W V : Submodule (ZMod 2) E)
    (g : Module.Dual (ZMod 2) W) (f : Module.Dual (ZMod 2) V)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    eventMass (ambientExtensionLaw W g) (restrictionSuccessEvent W V g f) =
      1 / (2 : Rat) ^ codim (W.comap V.subtype) := by
  classical
  let glue : Module.Dual (ZMod 2) (W ⊔ V) :=
    Classical.choose (existsUnique_glue_on_sup W V g f hagree)
  let hEvent := restriction_event_fiber_equiv W V g f hagree
  have hcard : Fintype.card (restrictionSuccessEvent W V g f) =
      2 ^ (Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (W ⊔ V)) := by
    rw [Fintype.card_congr hEvent]
    exact functionalExtensionFiber_card (W ⊔ V) glue rfl
  have htotal := functionalExtensionFiber_card W g rfl
  have hcardSet : (restrictionSuccessEvent W V g f).card =
      2 ^ (Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (W ⊔ V)) := by
    simpa only [Fintype.card_coe] using hcard
  have hdim : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W =
      (Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (W ⊔ V)) +
        (Module.finrank (ZMod 2) (W ⊔ V) - Module.finrank (ZMod 2) W) := by
    have hW : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (W ⊔ V) :=
      Submodule.finrank_mono le_sup_left
    have hS : Module.finrank (ZMod 2) (W ⊔ V) ≤ Module.finrank (ZMod 2) E :=
      (W ⊔ V).finrank_le
    omega
  have hcod : codim (W.comap V.subtype) =
      Module.finrank (ZMod 2) (W ⊔ V) - Module.finrank (ZMod 2) W := by
    unfold codim
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W V
    rw [(comapSubtypeInfEquiv W V).finrank_eq]
    have hI : Module.finrank (ZMod 2) (W ⊓ V) ≤ Module.finrank (ZMod 2) V :=
      Submodule.finrank_mono inf_le_right
    have hW : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (W ⊔ V) :=
      Submodule.finrank_mono le_sup_left
    omega
  unfold eventMass ambientExtensionLaw
  simp only [uniformLaw_apply, Finset.sum_const, nsmul_eq_mul, hcardSet,
    htotal, Nat.cast_pow, Nat.cast_ofNat]
  rw [hdim, hcod, pow_add]
  field_simp <;> ring

/-- Codimension cannot increase when W is restricted to V, relative to the
original ambient codimension. -/
theorem intersection_codim_le_original
    (W V : Submodule (ZMod 2) E) :
    codim (W.comap V.subtype) ≤ codim W := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W V
  have hW : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) E := W.finrank_le
  have hS : Module.finrank (ZMod 2) (W ⊔ V) ≤ Module.finrank (ZMod 2) E :=
    (W ⊔ V).finrank_le
  have hI : Module.finrank (ZMod 2) (W ⊓ V) ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_mono inf_le_right
  unfold codim
  rw [(comapSubtypeInfEquiv W V).finrank_eq]
  omega

/-- The actual visible pair has the codimension of W ∩ V inside V. -/
theorem actual_visible_restricted_codim
    {N rows J : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J)
    (s : ActualRowDraw I copies U) {a d : Nat}
    (Q : Grass (OriginalCoord I copies U) a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ actualRetained I copies U s) :
    codim (actualVisibleRestrictedPair I copies J U s Q P hQV).W =
      codim ((restrictedPair I copies U Q P s hQV).W.comap
        (actualRetained I copies U s).subtype) := by
  change Module.finrank (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s)) -
      Module.finrank (ZMod 2)
        (((restrictedPair I copies U Q P s hQV).W.comap
          (actualRetained I copies U s).subtype).map
            (retainedVisibleEquiv I copies J U s).toLinearMap) = _
  rw [(retainedVisibleEquiv I copies J U s).finrank_map_eq]
  rw [(retainedVisible_finrank I copies J U s).symm]

/-- Actual fixed-draw matching bound from the literal visible agreement
already paid by the posterior step. No second side-loss charge is required. -/
theorem actual_visible_matching_bound
    {N rows J a h r : Nat} {I : ActualOccurrenceAllocation.Instance N rows}
    {copies : Nat} {U : TaggedGoodU I copies J}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (draw : ActualRowDraw I copies U)
    (Q : Grass (OriginalCoord I copies U) a) (P : DecodedPair Q (2 * h))
    (hQV : Q.val ≤ actualRetained I copies U draw)
    (hc : codim P.W ≤ r)
    (C : Rat) (hC : 0 < C)
    (hthreshold : C / 4 ≤
      agreement (visibleTableInOriginalCoordinates I copies U Traw choice
        (retainedVariables I copies J U draw)) Q
        (restrictedPair I copies U Q P draw hQV)) :
    ∃ j : Fin (r + 1),
      0 < (maximalPairList
        (actualVisibleAmbientTable I copies J U Traw choice draw)
        (pushGrass (retainedVisibleEquiv I copies J U draw)
          (retainedPreimageGrass I copies J U draw Q hQV))
        r (C / (4 * 5 ^ j.val))).card ∧
      ((1 / (maximalPairList
        (actualVisibleAmbientTable I copies J U Traw choice draw)
        (pushGrass (retainedVisibleEquiv I copies J U draw)
          (retainedPreimageGrass I copies J U draw Q hQV))
        r (C / (4 * 5 ^ j.val))).card) / (r + 1)) *
          (1 / (2 : Rat) ^ r) ≤
        extensionMatchProbability P.W (actualRetained I copies U draw) P.g
          (pushforward (fun f => f.comp
            (retainedVisibleEquiv I copies J U draw).toLinearMap)
            (visibleOutputLaw
              (actualVisibleAmbientTable I copies J U Traw choice draw)
              (pushGrass (retainedVisibleEquiv I copies J U draw)
                (retainedPreimageGrass I copies J U draw Q hQV)) r C)) := by
  let Qvis := pushGrass (retainedVisibleEquiv I copies J U draw)
    (retainedPreimageGrass I copies J U draw Q hQV)
  let Pvis := actualVisibleRestrictedPair I copies J U draw Q P hQV
  let Tvis := actualVisibleAmbientTable I copies J U Traw choice draw
  have htransport := actual_visible_agreement_eq_retained
    I copies J U Traw choice draw Q P hQV
  have hstart : C / 4 ≤ agreement Tvis Qvis Pvis := by
    dsimp [Tvis, Qvis, Pvis]
    rw [← htransport]
    exact hthreshold
  have hcomap : (restrictedPair I copies U Q P draw hQV).W.comap
      (actualRetained I copies U draw).subtype =
      P.W.comap (actualRetained I copies U draw).subtype := by
    ext x
    simp [restrictedPair, Submodule.mem_inf]
  have hcodimV : codim ((restrictedPair I copies U Q P draw hQV).W.comap
      (actualRetained I copies U draw).subtype) ≤ r := by
    rw [hcomap]
    exact (intersection_codim_le_original P.W
      (actualRetained I copies U draw)).trans hc
  have hcodimVis : codim Pvis.W ≤ r := by
    rw [actual_visible_restricted_codim I copies J U draw Q P hQV]
    exact hcodimV
  obtain ⟨j, hcard, hmass⟩ := ladder_visible_output_lower
    Tvis Qvis r C Pvis hC hcodimVis hstart
  refine ⟨j, hcard, ?_⟩
  let ν := visibleOutputLaw Tvis Qvis r C
  let A := compatibleOutputEvent Pvis
  have hsum : eventMass ν A * (1 / (2 : Rat) ^ r) ≤
      extensionMatchProbability P.W (actualRetained I copies U draw) P.g
        (pushforward (fun f => f.comp
          (retainedVisibleEquiv I copies J U draw).toLinearMap) ν) := by
    rw [extensionMatchProbability_pushforward]
    unfold eventMass
    rw [Finset.sum_mul]
    have hsub : (∑ f ∈ A, ν.mass f * (1 / (2 : Rat) ^ r)) ≤
        ∑ f ∈ A, ν.mass f *
          eventMass (ambientExtensionLaw P.W P.g)
            (restrictionSuccessEvent P.W (actualRetained I copies U draw) P.g
              (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap)) := by
      apply Finset.sum_le_sum
      intro f hf
      have hcompat : f.comp Pvis.W.subtype = Pvis.g :=
        (Finset.mem_filter.mp hf).2
      have hgeom : ∀ x : ↥(P.W ⊓ actualRetained I copies U draw),
          P.g ⟨x.1, x.2.1⟩ =
            (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap)
              ⟨x.1, x.2.2⟩ := by
        intro x
        let y : (actualRetainedRestrictedPair I copies J U draw Q P hQV).W :=
          ⟨⟨x.1, x.2.2⟩, x.2⟩
        have hp := actualVisibleRestrictedPair_preserves_functional
          I copies J U draw Q P hQV y
        have hcomp := LinearMap.congr_fun hcompat
          ((retainedVisibleEquiv I copies J U draw).submoduleMap
            (actualRetainedRestrictedPair I copies J U draw Q P hQV).W y)
        calc
          P.g ⟨x.1, x.2.1⟩ =
              (restrictedPair I copies U Q P draw hQV).g
                ⟨x.1, x.2⟩ := rfl
          _ = Pvis.g
              ((retainedVisibleEquiv I copies J U draw).submoduleMap
                (actualRetainedRestrictedPair I copies J U draw Q P hQV).W y) := hp.symm
          _ = f ((Pvis.W).subtype
              ((retainedVisibleEquiv I copies J U draw).submoduleMap
                (actualRetainedRestrictedPair I copies J U draw Q P hQV).W y)) := hcomp.symm
          _ = (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap)
              ⟨x.1, x.2.2⟩ := by rfl
      apply mul_le_mul_of_nonneg_left _ (ν.nonneg f)
      rw [restriction_success_mass_eq_intersection_codim P.W
        (actualRetained I copies U draw) P.g
        (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap) hgeom]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      exact (intersection_codim_le_original P.W
        (actualRetained I copies U draw)).trans hc
    apply hsub.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro f _ _
    exact mul_nonneg (ν.nonneg f)
      (finite_event_nonneg (ambientExtensionLaw P.W P.g)
        (restrictionSuccessEvent P.W (actualRetained I copies U draw) P.g
          (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap)))
  exact (mul_le_mul_of_nonneg_right hmass (by positivity)).trans hsum
/-- Functional equality on the retained carrier is exactly equality of the
induced assignments on retained coordinates, by the v2 finite expansion. -/
theorem retained_visible_assignment_bridge
    {N rows J : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J)
    (s : ActualRowDraw I copies U)
    (f : Module.Dual (ZMod 2) (actualRetained I copies U s))
    (g : Module.Dual (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s))) :
    f = g.comp (actualRetainedToVisible I copies U s) ↔
      ∀ x, x ∈ retainedVariables I copies J U s →
        retainedAssignment I copies U s f x =
          visibleAssignment I copies (retainedVariables I copies J U s) g x :=
  retained_functional_restriction_iff_assignment_agreement I copies U s f g

/-- The actual favorable full-decoder witness extracts the canonical RHS
restriction; every extension in that fiber accepts every tagged equation. -/
theorem favorable_decoder_RHS_equation_bridge
    {N rows J a h : Nat} {I : ActualOccurrenceAllocation.Instance N rows}
    {copies : Nat} {U : TaggedGoodU I copies J}
    (e : Real) (r : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (OriginalSpace I copies U) a)
    (hfav : actualFullDecoderFavorable I copies U e r T choice Q) :
    ∃ P : DecodedPair Q (2 * h),
      codim P.W ≤ r ∧
      ∃ hHW : OriginalH I copies U ≤ P.W,
        P.g.comp (Submodule.inclusion hHW) = sideCanonicalRhs I copies U ∧
        ∀ F : FunctionalExtensionFiber P.W P.g,
          ∀ row (hrow : row ∈ U.1),
            originalAssignment I copies U F.1
                ((taggedSource I copies).row row 0) +
            originalAssignment I copies U F.1
                ((taggedSource I copies).row row 1) +
            originalAssignment I copies U F.1
                ((taggedSource I copies).row row 2) =
              (taggedSource I copies).rhs row :=
  actual_favorable_decoder_has_equation_accepting_extensions
    I copies U e r T choice Q hfav

/-- The extension fiber is that of the SAME total selected pair used by the
posterior score. No new existential decoder is selected after the draw. -/
theorem selected_pair_equation_acceptance
    {N rows J a h : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J)
    (e : Real) (r : Nat) (T : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (OriginalSpace I copies U) a)
    (hfav : actualFullDecoderFavorable I copies U e r T choice Q)
    (F : FunctionalExtensionFiber (selectedPair I copies U e r T choice Q).W
      (selectedPair I copies U e r T choice Q).g) :
    ∀ row (hrow : row ∈ U.1),
      originalAssignment I copies U F.1 ((taggedSource I copies).row row 0) +
      originalAssignment I copies U F.1 ((taggedSource I copies).row row 1) +
      originalAssignment I copies U F.1 ((taggedSource I copies).row row 2) =
        (taggedSource I copies).rhs row := by
  obtain ⟨hHW, hRhs, _hAgree⟩ :=
    (selectedPair_properties I copies U e r T choice Q hfav).2
  exact every_original_extension_satisfies_tagged_equations I copies U
    (selectedPair I copies U e r T choice Q).W hHW
    (selectedPair I copies U e r T choice Q).g hRhs F

/-- Restricting the original functional gives exactly its original assignment
on each retained variable; totalization outside the question is irrelevant. -/
theorem retained_assignment_of_original
    {N rows J : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U)
    (F : Module.Dual (ZMod 2) (OriginalSpace I copies U))
    (x : TaggedVar I copies) (hx : x ∈ retainedVariables I copies J U s) :
    retainedAssignment I copies U s (F.comp (actualRetained I copies U s).subtype) x =
      originalAssignment I copies U F x := by
  have hxs : x ∈ OriginalSupport I copies U :=
    retainedVariables_subset_support I copies J U s hx
  simp only [retainedAssignment, originalAssignment, functionalAssignment,
    dif_pos hx, dif_pos hxs, LinearMap.comp_apply, coordinateUnitIn]
  apply congrArg F
  apply Subtype.ext
  simp [hxs]

/-- The literal functional match event is equivalent to the source game's
agreement test on retained assignments, for the original first functional. -/
theorem original_visible_assignment_agreement_iff
    {N rows J : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U)
    (F : Module.Dual (ZMod 2) (OriginalSpace I copies U))
    (g : Module.Dual (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s))) :
    F.comp (actualRetained I copies U s).subtype =
      g.comp (actualRetainedToVisible I copies U s) ↔
    ∀ x, x ∈ retainedVariables I copies J U s →
      originalAssignment I copies U F x =
        visibleAssignment I copies (retainedVariables I copies J U s) g x := by
  rw [retained_functional_restriction_iff_assignment_agreement I copies U s]
  constructor
  · intro h x hx
    have hp := h x hx
    rw [retained_assignment_of_original I copies U s F x hx] at hp
    exact hp
  · intro h x hx
    rw [retained_assignment_of_original I copies U s F x hx]
    exact h x hx
end
end PvNP.RealizableHardness.ActualVisibleActualMatch
