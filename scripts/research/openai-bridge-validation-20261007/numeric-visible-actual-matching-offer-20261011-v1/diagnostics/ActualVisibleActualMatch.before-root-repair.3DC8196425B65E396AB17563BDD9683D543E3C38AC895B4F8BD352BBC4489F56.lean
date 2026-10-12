import PvNP.RealizableHardness.ActualVisibleAmbientLadder
import PvNP.RealizableHardness.ActualVisibleListStrategy
import PvNP.RealizableHardness.ActualVisibleOutputTransport
import PvNP.RealizableHardness.ActualRestrictedVisiblePair
import PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance
import PvNP.RealizableHardness.ActualRandomExtensionSuccess
import PvNP.RealizableHardness.SubmoduleFunctionalGluing

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
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

variable {E B : Type*}
variable [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]

abbrev OriginalCoord {N rows J : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat) (U : TaggedGoodU I copies J) : Type _ :=
  coordinateSpace (taggedSource I copies).support U.1

private theorem restriction_event_fiber_equiv
    (W V : Submodule (ZMod 2) E)
    (g : Module.Dual (ZMod 2) W) (f : Module.Dual (ZMod 2) V)
    (hagree : ∀ x : ↥(W ⊓ V), g ⟨x.1, x.2.1⟩ = f ⟨x.1, x.2.2⟩) :
    restrictionSuccessEvent W V g f ≃
      FunctionalExtensionFiber (W ⊔ V)
        (Classical.choose (existsUnique_glue_on_sup W V g f hagree)) := by
  classical
  obtain ⟨glue, hglueW, hglueV, hglueUnique⟩ :=
    existsUnique_glue_on_sup W V g f hagree
  let toSup : restrictionSuccessEvent W V g f →
      FunctionalExtensionFiber (W ⊔ V) glue := fun F => by
    refine ⟨F.1.1, ?_⟩
    apply hglueUnique (F.1.1.comp (W ⊔ V).subtype)
    constructor
    · ext x
      have hx := LinearMap.congr_fun F.1.2 ⟨x, le_sup_left x.property⟩
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
    left_inv := by intro F; apply Subtype.ext; rfl
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
  have hdim : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) W =
      (Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (W ⊔ V)) +
        (Module.finrank (ZMod 2) (W ⊔ V) - Module.finrank (ZMod 2) W) := by
    have hW : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (W ⊔ V) :=
      Submodule.finrank_mono le_sup_left
    have hS : Module.finrank (ZMod 2) (W ⊔ V) ≤ Module.finrank (ZMod 2) E :=
      Submodule.finrank_mono le_top
    omega
  have hcod : codim (W.comap V.subtype) =
      Module.finrank (ZMod 2) (W ⊔ V) - Module.finrank (ZMod 2) W := by
    unfold codim
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W V
    have hinf : (W ⊓ V).comap V.subtype = W.comap V.subtype := by
      ext x
      simp [Submodule.mem_inf]
    rw [hinf] at hsum
    omega
  unfold eventMass ambientExtensionLaw
  simp only [uniformLaw_apply, Finset.sum_const, nsmul_eq_mul]
  rw [hcard, htotal, hdim, hcod, pow_add]
  field_simp
  ring

/-- Codimension cannot increase when W is restricted to V, relative to the
original ambient codimension. -/
theorem intersection_codim_le_original
    (W V : Submodule (ZMod 2) E) :
    codim (W.comap V.subtype) ≤ codim W := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W V
  have hinf : (W ⊓ V).comap V.subtype = W.comap V.subtype := by
    ext x
    simp [Submodule.mem_inf]
  have hW : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) E := W.finrank_le
  have hS : Module.finrank (ZMod 2) (W ⊔ V) ≤ Module.finrank (ZMod 2) E :=
    Submodule.finrank_mono le_top
  unfold codim
  rw [hinf]
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
  unfold codim actualVisibleRestrictedPair pushPair pushGrass
  rw [(retainedVisibleEquiv I copies J U s).finrank_map_eq]
  rw [(retainedVisible_finrank I copies J U s).symm]

/-- Actual fixed-draw matching bound. The start threshold is obtained from
restrictedPair's actual agreement-loss bound and transported exactly to the
visible global table. Only the actual list cardinal appears in the denominator. -/
theorem actual_visible_matching_bound
    {N rows J a h r Tcut : Nat} {I : ActualOccurrenceAllocation.Instance N rows}
    {copies : Nat} {U : TaggedGoodU I copies J}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (draw : ActualRowDraw I copies U)
    (Q : Grass (OriginalCoord I copies U) a) (P : DecodedPair Q (2 * h))
    (hQV : Q.val ≤ actualRetained I copies U draw)
    (hc : codim P.W ≤ r)
    (hdrop : dropCount (rowDrawEquiv I copies U draw) ≤ Tcut)
    (hQH : Q.val ⊓ originalSideSpace I copies U = ⊥)
    (hQ0 : Q.val ⊓ visibleSideSpace I copies U
      (retainedVariables I copies J U draw)
      (retainedVariables_reachable I copies J U draw) = ⊥)
    (had : a ≤ 2 * h) (hbd : 1 ≤ 2 * h - a)
    (hslack : J + 2 * h + 1 ≤ 3 * J - 2 * Tcut - r)
    (C : Rat) (hC : 0 < C)
    (hthreshold : C / 4 ≤
      agreement (totalHLeafTable I copies U Traw choice) Q
        (restrictedPair I copies U Q P draw hQV) -
        2 / (2 : Rat) ^ (2 * J - 2 * Tcut - 2 * h - r - 1)) :
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
  have hloss := actual_restricted_visible_agreement_lower
    I copies J U Traw choice Q P draw hQV hc hdrop hQH hQ0 had hbd hslack
  have htransport := actual_visible_agreement_eq_retained
    I copies J U Traw choice draw Q P hQV
  have hstart : C / 4 ≤ agreement Tvis Qvis Pvis := by
    dsimp [Tvis, Qvis, Pvis]
    rw [htransport]
    exact hthreshold.trans hloss
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
  have hnonneg (μ : FiniteLaw (Module.Dual (ZMod 2) (actualRetained I copies U draw))) (S : Finset (Module.Dual (ZMod 2) (actualRetained I copies U draw))) : 0 ≤ eventMass μ S := Finset.sum_nonneg (fun f _ => μ.nonneg f)
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
                ⟨⟨x.1, x.2.2⟩, x.2⟩ := rfl
          _ = Pvis.g
              ((retainedVisibleEquiv I copies J U draw).submoduleMap
                (actualRetainedRestrictedPair I copies J U draw Q P hQV).W y) := hp.symm
          _ = f ((Pvis.W).subtype
              ((retainedVisibleEquiv I copies J U draw).submoduleMap
                (actualRetainedRestrictedPair I copies J U draw Q P hQV).W y)) := hcomp.symm
          _ = (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap)
              ⟨x.1, x.2.2⟩ := by rfl
      exact mul_le_mul_of_nonneg_left
        (restriction_success_mass_eq_intersection_codim P.W
          (actualRetained I copies U draw) P.g
          (f.comp (retainedVisibleEquiv I copies J U draw).toLinearMap) hgeom |>.trans_le
            (by
              apply one_div_le_one_div_of_le
              · positivity
              · exact pow_le_pow_right₀ (by norm_num) hcodimV))
        (ν.nonneg f)
    apply hsub.trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro f _ _
    exact mul_nonneg (ν.nonneg f)
      (hnonneg (ambientExtensionLaw P.W P.g)
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
  retained_functional_restriction_iff_assignment_agreement I copies J U s f g

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
    I copies J U e r T choice Q hfav
end
end PvNP.RealizableHardness.ActualVisibleActualMatch
