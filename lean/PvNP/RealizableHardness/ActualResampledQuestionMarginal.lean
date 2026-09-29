import PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier
import PvNP.RealizableHardness.ActualTaggedMZSideDraw
import PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
import PvNP.RealizableHardness.ActualTaggedYesReverseIncidence
import PvNP.RealizableHardness.ActualOriginalBlockYesJoint
import Mathlib.LinearAlgebra.LinearPMap

/-! Actual clique-resampled YES marginal and per-block numerator for Eq. (21).
The graph-pair and reverse-incidence counts identify the original draw's
presented-leaf law; its class-resampled representative yields uniform U'_i.
The final bound retains the raw legitimacy factor. The common multi-block
experiment and composed acceptance transport are separate obligations. -/

namespace PvNP.RealizableHardness.ActualResampledQuestionMarginal

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedMZSideDraw
open PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
open PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
open PvNP.RealizableHardness.ActualTaggedYesReverseIncidence
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier
open PvNP.RealizableHardness.ActualOriginalBlockYesJoint
open PvNP.RealizableHardness.ActualOriginalOrderedPaddingLaw
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

private def zeroCenter : TaggedCenterOver I copies 0 U :=
  ⟨⊥, bot_le, by simp, by simp⟩

private def baseQuestion : TaggedQuestionCenter I copies J 0 :=
  questionOf I copies U (zeroCenter I copies U)

private abbrev V := coordinateSpaceOf I copies (baseQuestion I copies U)
private abbrev H := equationInCoordinate I copies (baseQuestion I copies U)
private abbrev C := transverseComplement I copies (baseQuestion I copies U)

/- The equation space has rank J and its chosen complement has rank 2J.
For each transverse K, projection to the complement has rank t; the residual
H-component is a linear map on that projected t-plane. Conversely its graph
is a transverse K. -/
def CenterGraphPair (t : Nat) :=
  Σ G : Grass (C I copies U) t, G.val →ₗ[ZMod 2] H I copies U

noncomputable instance centerGraphMapFintype (t : Nat)
    (G : Grass (C I copies U) t) :
    Fintype (G.val →ₗ[ZMod 2] H I copies U) := by
  letI : Finite (G.val →ₗ[ZMod 2] H I copies U) :=
    Finite.of_injective
      (fun f : G.val →ₗ[ZMod 2] H I copies U => fun x => f x) (by
        intro f g hfg
        apply LinearMap.ext
        intro x
        exact congrFun hfg x)
  exact Fintype.ofFinite _

noncomputable instance centerGraphPairFintype (t : Nat) :
    Fintype (CenterGraphPair I copies U t) := by
  unfold CenterGraphPair
  infer_instance

private def centerProdEquiv :
    (C I copies U × H I copies U) ≃ₗ[ZMod 2] V I copies U :=
  (C I copies U).prodEquivOfIsCompl (H I copies U)
    (transverseComplement_isCompl I copies (baseQuestion I copies U)).symm

/- A partial linear map is exactly a submodule of C × H meeting the vertical
H-axis trivially. This Mathlib graph API is the bridge to the sigma pair. -/
private def centerGraphSubmodule (t : Nat) (K : SideCenter I copies U t) :
    Submodule (ZMod 2) (C I copies U × H I copies U) :=
  K.1.val.map (centerProdEquiv I copies U).symm.toLinearMap

private theorem sideCenter_transverse_coordinate (t : Nat)
    (K : SideCenter I copies U t) :
    K.1.val ⊓ H I copies U = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hxK : x ∈ K.1.val := hx.1
  have hxH : x ∈ H I copies U := hx.2
  have hambient : (x : TaggedAmbient I copies) ∈
      K.1.val.map (V I copies U).subtype ⊓
        equationSpan (taggedSource I copies).support U.1 := by
    constructor
    · exact ⟨x, hxK, rfl⟩
    · exact hxH
  have hzero : (x : TaggedAmbient I copies) = 0 := by
    have hK : K.1.val.map (V I copies U).subtype ⊓
        equationSpan (taggedSource I copies).support U.1 = ⊥ := K.2
    rw [hK] at hambient
    exact (Submodule.mem_bot (R := ZMod 2)).mp hambient
  exact Subtype.val_injective hzero

private theorem centerGraphSubmodule_vertical (t : Nat)
    (K : SideCenter I copies U t)
    (x : C I copies U × H I copies U)
    (hx : x ∈ centerGraphSubmodule I copies U t K)
    (hx0 : x.1 = 0) : x.2 = 0 := by
  obtain ⟨y, hy, hxy⟩ := hx
  have hyEq : (centerProdEquiv I copies U).symm y = x := hxy
  have hyH : y ∈ H I copies U := by
    have hfirst : ((centerProdEquiv I copies U).symm y).1 = 0 :=
      hyEq ▸ hx0
    exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero
      (C I copies U) (H I copies U)
      (transverseComplement_isCompl I copies (baseQuestion I copies U)).symm).mp hfirst
  have hy0 : y = 0 := by
    have hyInf : y ∈ K.1.val ⊓ H I copies U := ⟨hy, hyH⟩
    rw [sideCenter_transverse_coordinate I copies U t K] at hyInf
    exact (Submodule.mem_bot (R := ZMod 2)).mp hyInf
  have hxzero : x = 0 := by simpa [hy0] using hyEq.symm
  exact congrArg Prod.snd hxzero

private def sideCenterToPMap (t : Nat) (K : SideCenter I copies U t) :
    C I copies U →ₗ.[ZMod 2] H I copies U :=
  (centerGraphSubmodule I copies U t K).toLinearPMap

private theorem pmap_graph_finrank
    (f : C I copies U →ₗ.[ZMod 2] H I copies U) :
    Module.finrank (ZMod 2) f.graph =
      Module.finrank (ZMod 2) f.domain := by
  let p : f.graph →ₗ[ZMod 2] C I copies U :=
    (LinearMap.fst (ZMod 2) (C I copies U) (H I copies U)).comp
      f.graph.subtype
  have hpRange : LinearMap.range p = f.domain := by
    simpa only [p, LinearMap.range_comp, f.graph.range_subtype] using
      f.graph_map_fst_eq_domain
  have hpKer : LinearMap.ker p = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx0 : x.1.1 = 0 := hx
    have hx1 : x.1.2 = 0 := f.graph_fst_eq_zero_snd x.2 hx0
    apply Subtype.ext
    exact Prod.ext hx0 hx1
  have h := p.finrank_range_add_finrank_ker
  rw [hpRange, hpKer, finrank_bot, add_zero] at h
  exact h.symm

private theorem pmap_graph_transverse
    (f : C I copies U →ₗ.[ZMod 2] H I copies U) :
    f.graph.map (centerProdEquiv I copies U).toLinearMap ⊓ H I copies U = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx.1
  have hx0 : ((centerProdEquiv I copies U).symm x).1 = 0 :=
    (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero
      (C I copies U) (H I copies U)
      (transverseComplement_isCompl I copies (baseQuestion I copies U)).symm).mpr hx.2
  have hz0 : z.1 = 0 := by
    simpa [← hzx] using hx0
  have hz1 : z.2 = 0 := f.graph_fst_eq_zero_snd hz hz0
  have zx0 : z = 0 := Prod.ext hz0 hz1
  have xx0 : x = 0 := by simpa [zx0] using hzx.symm
  simpa using xx0

private def pmapToSide (t : Nat)
    (f : C I copies U →ₗ.[ZMod 2] H I copies U)
    (hf : Module.finrank (ZMod 2) f.domain = t) :
    SideCenter I copies U t := by
  let K : Submodule (ZMod 2) (V I copies U) :=
    f.graph.map (centerProdEquiv I copies U).toLinearMap
  have hKdim : Module.finrank (ZMod 2) K = t := by
    dsimp only [K]
    rw [(centerProdEquiv I copies U).finrank_map_eq,
      pmap_graph_finrank I copies U f, hf]
  refine ⟨⟨K, hKdim⟩, ?_⟩
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, hzK, rfl⟩ := hx.1
  have hzH : z ∈ H I copies U := hx.2
  have hzInf : z ∈ K ⊓ H I copies U := ⟨hzK, hzH⟩
  have hz0 : z = 0 := by
    change z ∈ f.graph.map (centerProdEquiv I copies U).toLinearMap ⊓
      H I copies U at hzInf
    rw [pmap_graph_transverse I copies U f] at hzInf
    exact (Submodule.mem_bot (R := ZMod 2)).mp hzInf
  simpa [hz0]

private theorem sideCenterToPMap_rank (t : Nat)
    (K : SideCenter I copies U t) :
    Module.finrank (ZMod 2) (sideCenterToPMap I copies U t K).domain = t := by
  have hg : (sideCenterToPMap I copies U t K).graph =
      centerGraphSubmodule I copies U t K :=
    Submodule.toLinearPMap_graph_eq _
      (centerGraphSubmodule_vertical I copies U t K)
  have hdim : Module.finrank (ZMod 2)
      (centerGraphSubmodule I copies U t K) = t := by
    unfold centerGraphSubmodule
    exact ((centerProdEquiv I copies U).symm.finrank_map_eq K.1.val).trans
      K.1.property
  rw [← pmap_graph_finrank I copies U, hg]
  exact hdim

private def pmapToGraphPair (t : Nat)
    (f : {f : C I copies U →ₗ.[ZMod 2] H I copies U //
      Module.finrank (ZMod 2) f.domain = t}) :
    CenterGraphPair I copies U t :=
  ⟨⟨f.1.domain, f.2⟩, f.1.toFun⟩

private def sideToGraphPair (t : Nat) (K : SideCenter I copies U t) :
    CenterGraphPair I copies U t :=
  pmapToGraphPair I copies U t
    ⟨sideCenterToPMap I copies U t K,
      sideCenterToPMap_rank I copies U t K⟩

private def graphPairToSide (t : Nat) (p : CenterGraphPair I copies U t) :
    SideCenter I copies U t :=
  pmapToSide I copies U t
    { domain := p.1.val, toFun := p.2 } p.1.property

private theorem centerGraphSubmodule_pairToSide (t : Nat)
    (p : CenterGraphPair I copies U t) :
    centerGraphSubmodule I copies U t (graphPairToSide I copies U t p) =
      (show C I copies U →ₗ.[ZMod 2] H I copies U from
        { domain := p.1.val, toFun := p.2 }).graph := by
  unfold centerGraphSubmodule graphPairToSide pmapToSide
  exact (Submodule.map_symm_eq_iff (centerProdEquiv I copies U)).mpr rfl

private theorem graphPair_right_inverse (t : Nat)
    (p : CenterGraphPair I copies U t) :
    sideToGraphPair I copies U t (graphPairToSide I copies U t p) = p := by
  let f : C I copies U →ₗ.[ZMod 2] H I copies U :=
    { domain := p.1.val, toFun := p.2 }
  have hgraph :
      (sideCenterToPMap I copies U t (graphPairToSide I copies U t p)).graph =
        f.graph := by
    exact (Submodule.toLinearPMap_graph_eq _
      (centerGraphSubmodule_vertical I copies U t
        (graphPairToSide I copies U t p))).trans
      (centerGraphSubmodule_pairToSide I copies U t p)
  have hfun : sideCenterToPMap I copies U t
      (graphPairToSide I copies U t p) = f :=
    LinearPMap.eq_of_eq_graph hgraph
  have hsub :
      (⟨sideCenterToPMap I copies U t (graphPairToSide I copies U t p),
        sideCenterToPMap_rank I copies U t (graphPairToSide I copies U t p)⟩ :
        {f : C I copies U →ₗ.[ZMod 2] H I copies U //
          Module.finrank (ZMod 2) f.domain = t}) = ⟨f, p.1.property⟩ :=
    Subtype.ext hfun
  change pmapToGraphPair I copies U t _ = p
  rw [hsub]
  cases p with
  | mk G g => rfl

private theorem graphPair_left_inverse (t : Nat)
    (K : SideCenter I copies U t) :
    graphPairToSide I copies U t (sideToGraphPair I copies U t K) = K := by
  apply Subtype.ext
  apply Subtype.ext
  have hg : (sideCenterToPMap I copies U t K).graph =
      centerGraphSubmodule I copies U t K :=
    Submodule.toLinearPMap_graph_eq _
      (centerGraphSubmodule_vertical I copies U t K)
  change (sideCenterToPMap I copies U t K).graph.map
      (centerProdEquiv I copies U).toLinearMap = K.1.val
  rw [hg]
  unfold centerGraphSubmodule
  exact (Submodule.map_symm_eq_iff (centerProdEquiv I copies U).symm).mpr rfl

/-- Exact graph-pair coordinates for actual tagged transverse centers.
This equivalence is used only to establish the initial presented-leaf
biregularity required for the manuscript's resampled `U'_i` law. -/
def sideCenterGraphPairEquiv (t : Nat) :
    SideCenter I copies U t ≃ CenterGraphPair I copies U t where
  toFun := sideToGraphPair I copies U t
  invFun := graphPairToSide I copies U t
  left_inv := graphPair_left_inverse I copies U t
  right_inv := graphPair_right_inverse I copies U t

/-- Exact cardinality of actual tagged transverse centers for each eligible
first question U. This is the count needed for the original-leaf
biregularity calculation in Eq. (21). -/
theorem taggedCenterOver_card (t : Nat) :
    Fintype.card (TaggedCenterOver I copies t U) =
      gaussian (2 * J) t * 2 ^ (t * J) := by
  classical
  have hlinear (G : Grass (C I copies U) t) :
      Fintype.card (G.val →ₗ[ZMod 2] H I copies U) = 2 ^ (t * J) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)
      (V := G.val →ₗ[ZMod 2] H I copies U),
      Module.finrank_linearMap (R := ZMod 2) (S := ZMod 2)
        (M := G.val) (N := H I copies U), G.property,
      taggedEquationInCoordinate_finrank I copies (baseQuestion I copies U)]
    norm_num
  calc
    Fintype.card (TaggedCenterOver I copies t U) =
        Fintype.card (SideCenter I copies U t) :=
      Fintype.card_congr (centerEquivSide I copies U t)
    _ = Fintype.card (CenterGraphPair I copies U t) :=
      Fintype.card_congr (sideCenterGraphPairEquiv I copies U t)
    _ = ∑ G : Grass (C I copies U) t,
        Fintype.card (G.val →ₗ[ZMod 2] H I copies U) := by
      exact Fintype.card_sigma
    _ = gaussian (2 * J) t * 2 ^ (t * J) := by
      simp_rw [hlinear]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_grass]
      rw [taggedComplement_finrank I copies (baseQuestion I copies U)]
      norm_cast

/-- Every actual center has the same conditional leaf-fibre cardinality. -/
theorem taggedLeafOver_card_actual {t h : Nat}
    (K : TaggedCenterOver I copies t U)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    Fintype.card (TaggedLeafOver I copies h (questionOf I copies U K)) =
      gaussian (2 * J - t) (2 * h - t) * 2 ^ (J * (2 * h - t)) := by
  classical
  let q := questionOf I copies U K
  calc
    Fintype.card (TaggedLeafOver I copies h q) =
        Fintype.card (Σ D : TaggedDomainDraw I copies q h,
          taggedLeafDomainFiber I copies q D) :=
      (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (taggedLeaf_domainDraw I copies q))).symm
    _ = ∑ D : TaggedDomainDraw I copies q h,
          Fintype.card (taggedLeafDomainFiber I copies q D) := Fintype.card_sigma
    _ = Fintype.card (TaggedDomainDraw I copies q h) *
          2 ^ (J * (2 * h - t)) := by
      simp_rw [taggedLeafDomainFiber_card I copies q]
      simp [Finset.sum_const]
    _ = gaussian (2 * J - t) (2 * h - t) *
          2 ^ (J * (2 * h - t)) := by
      rw [taggedDomainDraw_card I copies q h ht hh]

def PresentedOver (h : Nat) :=
  {P : TaggedPresentedLeaf I copies J h // P.U = U.1}

noncomputable instance presentedOverFintype (h : Nat) :
    Fintype (PresentedOver I copies U h) := by
  unfold PresentedOver
  infer_instance

private def presentedOverZeroLeafEquiv (h : Nat) :
    PresentedOver I copies U h ≃
      TaggedLeafOver I copies h
        (questionOf I copies U (zeroCenter I copies U)) where
  toFun P := ⟨P.1, P.2, bot_le⟩
  invFun P := ⟨P.1, P.2.1⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

/-- Every eligible first question has the same number of full presented
leaves. The zero center turns the earlier K-fibre count into this count. -/
theorem presentedOver_card (h : Nat) (hh : h ≤ J) :
    Fintype.card (PresentedOver I copies U h) =
      gaussian (2 * J) (2 * h) * 2 ^ (J * (2 * h)) := by
  rw [Fintype.card_congr (presentedOverZeroLeafEquiv I copies U h)]
  simpa only [Nat.sub_zero] using taggedLeafOver_card_actual I copies U
    (zeroCenter I copies U) (h := h) (by omega) hh

def presentedU {J h : Nat}
    (P : TaggedPresentedLeaf I copies J h) : TaggedGoodU I copies J :=
  ⟨P.U, P.goodU, P.card_U⟩

private def presentedUFiberEquiv {J h : Nat}
    (U : TaggedGoodU I copies J) :
    {P : TaggedPresentedLeaf I copies J h // presentedU I copies P = U} ≃
      PresentedOver I copies U h where
  toFun P := ⟨P.1, congrArg Subtype.val P.2⟩
  invFun P := ⟨P.1, Subtype.ext P.2⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

private theorem presentedUFiber_card {J h : Nat}
    (U : TaggedGoodU I copies J) (hh : h ≤ J) :
    Fintype.card {P : TaggedPresentedLeaf I copies J h //
      presentedU I copies P = U} =
      gaussian (2 * J) (2 * h) * 2 ^ (J * (2 * h)) := by
  rw [Fintype.card_congr (presentedUFiberEquiv I copies U)]
  exact presentedOver_card I copies U h hh

/-- Reverse incidence, now specialized to the same fixed eligible U as the
actual sampler. No center is resampled into a different first question. -/
private theorem centersInPresentedOver_card {t h : Nat}
    (P : PresentedOver I copies U h) :
    Fintype.card {K : TaggedCenterOver I copies t U // K.1 ≤ P.1.L} =
      gaussian (2 * h) t := by
  have hU :
      (⟨P.1.U, P.1.goodU, P.1.card_U⟩ : TaggedGoodU I copies J) = U :=
    Subtype.ext P.2
  have hty : {K : TaggedCenterOver I copies t U // K.1 ≤ P.1.L} =
      CentersInLeaf I copies (t := t) P.1 := by
    unfold CentersInLeaf
    rw [hU]
  exact (Fintype.card_congr (Equiv.cast hty)).trans
    (centersInLeaf_card I copies (t := t) P.1)

private def fixedULeafToPresented {t h : Nat}
    (K : TaggedCenterOver I copies t U) :
    TaggedLeafOver I copies h (questionOf I copies U K) →
      PresentedOver I copies U h :=
  fun P => ⟨P.1, P.2.1⟩

/-- The actual conditional center/leaf mechanism for one presented leaf,
with the first question U fixed. -/
def fixedUPresentedLeafLaw {t h : Nat}
    [Nonempty (TaggedCenterOver I copies t U)]
    (hleaf : ∀ K : TaggedCenterOver I copies t U,
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (PresentedOver I copies U h) :=
  uniformMixture (fun K : TaggedCenterOver I copies t U =>
    pushforward (fixedULeafToPresented I copies U K)
      (@uniformLaw _ inferInstance (hleaf K)))

private theorem fixedULeafToPresented_atom {t h : Nat}
    (K : TaggedCenterOver I copies t U)
    [Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))]
    (P : PresentedOver I copies U h) :
    (pushforward (fixedULeafToPresented I copies U K)
      (uniformLaw (TaggedLeafOver I copies h (questionOf I copies U K)))).mass P =
      if K.1 ≤ P.1.L then
        (1 : ℚ) / Fintype.card
          (TaggedLeafOver I copies h (questionOf I copies U K))
      else 0 := by
  classical
  rw [pushforward_apply]
  by_cases hK : K.1 ≤ P.1.L
  · let L : TaggedLeafOver I copies h (questionOf I copies U K) :=
      ⟨P.1, P.2, hK⟩
    rw [Fintype.sum_eq_single L]
    · have hLP : fixedULeafToPresented I copies U K L = P :=
        Subtype.ext rfl
      rw [if_pos hLP, uniformLaw_apply]
      simp [hK]
    · intro L' hne
      have hne' : fixedULeafToPresented I copies U K L' ≠ P := by
        intro heq
        apply hne
        have hp : L'.1 = P.1 := congrArg Subtype.val heq
        exact Subtype.ext hp
      simp [hne']
  · simp only [hK, if_false]
    apply Finset.sum_eq_zero
    intro L _
    have hne : fixedULeafToPresented I copies U K L ≠ P := by
      intro heq
      apply hK
      have hval : L.1 = P.1 := congrArg Subtype.val heq
      simpa [questionOf, hval] using L.2.2
    simp [hne]

/-- The actual U→K→one-leaf kernel has constant point mass on every
presented leaf over that U. This is the numerator computation needed to
identify the original draw's i-th leaf marginal. -/
theorem fixedU_presentedLeaf_kernel_constant {t h : Nat}
    (P : PresentedOver I copies U h)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    (∑ K : TaggedCenterOver I copies t U,
      if K.1 ≤ P.1.L then
        ((1 : ℚ) / Fintype.card (TaggedCenterOver I copies t U)) *
          ((1 : ℚ) / Fintype.card
            (TaggedLeafOver I copies h (questionOf I copies U K)))
      else 0) =
      (gaussian (2 * h) t : ℚ) *
        ((1 : ℚ) /
          (gaussian (2 * J) t * 2 ^ (t * J) : Nat)) *
        ((1 : ℚ) /
          (gaussian (2 * J - t) (2 * h - t) *
            2 ^ (J * (2 * h - t)) : Nat)) := by
  classical
  have hc : Fintype.card (TaggedCenterOver I copies t U) =
      gaussian (2 * J) t * 2 ^ (t * J) :=
    taggedCenterOver_card I copies U t
  have hl (K : TaggedCenterOver I copies t U) :
      Fintype.card (TaggedLeafOver I copies h (questionOf I copies U K)) =
        gaussian (2 * J - t) (2 * h - t) *
          2 ^ (J * (2 * h - t)) :=
    taggedLeafOver_card_actual I copies U K ht hh
  simp_rw [hc, hl]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype
    (fun K : TaggedCenterOver I copies t U => K.1 ≤ P.1.L),
    centersInPresentedOver_card I copies U P]
  rw [mul_assoc]

/-- The actual fixed-U one-leaf sampling law has constant mass. -/
private theorem fixedUPresentedLeafLaw_mass_constant {t h : Nat}
    [Nonempty (TaggedCenterOver I copies t U)]
    (hleaf : ∀ K : TaggedCenterOver I copies t U,
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (P : PresentedOver I copies U h)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    (fixedUPresentedLeafLaw I copies U hleaf).mass P =
      (gaussian (2 * h) t : ℚ) *
        ((1 : ℚ) / (gaussian (2 * J) t * 2 ^ (t * J) : Nat)) *
        ((1 : ℚ) /
          (gaussian (2 * J - t) (2 * h - t) *
            2 ^ (J * (2 * h - t)) : Nat)) := by
  classical
  change (∑ K : TaggedCenterOver I copies t U,
    (pushforward (fixedULeafToPresented I copies U K)
      (@uniformLaw _ inferInstance (hleaf K))).mass P) /
        Fintype.card (TaggedCenterOver I copies t U) = _
  simp_rw [fixedULeafToPresented_atom I copies U]
  rw [div_eq_mul_inv, Finset.sum_mul]
  convert fixedU_presentedLeaf_kernel_constant I copies U P ht hh using 1
  apply Finset.sum_congr rfl
  intro K _
  by_cases hK : K.1 ≤ P.1.L
  · simp [hK, div_eq_mul_inv, mul_comm]
  · simp [hK]

/-- Uniform full presented leaves project to uniform eligible first questions.
This is the final deterministic projection after class-resampling stationarity. -/
theorem uniform_presentedU_pushforward {J h : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)] (hh : h ≤ J) :
    pushforward (presentedU I copies)
      (uniformLaw (TaggedPresentedLeaf I copies J h)) =
        uniformLaw (TaggedGoodU I copies J) := by
  classical
  let d := gaussian (2 * J) (2 * h) * 2 ^ (J * (2 * h))
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos (GaussianRatio.gaussian_pos (by omega))
      (pow_pos (by decide) _)
  have htotal : Fintype.card (TaggedPresentedLeaf I copies J h) =
      Fintype.card (TaggedGoodU I copies J) * d := by
    calc
      Fintype.card (TaggedPresentedLeaf I copies J h) =
          Fintype.card (Σ U : TaggedGoodU I copies J,
            {P : TaggedPresentedLeaf I copies J h //
              presentedU I copies P = U}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv (presentedU I copies)).symm
      _ = ∑ U : TaggedGoodU I copies J,
            Fintype.card {P : TaggedPresentedLeaf I copies J h //
              presentedU I copies P = U} := Fintype.card_sigma
      _ = Fintype.card (TaggedGoodU I copies J) * d := by
        simp_rw [presentedUFiber_card I copies (hh := hh)]
        simp [Finset.sum_const, d]
  apply FiniteLaw.ext
  intro U
  rw [pushforward_apply, uniformLaw_apply]
  simp_rw [uniformLaw_apply (TaggedPresentedLeaf I copies J h)]
  have hsum :
      (∑ P : TaggedPresentedLeaf I copies J h,
        if presentedU I copies P = U then
          (1 : ℚ) / Fintype.card (TaggedPresentedLeaf I copies J h)
        else 0) =
      (Fintype.card {P : TaggedPresentedLeaf I copies J h //
        presentedU I copies P = U} : ℚ) /
        Fintype.card (TaggedPresentedLeaf I copies J h) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype
      (fun P : TaggedPresentedLeaf I copies J h =>
        presentedU I copies P = U)]
    simp [div_eq_mul_inv]
  rw [hsum, presentedUFiber_card I copies U hh, htotal]
  have hU : (Fintype.card (TaggedGoodU I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedGoodU I copies J) ≠ 0)
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hU, hdq]
  simp [d, Nat.cast_mul, mul_comm]

/- The next law is the actual class-resampling kernel on presented vertices.
Its input is the initial presented-leaf law; after the initial marginal is
identified with the original draw, stationarity transfers to every U'_i. -/
private def classRepresentativeVal {J h : Nat}
    (C₀ : TaggedLeafClass I copies J h) :
    TaggedClassRepresentative I copies C₀ →
      TaggedPresentedLeaf I copies J h := Subtype.val

def classResampledPresentedLaw {J h : Nat}
    [Nonempty (TaggedPresentedLeaf I copies J h)] :
    FiniteLaw (TaggedPresentedLeaf I copies J h) :=
  uniformMixture (fun P : TaggedPresentedLeaf I copies J h =>
    pushforward (classRepresentativeVal I copies (taggedClassOf I copies P))
      (uniformLaw (TaggedClassRepresentative I copies
        (taggedClassOf I copies P))))

private theorem classRepresentative_pushforward_atom {J h : Nat}
    (C₀ : TaggedLeafClass I copies J h)
    (Q : TaggedPresentedLeaf I copies J h) :
    (pushforward (classRepresentativeVal I copies C₀)
      (uniformLaw (TaggedClassRepresentative I copies C₀))).mass Q =
      if taggedClassOf I copies Q = C₀ then
        (1 : ℚ) / Fintype.card (TaggedClassRepresentative I copies C₀)
      else 0 := by
  classical
  rw [pushforward_apply]
  by_cases hQ : taggedClassOf I copies Q = C₀
  · let r : TaggedClassRepresentative I copies C₀ := ⟨Q, hQ⟩
    rw [Fintype.sum_eq_single r]
    · rw [if_pos (show classRepresentativeVal I copies C₀ r = Q by rfl),
        if_pos hQ]
      simpa only [one_div] using
        (uniformLaw_apply (TaggedClassRepresentative I copies C₀) r)
    · intro s hs
      have hne : s.1 ≠ Q := by
        intro heq
        exact hs (Subtype.ext heq)
      simp [classRepresentativeVal, hne]
  · simp only [hQ, if_false]
    apply Finset.sum_eq_zero
    intro r hr
    have hrne : r.1 ≠ Q := by
      intro heq
      exact hQ (heq ▸ r.2)
    simp [classRepresentativeVal, hrne]

/-- A uniform initial full presented leaf stays uniform after choosing a
uniform representative in its tagged equivalence class. Class sizes may vary;
their cardinality cancels within each class. -/
theorem uniform_presented_classResample_stationary {J h : Nat}
    [Nonempty (TaggedPresentedLeaf I copies J h)] :
    classResampledPresentedLaw I copies (J := J) (h := h) =
      uniformLaw (TaggedPresentedLeaf I copies J h) := by
  classical
  apply FiniteLaw.ext
  intro Q
  have hsum :
      (∑ P : TaggedPresentedLeaf I copies J h,
        if taggedClassOf I copies Q = taggedClassOf I copies P then
          (1 : ℚ) / Fintype.card
            (TaggedClassRepresentative I copies (taggedClassOf I copies P))
        else 0) = 1 := by
    let C₀ := taggedClassOf I copies Q
    have hc : (Fintype.card (TaggedClassRepresentative I copies C₀) : ℚ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (TaggedClassRepresentative I copies C₀) ≠ 0)
    calc
      _ = ∑ P : TaggedPresentedLeaf I copies J h,
          if taggedClassOf I copies P = C₀ then
            (1 : ℚ) / Fintype.card (TaggedClassRepresentative I copies C₀)
          else 0 := by
            apply Finset.sum_congr rfl
            intro P _
            by_cases hP : taggedClassOf I copies P = C₀
            · simp [C₀, hP]
            · have hn : taggedClassOf I copies Q ≠ taggedClassOf I copies P := by
                simpa only [C₀, eq_comm] using hP
              simp [hn, hP]
      _ = (Fintype.card (TaggedClassRepresentative I copies C₀) : ℚ) /
            Fintype.card (TaggedClassRepresentative I copies C₀) := by
            simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
              Finset.sum_const, nsmul_eq_mul]
            rw [← Fintype.card_subtype
              (fun P : TaggedPresentedLeaf I copies J h =>
                taggedClassOf I copies P = C₀)]
            have hcard : Fintype.card {x : TaggedPresentedLeaf I copies J h //
                taggedClassOf I copies x = C₀} =
                Fintype.card (TaggedClassRepresentative I copies C₀) :=
              Fintype.card_congr (Equiv.refl _)
            rw [hcard]
            field_simp [hc]
      _ = 1 := by field_simp
  change (∑ P : TaggedPresentedLeaf I copies J h,
      (pushforward (classRepresentativeVal I copies (taggedClassOf I copies P))
        (uniformLaw (TaggedClassRepresentative I copies
          (taggedClassOf I copies P)))).mass Q) /
      Fintype.card (TaggedPresentedLeaf I copies J h) =
        (uniformLaw (TaggedPresentedLeaf I copies J h)).mass Q
  simp_rw [classRepresentative_pushforward_atom I copies]
  rw [hsum, uniformLaw_apply]

private theorem uniformProdFst
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    pushforward (fun z : A × B => z.1) (uniformLaw (A × B)) =
      uniformLaw A := by
  classical
  apply FiniteLaw.ext
  intro a
  rw [pushforward_apply, uniformLaw_apply]
  simp_rw [uniformLaw_apply (A × B)]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single a]
  · simp only [ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_prod, Nat.cast_mul]
    have ha : (Fintype.card A : ℚ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
    have hb : (Fintype.card B : ℚ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
    field_simp [ha, hb]
  · intro a' hne
    simp [hne]

private theorem uniformFinEval
    {A : Type*} [Fintype A] [Nonempty A] {k : Nat}
    (i : Fin k) :
    pushforward (fun f : Fin k → A => f i)
      (uniformLaw (Fin k → A)) = uniformLaw A := by
  classical
  let e := Equiv.funSplitAt i A
  letI : Nonempty ({j : Fin k // j ≠ i} → A) :=
    ⟨fun _ => Classical.choice inferInstance⟩
  calc
    pushforward (fun f : Fin k → A => f i) (uniformLaw (Fin k → A)) =
        pushforward (fun z : A × ({j : Fin k // j ≠ i} → A) => z.1)
          (pushforward e (uniformLaw (Fin k → A))) := by
        rw [pushforward_comp]
        rfl
    _ = pushforward (fun z : A × ({j : Fin k // j ≠ i} → A) => z.1)
          (uniformLaw (A × ({j : Fin k // j ≠ i} → A))) := by
        rw [pushforward_uniformLaw_equiv e]
    _ = uniformLaw A := uniformProdFst

/-- A coordinate of a uniform dependent choice is uniform in its own fibre.
This is the representative-choice kernel in the actual tagged joint draw. -/
private theorem uniformDependentFinEval
    {k : Nat} (A : Fin k → Type*) [∀ j, Fintype (A j)]
    [∀ j, Nonempty (A j)] (i : Fin k) :
    pushforward (fun f : (j : Fin k) → A j => f i)
      (uniformLaw ((j : Fin k) → A j)) = uniformLaw (A i) := by
  classical
  let e := Equiv.piSplitAt i A
  letI : Nonempty ((j : {j : Fin k // j ≠ i}) → A j.1) :=
    ⟨fun j => Classical.choice (inferInstance : Nonempty (A j.1))⟩
  calc
    pushforward (fun f : (j : Fin k) → A j => f i)
        (uniformLaw ((j : Fin k) → A j)) =
      pushforward (fun z : A i × ((j : {j : Fin k // j ≠ i}) → A j.1) => z.1)
        (pushforward e (uniformLaw ((j : Fin k) → A j))) := by
          rw [pushforward_comp]
          rfl
    _ = pushforward (fun z : A i × ((j : {j : Fin k // j ≠ i}) → A j.1) => z.1)
          (uniformLaw (A i × ((j : {j : Fin k // j ≠ i}) → A j.1))) := by
            rw [pushforward_uniformLaw_equiv e]
    _ = uniformLaw (A i) := uniformProdFst

/-- In the source's actual independent class-representative draw, the
coordinate `i` is uniform in its own presented-leaf class. -/
theorem taggedIndependentChoice_eval_uniform {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) (i : Fin k) :
    pushforward (fun r : TaggedIndependentChoice I copies vs => r i)
      (uniformLaw (TaggedIndependentChoice I copies vs)) =
        uniformLaw (TaggedClassRepresentative I copies
          (taggedClassOf I copies (vs i))) := by
  classical
  exact uniformDependentFinEval
    (fun j : Fin k => TaggedClassRepresentative I copies
      (taggedClassOf I copies (vs j))) i

theorem taggedIndependentChoice_presented_coordinate {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) (i : Fin k) :
    pushforward (fun r : TaggedIndependentChoice I copies vs => (r i).1)
      (uniformLaw (TaggedIndependentChoice I copies vs)) =
    pushforward (classRepresentativeVal I copies (taggedClassOf I copies (vs i)))
      (uniformLaw (TaggedClassRepresentative I copies
        (taggedClassOf I copies (vs i)))) := by
  classical
  calc
    _ = pushforward
        (classRepresentativeVal I copies (taggedClassOf I copies (vs i)))
        (pushforward (fun r : TaggedIndependentChoice I copies vs => r i)
          (uniformLaw (TaggedIndependentChoice I copies vs))) := by
            rw [pushforward_comp]
            rfl
    _ = _ := by rw [taggedIndependentChoice_eval_uniform I copies vs i]

/-- Finite normalization turns an atomwise constant law into uniformity. -/
private theorem law_eq_uniform_of_constant
    {A : Type*} [Fintype A] [Nonempty A]
    (μ : FiniteLaw A) (c : ℚ) (hc : ∀ a : A, μ.mass a = c) :
    μ = uniformLaw A := by
  classical
  have hmass : c * (Fintype.card A : ℚ) = 1 := by
    have hn := μ.normalized
    simp_rw [hc] at hn
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_comm] using hn
  have hcard : (Fintype.card A : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  apply FiniteLaw.ext
  intro a
  rw [hc, uniformLaw_apply]
  exact (eq_div_iff hcard).2 hmass

/-- For each fixed eligible U, the actual center and leaf kernel samples a
uniform full presented leaf over that U. -/
theorem fixedUPresentedLeafLaw_uniform {t h : Nat}
    [Nonempty (TaggedCenterOver I copies t U)]
    [Nonempty (PresentedOver I copies U h)]
    (hleaf : ∀ K : TaggedCenterOver I copies t U,
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    fixedUPresentedLeafLaw I copies U hleaf =
      uniformLaw (PresentedOver I copies U h) := by
  classical
  apply law_eq_uniform_of_constant
    (fixedUPresentedLeafLaw I copies U hleaf)
    ((gaussian (2 * h) t : ℚ) *
      ((1 : ℚ) / (gaussian (2 * J) t * 2 ^ (t * J) : Nat)) *
      ((1 : ℚ) /
        (gaussian (2 * J - t) (2 * h - t) *
          2 ^ (J * (2 * h - t)) : Nat)))
  intro P
  exact fixedUPresentedLeafLaw_mass_constant I copies U hleaf P ht hh

/-- At a fixed U and K, evaluating one coordinate of the actual uniform
ordered leaf tuple gives the one-leaf kernel used above. -/
private theorem fixedU_orderedLeaf_coordinate {t h k : Nat}
    (K : TaggedCenterOver I copies t U)
    [Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))]
    (i : Fin k) :
    pushforward
      (fun Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K) =>
        fixedULeafToPresented I copies U K (Ls i))
      (uniformLaw (Fin k → TaggedLeafOver I copies h (questionOf I copies U K))) =
    pushforward (fixedULeafToPresented I copies U K)
      (uniformLaw (TaggedLeafOver I copies h (questionOf I copies U K))) := by
  classical
  calc
    _ = pushforward (fixedULeafToPresented I copies U K)
        (pushforward (fun Ls : Fin k → TaggedLeafOver I copies h
          (questionOf I copies U K) => Ls i)
          (uniformLaw (Fin k → TaggedLeafOver I copies h
            (questionOf I copies U K)))) := by
          rw [pushforward_comp]
          rfl
    _ = _ := by rw [uniformFinEval]

/-- The fixed-U, center-averaged ordered-tuple coordinate law is exactly the
fixed-U one-leaf law whose uniformity was proved by reverse incidence. -/
theorem fixedU_orderedLeaf_coordinate_mixture {t h k : Nat}
    [Nonempty (TaggedCenterOver I copies t U)]
    (hleaf : ∀ K : TaggedCenterOver I copies t U,
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (i : Fin k) :
    uniformMixture (fun K : TaggedCenterOver I copies t U =>
      pushforward
        (fun Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K) =>
          fixedULeafToPresented I copies U K (Ls i))
        (@uniformLaw _ inferInstance
          ⟨fun _ => Classical.choice (hleaf K)⟩)) =
      fixedUPresentedLeafLaw I copies U hleaf := by
  classical
  unfold fixedUPresentedLeafLaw
  congr 1
  funext K
  exact fixedU_orderedLeaf_coordinate I copies U K i

/-- Forgetting the sampled class representatives in the actual joint law
recovers the source's tagged U→K→ordered-leaf geometry law. -/
private theorem taggedJoint_geometry_pushforward {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    pushforward Sigma.fst
      (taggedJointLaw I copies (k := k) hcenter hleaf) =
        taggedSampleLaw I copies hcenter hleaf := by
  classical
  apply FiniteLaw.ext
  intro p
  rw [pushforward_apply]
  change (∑ z : Σ q : TaggedSample I copies J t h k,
      TaggedIndependentChoice I copies (sampledStar I copies q).leaves,
      if z.1 = p then
        (taggedSampleLaw I copies hcenter hleaf).mass z.1 *
          (uniformLaw (TaggedIndependentChoice I copies
            (sampledStar I copies z.1).leaves)).mass z.2
      else 0) = (taggedSampleLaw I copies hcenter hleaf).mass p
  simp only [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single p]
  · simp only [ite_true]
    rw [← Finset.mul_sum,
      (uniformLaw (TaggedIndependentChoice I copies
        (sampledStar I copies p).leaves)).normalized, mul_one]
  · intro q hq
    simp [hq]

/-- The independently defined original field draw is exactly the pushforward
of the tagged joint law through its proved field equivalence. -/
private theorem originalLaw_pushforward_decode {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    pushforward (decodeDraw I copies)
      (taggedJointLaw I copies (k := k) hcenter hleaf) =
        originalLawFromTagged I copies hcenter hleaf := by
  classical
  apply FiniteLaw.ext
  intro x
  rw [pushforward_apply]
  rw [Fintype.sum_eq_single (encodeDraw I copies x)]
  · have hx : decodeDraw I copies (encodeDraw I copies x) = x :=
      (originalDrawEquiv I copies).left_inv x
    simp only [hx, if_true]
    exact (originalLaw_mass_encode I copies hcenter hleaf x).symm
  · intro y hy
    have hne : decodeDraw I copies y ≠ x := by
      intro hxy
      apply hy
      calc
        y = encodeDraw I copies (decodeDraw I copies y) :=
          ((originalDrawEquiv I copies).right_inv y).symm
        _ = encodeDraw I copies x := congrArg (encodeDraw I copies) hxy
    simp [hne]

private def taggedPresentedLeafLawFromFixedU {J t h : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (TaggedPresentedLeaf I copies J h) := by
  classical
  letI (U : TaggedGoodU I copies J) :
      Nonempty (TaggedCenterOver I copies t U) := hcenter U
  exact uniformMixture (fun U : TaggedGoodU I copies J =>
    pushforward Subtype.val
      (fixedUPresentedLeafLaw I copies U (hleaf U)))

private theorem presentedOver_uniform_pushforward_atom {J h : Nat}
    (U : TaggedGoodU I copies J) [Nonempty (PresentedOver I copies U h)]
    (P : TaggedPresentedLeaf I copies J h) :
    (pushforward Subtype.val (uniformLaw (PresentedOver I copies U h))).mass P =
      if P.U = U.1 then
        (1 : ℚ) / Fintype.card (PresentedOver I copies U h)
      else 0 := by
  classical
  change (∑ Q : PresentedOver I copies U h,
    if Q.1 = P then (uniformLaw (PresentedOver I copies U h)).mass Q
    else 0) = _
  by_cases hU : P.U = U.1
  · let Q : PresentedOver I copies U h := ⟨P, hU⟩
    rw [Fintype.sum_eq_single Q]
    · have hQP : Q.1 = P := rfl
      rw [if_pos hQP, uniformLaw_apply]
      simp [hU]
    · intro Q' hne
      have hne' : Q'.1 ≠ P := by
        intro heq
        exact hne (Subtype.ext heq)
      simp [hne']
  · simp only [hU, if_false]
    apply Finset.sum_eq_zero
    intro Q _
    have hne : Q.1 ≠ P := by
      intro heq
      exact hU (heq ▸ Q.2)
    simp [hne]

private theorem taggedSample_presented_coordinate_mixture {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (i : Fin k) :
    pushforward (fun p : TaggedSample I copies J t h k => (p.2.2 i).1)
      (taggedSampleLaw I copies hcenter hleaf) =
        taggedPresentedLeafLawFromFixedU I copies hcenter hleaf := by
  classical
  apply FiniteLaw.ext
  intro P
  rw [pushforward_apply]
  simp only [TaggedSample, Fintype.sum_sigma]
  simp only [taggedSampleLaw, uniformLaw_apply]
  change _ = (∑ U : TaggedGoodU I copies J,
    (pushforward Subtype.val
      (fixedUPresentedLeafLaw I copies U (hleaf U))).mass P) /
      Fintype.card (TaggedGoodU I copies J)
  have hU (U : TaggedGoodU I copies J) :
      (∑ K : TaggedCenterOver I copies t U,
        ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
          if (Ls i).1 = P then
            (1 : ℚ) / Fintype.card (TaggedCenterOver I copies t U) *
              ((1 : ℚ) / Fintype.card
                (Fin k → TaggedLeafOver I copies h (questionOf I copies U K)))
          else 0) =
        (pushforward Subtype.val
          (fixedUPresentedLeafLaw I copies U (hleaf U))).mass P := by
    letI : Nonempty (TaggedCenterOver I copies t U) := hcenter U
    rw [← fixedU_orderedLeaf_coordinate_mixture I copies U (hleaf U) i]
    have htransport :
        pushforward Subtype.val
          (uniformMixture (fun K : TaggedCenterOver I copies t U =>
            pushforward (fun Ls : Fin k → TaggedLeafOver I copies h
              (questionOf I copies U K) =>
                fixedULeafToPresented I copies U K (Ls i))
              (@uniformLaw _ inferInstance
                ⟨fun _ => Classical.choice (hleaf U K)⟩))) =
          uniformMixture (fun K : TaggedCenterOver I copies t U =>
            pushforward (fun Ls : Fin k → TaggedLeafOver I copies h
              (questionOf I copies U K) => (Ls i).1)
              (@uniformLaw _ inferInstance
                ⟨fun _ => Classical.choice (hleaf U K)⟩)) := by
      rw [pushforward_uniformMixture]
      congr 1
      funext K
      exact (pushforward_comp
        (fun Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K) =>
          fixedULeafToPresented I copies U K (Ls i))
        (fun Q : PresentedOver I copies U h => Q.1)
        (@uniformLaw _ inferInstance
          ⟨fun _ => Classical.choice (hleaf U K)⟩))
    calc
      _ = (uniformMixture (fun K : TaggedCenterOver I copies t U =>
          pushforward (fun Ls : Fin k → TaggedLeafOver I copies h
            (questionOf I copies U K) => (Ls i).1)
            (@uniformLaw _ inferInstance
              ⟨fun _ => Classical.choice (hleaf U K)⟩))).mass P := by
            change _ = (∑ K : TaggedCenterOver I copies t U,
              ∑ Ls : Fin k → TaggedLeafOver I copies h
                (questionOf I copies U K),
                if (Ls i).1 = P then
                  (1 : ℚ) / Fintype.card
                    (Fin k → TaggedLeafOver I copies h (questionOf I copies U K))
                else 0) /
                  Fintype.card (TaggedCenterOver I copies t U)
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro K _
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro Ls _
            by_cases hP : (Ls i).1 = P
            · simp [hP, div_eq_mul_inv, mul_comm]
            · simp [hP]
      _ = _ := congrArg (fun μ : FiniteLaw (TaggedPresentedLeaf I copies J h) =>
        μ.mass P) htransport.symm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro U _
  rw [← hU U, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro Ls _
  by_cases hP : (Ls i).1 = P
  · simp [hP, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · simp [hP]

/-- Uniform U and the actual uniform fixed-U presented-leaf kernels yield
the uniform law on all full presented leaves. -/
theorem taggedPresentedLeafLawFromFixedU_uniform {J t h : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    taggedPresentedLeafLawFromFixedU I copies hcenter hleaf =
      uniformLaw (TaggedPresentedLeaf I copies J h) := by
  classical
  letI (U : TaggedGoodU I copies J) :
      Nonempty (TaggedCenterOver I copies t U) := hcenter U
  letI (U : TaggedGoodU I copies J) :
      Nonempty (PresentedOver I copies U h) := by
    let K := Classical.choice (hcenter U)
    exact ⟨fixedULeafToPresented I copies U K
      (Classical.choice (hleaf U K))⟩
  have hmix : taggedPresentedLeafLawFromFixedU I copies hcenter hleaf =
      uniformMixture (fun U : TaggedGoodU I copies J =>
        pushforward Subtype.val (uniformLaw (PresentedOver I copies U h))) := by
    unfold taggedPresentedLeafLawFromFixedU
    congr 1
    funext U
    rw [fixedUPresentedLeafLaw_uniform I copies U (hleaf U) ht hh]
  let d := gaussian (2 * J) (2 * h) * 2 ^ (J * (2 * h))
  have hd : (d : ℚ) ≠ 0 := by
    have hg : 0 < d := Nat.mul_pos (GaussianRatio.gaussian_pos (by omega))
      (pow_pos (by decide) _)
    exact_mod_cast (Nat.ne_of_gt hg)
  have htotal : Fintype.card (TaggedPresentedLeaf I copies J h) =
      Fintype.card (TaggedGoodU I copies J) * d := by
    calc
      Fintype.card (TaggedPresentedLeaf I copies J h) =
          Fintype.card (Σ U : TaggedGoodU I copies J,
            {P : TaggedPresentedLeaf I copies J h //
              presentedU I copies P = U}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv (presentedU I copies)).symm
      _ = ∑ U : TaggedGoodU I copies J,
            Fintype.card {P : TaggedPresentedLeaf I copies J h //
              presentedU I copies P = U} := Fintype.card_sigma
      _ = Fintype.card (TaggedGoodU I copies J) * d := by
        simp_rw [presentedUFiber_card I copies (hh := hh)]
        simp [Finset.sum_const, d]
  rw [hmix]
  apply FiniteLaw.ext
  intro P
  change (∑ U : TaggedGoodU I copies J,
    (pushforward Subtype.val
      (uniformLaw (PresentedOver I copies U h))).mass P) /
      Fintype.card (TaggedGoodU I copies J) =
        (uniformLaw (TaggedPresentedLeaf I copies J h)).mass P
  simp_rw [presentedOver_uniform_pushforward_atom I copies]
  have hsum : (∑ U : TaggedGoodU I copies J,
      if P.U = U.1 then (1 : ℚ) / Fintype.card (PresentedOver I copies U h)
      else 0) = (1 : ℚ) / d := by
    rw [Fintype.sum_eq_single (presentedU I copies P)]
    · have hP : P.U = (presentedU I copies P).1 := rfl
      rw [if_pos hP, presentedOver_card I copies (presentedU I copies P) h hh]
    · intro U hne
      have hneq : P.U ≠ U.1 := by
        intro heq
        apply hne
        exact Subtype.ext heq.symm
      simp [hneq]
  rw [hsum, uniformLaw_apply, htotal]
  have hU : (Fintype.card (TaggedGoodU I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedGoodU I copies J) ≠ 0)
  field_simp [hU, hd]
  simp [d, Nat.cast_mul, mul_comm]

theorem taggedSample_presented_coordinate_uniform {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) (i : Fin k) :
    pushforward (fun p : TaggedSample I copies J t h k => (p.2.2 i).1)
      (taggedSampleLaw I copies hcenter hleaf) =
        uniformLaw (TaggedPresentedLeaf I copies J h) := by
  rw [taggedSample_presented_coordinate_mixture I copies hcenter hleaf i]
  exact taggedPresentedLeafLawFromFixedU_uniform I copies hcenter hleaf ht hh

theorem originalDraw_presented_coordinate_uniform {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) (i : Fin k) :
    pushforward (fun x : OriginalDraw I copies J t h k =>
      (x.leaves i).presented)
      (originalLawFromTagged I copies hcenter hleaf) =
        uniformLaw (TaggedPresentedLeaf I copies J h) := by
  calc
    _ = pushforward (fun x : OriginalDraw I copies J t h k =>
        (x.leaves i).presented)
        (pushforward (decodeDraw I copies)
          (taggedJointLaw I copies hcenter hleaf)) := by
          rw [originalLaw_pushforward_decode I copies hcenter hleaf]
    _ = pushforward (fun p : TaggedSample I copies J t h k =>
        (p.2.2 i).1)
        (pushforward Sigma.fst
          (taggedJointLaw I copies hcenter hleaf)) := by
          rw [pushforward_comp, pushforward_comp]
          rfl
    _ = pushforward (fun p : TaggedSample I copies J t h k =>
        (p.2.2 i).1)
        (taggedSampleLaw I copies hcenter hleaf) := by
          rw [taggedJoint_geometry_pushforward I copies hcenter hleaf]
    _ = uniformLaw (TaggedPresentedLeaf I copies J h) :=
      taggedSample_presented_coordinate_uniform I copies hcenter hleaf ht hh i

private theorem weightedKernel_sum_pushforward
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteLaw A) (f : A → B) (κ : B → FiniteLaw C) (c : C) :
    (∑ a : A, μ.mass a * (κ (f a)).mass c) =
      ∑ b : B, (pushforward f μ).mass b * (κ b).mass c := by
  classical
  calc
    _ = ∑ a : A, ∑ b : B,
        if f a = b then μ.mass a * (κ b).mass c else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Fintype.sum_eq_single (f a)]
          · simp
          · intro b hne
            simp [Ne.symm hne]
    _ = ∑ b : B, ∑ a : A,
        if f a = b then μ.mass a * (κ b).mass c else 0 := Finset.sum_comm
    _ = ∑ b : B, (pushforward f μ).mass b * (κ b).mass c := by
          apply Finset.sum_congr rfl
          intro b _
          rw [pushforward_apply, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : f a = b <;> simp [h]

private theorem taggedJoint_representative_coordinate_eq_classResampled
    {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) (i : Fin k) :
    pushforward (fun z : Σ p : TaggedSample I copies J t h k,
      TaggedIndependentChoice I copies (sampledStar I copies p).leaves =>
        (z.2 i).1)
      (taggedJointLaw I copies hcenter hleaf) =
        classResampledPresentedLaw I copies (J := J) (h := h) := by
  classical
  apply FiniteLaw.ext
  intro Q
  rw [pushforward_apply]
  simp only [Fintype.sum_sigma]
  let μ : FiniteLaw (TaggedSample I copies J t h k) :=
    taggedSampleLaw I copies hcenter hleaf
  let f : TaggedSample I copies J t h k → TaggedPresentedLeaf I copies J h :=
    fun p => (p.2.2 i).1
  let κ : TaggedPresentedLeaf I copies J h →
      FiniteLaw (TaggedPresentedLeaf I copies J h) :=
    fun P => pushforward
      (classRepresentativeVal I copies (taggedClassOf I copies P))
      (uniformLaw (TaggedClassRepresentative I copies
        (taggedClassOf I copies P)))
  have hinner (p : TaggedSample I copies J t h k) :
      (∑ r : TaggedIndependentChoice I copies (sampledStar I copies p).leaves,
        if (r i).1 = Q then
          (taggedJointLaw I copies hcenter hleaf).mass ⟨p, r⟩
        else 0) = μ.mass p * (κ (f p)).mass Q := by
    change (∑ r : TaggedIndependentChoice I copies (sampledStar I copies p).leaves,
      if (r i).1 = Q then
        μ.mass p * (uniformLaw (TaggedIndependentChoice I copies
          (sampledStar I copies p).leaves)).mass r
      else 0) = _
    calc
      _ = μ.mass p *
          (∑ r : TaggedIndependentChoice I copies (sampledStar I copies p).leaves,
            if (r i).1 = Q then
              (uniformLaw (TaggedIndependentChoice I copies
                (sampledStar I copies p).leaves)).mass r
            else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              by_cases hr : (r i).1 = Q <;> simp [hr]
      _ = μ.mass p *
          (pushforward (fun r : TaggedIndependentChoice I copies
            (sampledStar I copies p).leaves => (r i).1)
            (uniformLaw (TaggedIndependentChoice I copies
              (sampledStar I copies p).leaves))).mass Q := rfl
      _ = μ.mass p * (κ (f p)).mass Q := by
        rw [taggedIndependentChoice_presented_coordinate I copies
          (sampledStar I copies p).leaves i]
        rfl
  calc
    _ = ∑ p : TaggedSample I copies J t h k,
        μ.mass p * (κ (f p)).mass Q := by
          apply Finset.sum_congr rfl
          intro p _
          exact hinner p
    _ = ∑ P : TaggedPresentedLeaf I copies J h,
        (pushforward f μ).mass P * (κ P).mass Q :=
          weightedKernel_sum_pushforward μ f κ Q
    _ = ∑ P : TaggedPresentedLeaf I copies J h,
        (uniformLaw (TaggedPresentedLeaf I copies J h)).mass P *
          (κ P).mass Q := by
          rw [show pushforward f μ =
            uniformLaw (TaggedPresentedLeaf I copies J h) from
            taggedSample_presented_coordinate_uniform I copies hcenter hleaf ht hh i]
    _ = (classResampledPresentedLaw I copies (J := J) (h := h)).mass Q := by
          change (∑ P : TaggedPresentedLeaf I copies J h,
            (uniformLaw (TaggedPresentedLeaf I copies J h)).mass P *
              (κ P).mass Q) =
            (∑ P : TaggedPresentedLeaf I copies J h, (κ P).mass Q) /
              Fintype.card (TaggedPresentedLeaf I copies J h)
          simp_rw [uniformLaw_apply]
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro P _
          ring

/-- Under the actual original draw, the i-th sampled class representative
has the uniform full-presented-leaf marginal. -/
theorem originalDraw_representative_coordinate_uniform {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) (i : Fin k) :
    pushforward (fun x : OriginalDraw I copies J t h k =>
      (x.representatives i).1)
      (originalLawFromTagged I copies hcenter hleaf) =
        uniformLaw (TaggedPresentedLeaf I copies J h) := by
  calc
    _ = pushforward (fun x : OriginalDraw I copies J t h k =>
        (x.representatives i).1)
        (pushforward (decodeDraw I copies)
          (taggedJointLaw I copies hcenter hleaf)) := by
          rw [originalLaw_pushforward_decode I copies hcenter hleaf]
    _ = pushforward (fun z : Σ p : TaggedSample I copies J t h k,
        TaggedIndependentChoice I copies (sampledStar I copies p).leaves =>
          (z.2 i).1)
        (taggedJointLaw I copies hcenter hleaf) := by
          rw [pushforward_comp]
          rfl
    _ = classResampledPresentedLaw I copies (J := J) (h := h) :=
      taggedJoint_representative_coordinate_eq_classResampled I copies
        hcenter hleaf ht hh i
    _ = uniformLaw (TaggedPresentedLeaf I copies J h) :=
      uniform_presented_classResample_stationary I copies

/-- The actual clique-resampled first question U'_i is uniform over every
eligible tagged U, for each fixed coordinate i of the original draw. -/
theorem originalDraw_resampledU_coordinate_uniform {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    [Nonempty (TaggedPresentedLeaf I copies J h)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J) (i : Fin k) :
    pushforward (fun x : OriginalDraw I copies J t h k =>
      presentedU I copies (x.representatives i).1)
      (originalLawFromTagged I copies hcenter hleaf) =
        uniformLaw (TaggedGoodU I copies J) := by
  calc
    _ = pushforward (presentedU I copies)
        (pushforward (fun x : OriginalDraw I copies J t h k =>
          (x.representatives i).1)
          (originalLawFromTagged I copies hcenter hleaf)) := by
            rw [pushforward_comp]
            rfl
    _ = pushforward (presentedU I copies)
        (uniformLaw (TaggedPresentedLeaf I copies J h)) := by
          rw [originalDraw_representative_coordinate_uniform I copies
            hcenter hleaf ht hh i]
    _ = uniformLaw (TaggedGoodU I copies J) :=
      uniform_presentedU_pushforward I copies hh

/-- The actual i-th clique-resampled question contributes at most `J ε₁`
to the *raw legitimate joint numerator*. The eligible-question conditioning
factor is retained, as required for the manuscript's YES comparison. -/
theorem resampledU_badRow_joint_le {J t h k : Nat}
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
    (ε₁ : ℚ) (hε : 0 ≤ ε₁)
    (hrow : 0 < Fintype.card (TaggedRow I copies))
    (herror : PositiveErrorAssignment I copies f ε₁)
    (i : Fin k) :
    eventMass
      (pushforward (fun x : OriginalDraw I copies J t h k =>
        (originalUEquiv I copies J).symm
          (presentedU I copies (x.representatives i).1))
        (originalLawFromTagged I copies hcenter hleaf))
      (badOriginalU I copies J f) *
      eventMass (uniformLaw (RawOrdered I copies J))
        (legitimate I copies J) ≤ (J : ℚ) * ε₁ := by
  have hdist :
      pushforward (fun x : OriginalDraw I copies J t h k =>
        (originalUEquiv I copies J).symm
          (presentedU I copies (x.representatives i).1))
        (originalLawFromTagged I copies hcenter hleaf) =
      pushforward (orderedToOriginalU I copies J)
        (orderedGoodLaw I copies J) := by
    calc
      _ = pushforward (originalUEquiv I copies J).symm
          (pushforward (fun x : OriginalDraw I copies J t h k =>
            presentedU I copies (x.representatives i).1)
            (originalLawFromTagged I copies hcenter hleaf)) := by
              rw [pushforward_comp]
              rfl
      _ = pushforward (originalUEquiv I copies J).symm
          (uniformLaw (TaggedGoodU I copies J)) := by
            rw [originalDraw_resampledU_coordinate_uniform I copies
              hcenter hleaf ht hh i]
      _ = pushforward (originalUEquiv I copies J).symm
          (pushforward (orderedToGoodU I copies J)
            (orderedGoodLaw I copies J)) := by
              rw [orderedGood_pushforward I copies J]
      _ = pushforward (orderedToOriginalU I copies J)
          (orderedGoodLaw I copies J) := by
            rw [pushforward_comp]
            rfl
  rw [hdist, conditioned_badU_joint_eq_raw I copies J f]
  exact raw_original_joint_le I copies J f ε₁ hε hrow herror

end
end PvNP.RealizableHardness.ActualResampledQuestionMarginal
