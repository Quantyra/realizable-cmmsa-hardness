import PvNP.RealizableHardness.ActualOriginalLawAmplification
import PvNP.RealizableHardness.ActualNumericSideExtension
import PvNP.RealizableHardness.ActualSelectedHSideAgreement
import PvNP.RealizableHardness.ActualNumericRobustReal

/-! Concrete original-law advice and full H-side decoder integration.
This offer binds the original complement/advice law to the selected actual
raw table. It is an uncompiled source offer. -/
namespace PvNP.RealizableHardness.ActualOriginalLawFullDecoderIntegration

open PvNP.RealizableHardness
open ActualOriginalLawAmplification ActualNumericSideExtension
open ActualSelectedHSideAgreement ActualHSideFullZoom ActualNumericRobustReal
open ActualTaggedComplementIncidence ActualTaggedMZSideDraw
open ActualTaggedFixedCenterGeometry ActualTaggedSelectedDecoderBridge
open ActualTaggedComplementStarDensityBridge ActualTaggedConcreteStarLaw
open ActualFiniteLaw ActualMaximalPairLadder GrassmannCounting
open ActualNumericExplicitHeight ActualNumericSourceHeight
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open SamplerParameters
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J)

private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

/-- The center transported from an actual complement has precisely the
original advice as its inverse image in that complement. -/
private theorem sideCenter_comap_eq
    {a : Nat} (A : SideComplement I copies U) (QA : Grass A.1 a) :
    (centerInComplementEquiv I copies U A a QA).1.1.val.comap A.1.subtype = QA.val := by
  change (QA.val.map A.1.subtype).comap A.1.subtype = QA.val
  exact Submodule.comap_map_eq_of_injective A.1.injective_subtype QA.val

/-- The bounded ordinary and Zoom carriers have the same Grassmann leaves. -/
private def boundedOrdinaryZoomEquiv
    {a h : Nat} (A : SideComplement I copies U)
    (QA : Grass A.1 a) (P : DecodedPair QA (2 * h))
    (K : SideCenter I copies U a) (hKA : K.1.val <= A.1)
    (hcenter : K.1.val.comap A.1.subtype = QA.val) :
    {L : OrdinaryLeaf I copies U A K hKA h // L.1.val <= P.W} ≃ Zoom QA P where
  toFun L := by
    have hQA : QA.val <= L.1.1.val := by
      rw [← hcenter]
      exact L.1.2
    exact ⟨L.1.1, ⟨hQA, L.2⟩⟩
  invFun z := by
    have hK : K.1.val.comap A.1.subtype <= z.1.val := by
      rw [hcenter]
      exact z.2.1
    exact ⟨⟨z.1, hK⟩, z.2.2⟩
  left_inv L := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
/-- The fixed-table ordinary event is the Zoom agreement event, with the
orientation reversal handled pointwise. -/
private theorem actualOrdinaryAgreement_iff_zoomAgreesOn
    {a h : Nat} (A : SideComplement I copies U)
    (QA : Grass A.1 a) (P : DecodedPair QA (2 * h))
    (K : SideCenter I copies U a) (hKA : K.1.val <= A.1)
    (hcenter : K.1.val.comap A.1.subtype = QA.val)
    (Traw : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (L : {L : OrdinaryLeaf I copies U A K hKA h // L.1.val <= P.W}) :
    actualOrdinaryAgreement I copies U A P.W P.g K hKA L.1 L.2 Traw s ↔
      AgreesOn (transportedLeafTable I copies U A
        (taggedSelectedDomainTable I copies Traw s)) (P := P)
        (boundedOrdinaryZoomEquiv I copies U A QA P K hKA hcenter L).1
        (boundedOrdinaryZoomEquiv I copies U A QA P K hKA hcenter L).2.2 := by
  constructor
  · intro hagree x
    have hx := LinearMap.congr_fun hagree x
    exact hx.symm
  · intro hagree
    ext x
    exact (hagree x).symm

/-- The two finite agreement ratios are exactly equal; this statement keeps
the actual transported global table and the original raw representative. -/
private theorem actualOrdinaryRatio_eq_zoomAgreement
    {a h : Nat} (A : SideComplement I copies U)
    (QA : Grass A.1 a) (P : DecodedPair QA (2 * h))
    (K : SideCenter I copies U a) (hKA : K.1.val <= A.1)
    (hcenter : K.1.val.comap A.1.subtype = QA.val)
    (Traw : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (hzoom : Fintype.card (Zoom QA P) ≠ 0) :
    (Fintype.card {L : {L : OrdinaryLeaf I copies U A K hKA h // L.1.val <= P.W} //
      actualOrdinaryAgreement I copies U A P.W P.g K hKA L.1 L.2 Traw s} : Rat) /
      Fintype.card {L : OrdinaryLeaf I copies U A K hKA h // L.1.val <= P.W} =
    agreement (transportedLeafTable I copies U A
      (taggedSelectedDomainTable I copies Traw s)) QA P := by
  let e := boundedOrdinaryZoomEquiv I copies U A QA P K hKA hcenter
  let goodOrdinary :
      {L : OrdinaryLeaf I copies U A K hKA h // L.1.val <= P.W} → Prop :=
    fun L => actualOrdinaryAgreement I copies U A P.W P.g K hKA
      L.1 L.2 Traw s
  let goodZoom : Zoom QA P → Prop :=
    fun z => AgreesOn (transportedLeafTable I copies U A
      (taggedSelectedDomainTable I copies Traw s)) (P := P) z.1 z.2.2
  have hevent : ∀ L, goodOrdinary L ↔ goodZoom (e L) := by
    intro L
    exact actualOrdinaryAgreement_iff_zoomAgreesOn
      I copies U A QA P K hKA hcenter Traw s L
  have hratio := rationalAgreement_eq_of_carrierEquiv e goodOrdinary goodZoom hevent
  have hagreement := agreement_eq_fraction_of_nonempty
    (transportedLeafTable I copies U A (taggedSelectedDomainTable I copies Traw s))
    QA P hzoom
  calc
    _ = (Fintype.card {z : Zoom QA P // goodZoom z} : Rat) / Fintype.card (Zoom QA P) := hratio
    _ = agreement (transportedLeafTable I copies U A
      (taggedSelectedDomainTable I copies Traw s)) QA P := hagreement.symm

/-- One literal ordinary success yields the actual H-side full decoder. The
ordinary Zoom supplies every leaf and window nonemptiness input. -/
theorem actual_success_to_full_hside_agreement
    {L m samplerA a : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U) (QA : Grass A.1 a)
    (P : DecodedPair QA (2 * hBlock L m))
    (Traw : TaggedRawVertexTable I copies (blocks samplerA (hBlock L m))
      (hBlock L m))
    (s : TaggedRepresentativeChoice I copies (blocks samplerA (hBlock L m))
      (hBlock L m))
    (ha : a <= numericRankThreshold m)
    (hbudget : a + codim P.W = numericRankThreshold m)
    (hagree : refreshThreshold m (hBlock L m) / 2 <
      (agreement (transportedLeafTable I copies U A
        (taggedSelectedDomainTable I copies Traw s)) QA P : Real)) :
    let Kc := centerInComplementEquiv I copies U A a QA
    let K := Kc.1
    let hKW : K.1.val <= sideWindow I copies U A P.W := by
      have hmap : K.1.val = QA.val.map A.1.subtype := by
        change (QA.val.map A.1.subtype) = _
        rfl
      rw [hmap]
      exact (complement_map_le_sideWindow_iff I copies U A P.W QA.val).2 P.hQW
    refreshThreshold m (hBlock L m) / 3 <
      (agreement (totalHLeafTable I copies U Traw s) K.1
        (sideDecodedPair I copies U A P.W P.g K hKW) : Real) := by
  classical
  let h := hBlock L m
  let J' := blocks samplerA h
  let r := numericRankThreshold m
  let Kc := centerInComplementEquiv I copies U A a QA
  let K := Kc.1
  have hKA : K.1.val <= A.1 := Kc.2
  have hcenter : K.1.val.comap A.1.subtype = QA.val := by
    simpa [K, Kc] using sideCenter_comap_eq I copies U A QA
  have hKW : K.1.val <= sideWindow I copies U A P.W := by
    have hmap : K.1.val = QA.val.map A.1.subtype := by
      change (QA.val.map A.1.subtype) = _
      rfl
    rw [hmap]
    exact (complement_map_le_sideWindow_iff I copies U A P.W QA.val).2 P.hQW
  have hZoom : Fintype.card (Zoom QA P) ≠ 0 := by
    intro hzero
    have hzeroRat : agreement
        (transportedLeafTable I copies U A (taggedSelectedDomainTable I copies Traw s))
        QA P = 0 := agreement_eq_zero_of_empty
          (transportedLeafTable I copies U A (taggedSelectedDomainTable I copies Traw s))
          QA P hzero
    have hepos : 0 < refreshThreshold m h / 2 := by
      unfold refreshThreshold
      positivity
    rw [hzeroRat] at hagree
    linarith
  have hZoomPos : 0 < Fintype.card (Zoom QA P) := Nat.pos_of_ne_zero hZoom
  letI : Nonempty (Zoom QA P) := Fintype.card_pos_iff.mp hZoomPos
  obtain ⟨z⟩ := (inferInstance : Nonempty (Zoom QA P))
  let ordinary := (boundedOrdinaryZoomEquiv I copies U A QA P K hKA hcenter).symm z
  let Lc := ordinaryCenterToSide I copies U A ordinary.1.1
  have hQA_L : QA.val <= ordinary.1.1.val := by
    rw [← hcenter]
    exact ordinary.1.2
  have hKmap : K.1.val = QA.val.map A.1.subtype := by
    change (QA.val.map A.1.subtype) = _
    rfl
  have hKLeaf : K.1.val <= Lc.1.1.val := by
    change K.1.val <= ordinary.1.1.val.map A.1.subtype
    rw [hKmap]
    exact Submodule.map_mono hQA_L
  let sideL : SideLeaf I copies U h K := ⟨Lc.1.1, Lc.1.2, hKLeaf⟩
  letI : Nonempty (SideLeaf I copies U h K) := ⟨sideL⟩
  let boundedFull := boundedOrdinaryFullEquiv I copies U A K hKA P.W ordinary
  have hWindow : Nonempty {D : SideFullDomain I copies U K h //
      D.1 <= sideWindow I copies U A P.W} := ⟨boundedFull⟩
  obtain ⟨D⟩ := hWindow
  letI : Nonempty (SideFullDomain I copies U K h) := ⟨D.1⟩
  have guards := selected_robust_dimension_guards base cutoff hA hsel
  change RobustDimensionGuards m h samplerA at guards
  rcases guards with ⟨_hbsq, h8r, _h16, _hquad, hdim, _hlarge, _hcoef⟩
  have hhJ : h <= J' := by omega
  have hta : a <= 2 * h := by omega
  have hc : codim P.W <= r := by omega
  have hcodim : Module.finrank (ZMod 2) A.1 = codim P.W +
      Module.finrank (ZMod 2) P.W := by
    have hWle : Module.finrank (ZMod 2) P.W <= Module.finrank (ZMod 2) A.1 := P.W.finrank_le
    unfold codim
    omega
  have hratioIdentity := actualSideLeaf_k1_originalRatio_eq_ordinaryRatio
    (I := I) (copies := copies) (J := J') U A K hKA hta hhJ
    P.W P.g Traw s hWindow
  have hOrdRatio := actualOrdinaryRatio_eq_zoomAgreement
    (I := I) (copies := copies) (J := J') U A QA P K hKA hcenter
    Traw s hZoom
  have hsideRatio : refreshThreshold m h / 2 <
      (originalSideRestrictionRatio I copies U A P.W P.g K Traw s : Real) := by
    rw [hratioIdentity, hOrdRatio]
    exact hagree
  have hfull := selected_actual_hside_full_agreement
    (I := I) (copies := copies) base cutoff hA hsel U A P.W P.g K hKW
    ha hc hcodim Traw s hsideRatio
  simpa [h, K, Kc] using hfull

/-- An advice is favorable when it is embedded from an actual complement and
admits the canonical H-window extension with full-zoom agreement above e/3. -/
def actualFullDecoderFavorable
    {a h : Nat} (e : Real) (r : Nat)
    (Traw : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a) : Prop :=
  ∃ A : SideComplement I copies U,
  ∃ QA : Grass A.1 a,
  ∃ P : DecodedPair QA (2 * h),
    QA.val.map A.1.subtype = Q.val ∧
    a + codim P.W = r ∧
    ∃ hKW : (centerInComplementEquiv I copies U A a QA).1.1.val <=
        sideWindow I copies U A P.W,
      e / 3 < (agreement (totalHLeafTable I copies U Traw s)
        (centerInComplementEquiv I copies U A a QA).1.1
        (sideDecodedPair I copies U A P.W P.g
          (centerInComplementEquiv I copies U A a QA).1 hKW) : Real)

/-- Every favorable embedded advice carries a decoder on that exact ambient
Grassmann object. The whole dependent pair is transported along subtype
extensionality, preserving its window and linear functional. -/
theorem actualFullDecoderFavorable_exists_actualDecodedPair
    {a h : Nat} (e : Real) (r : Nat)
    (Traw : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a)
    (hfav : actualFullDecoderFavorable I copies U e r Traw s Q) :
    ∃ P : DecodedPair Q (2 * h),
      codim P.W ≤ r ∧
      ∃ hHW : H I copies U ≤ P.W,
        P.g.comp ((H I copies U).inclusion hHW) = sideCanonicalRhs I copies U ∧
      e / 3 < (agreement (totalHLeafTable I copies U Traw s) Q P : Real) := by
  classical
  rcases hfav with ⟨A, QA, P0, hembed, hbudget, hKW, hagree⟩
  let Kc := centerInComplementEquiv I copies U A a QA
  have hKQ : Kc.1.1 = Q := by
    apply Subtype.ext
    exact hembed.symm
  let Pside := sideDecodedPair I copies U A P0.W P0.g Kc.1 hKW
  let P : DecodedPair Q (2 * h) :=
    Eq.mp (congrArg (fun Q' => DecodedPair Q' (2 * h)) hKQ) Pside
  cases hKQ
  let q := questionOf I copies U (sideToCenter I copies U Kc.1)
  have hE : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by
    change Module.finrank (ZMod 2) (coordinateSpaceOf I copies q) = 3 * J
    exact taggedCoordinate_finrank I copies q
  have hcodimA : Module.finrank (ZMod 2) A.1 =
      codim P0.W + Module.finrank (ZMod 2) P0.W := by
    have hW := P0.W.finrank_le
    unfold codim
    omega
  have hwindowBudget := sideWindow_finrank_budget
    (I := I) (copies := copies) (U := U) (J := J) A Kc.1 P0.W hcodimA
  have hwindowCodim : codim (sideWindow I copies U A P0.W) = codim P0.W := by
    unfold codim at hwindowBudget ⊢
    rw [hE]
    omega
  refine ⟨P, ?_, ?_⟩
  · change codim (sideWindow I copies U A P0.W) ≤ r
    rw [hwindowCodim]
    omega
  · refine ⟨le_sup_left, ?_, ?_⟩
    · change (sideExtensionOnWindow I copies U A P0.W
        (sideCanonicalRhs I copies U) P0.g).comp
          ((sideWindow I copies U A P0.W).inclusion le_sup_left) =
            sideCanonicalRhs I copies U
      exact sideExtensionOnWindow_restrict_H I copies U A P0.W
        (sideCanonicalRhs I copies U) P0.g
    · change e / 3 <
        (agreement (totalHLeafTable I copies U Traw s) Kc.1.1 Pside : Real)
      simpa [Kc] using hagree
/-- A successful original draw implies the concrete full-decoder predicate on
its embedded transverse advice. -/
theorem actual_success_implies_fullDecoderFavorable
    {L m samplerA a : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U) (QA : Grass A.1 a)
    (Traw : TaggedRawVertexTable I copies (blocks samplerA (hBlock L m))
      (hBlock L m))
    (s : TaggedRepresentativeChoice I copies (blocks samplerA (hBlock L m))
      (hBlock L m))
    (ha : a <= numericRankThreshold m)
    (hs : actualComplementSuccess (a := a) (d := 2 * hBlock L m)
      I copies U A QA (taggedSelectedDomainTable I copies Traw s)
      (refreshThreshold m (hBlock L m)) (numericRankThreshold m)) :
    actualFullDecoderFavorable I copies U (refreshThreshold m (hBlock L m))
      (numericRankThreshold m) Traw s
      ⟨QA.val.map A.1.subtype, by
        rw [Submodule.finrank_map_subtype_eq]
        exact QA.property⟩ := by
  classical
  rcases hs with ⟨P, hbudget, hagree⟩
  let h := hBlock L m
  have hfull := actual_success_to_full_hside_agreement
    (I := I) (copies := copies) base cutoff hA hsel U A QA P Traw s ha hbudget hagree
  let Kc := centerInComplementEquiv I copies U A a QA
  have hmap : QA.val.map A.1.subtype = Kc.1.1.val := by
    change QA.val.map A.1.subtype =
      (centerInComplementEquiv I copies U A a QA).1.1.val
    simp [centerInComplementEquiv, ordinaryCenterToSide]
  have hKW : Kc.1.1.val <= sideWindow I copies U A P.W := by
    have hK : Kc.1.1.val = QA.val.map A.1.subtype := hmap.symm
    rw [hK]
    exact (complement_map_le_sideWindow_iff I copies U A P.W QA.val).2 P.hQW
  refine ⟨A, QA, P, ?_, hbudget, ?_⟩
  · exact hmap
  · refine ⟨hKW, ?_⟩
    simpa [h, Kc] using hfull
/-- The literal original A-first event, H11 incidence, all-advice correction,
and selected full-zoom decoder yield the quantitative full-Grassmann bound. -/
theorem actual_original_law_full_decoder_probability_lower
    {L m samplerA : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (U' : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (C : TaggedCenterTable I copies)
    (Traw : TaggedRawVertexTable I copies (blocks samplerA (hBlock L m))
      (hBlock L m))
    (s : TaggedRepresentativeChoice I copies (blocks samplerA (hBlock L m))
      (hBlock L m))
    (hside : 8 * successMargin (badExponent m (hBlock L m)) <=
      sideConditionalDensity I copies U' (leafT m (hBlock L m))
        (hBlock L m) m C (taggedSelectedDomainTable I copies Traw s)) :
    ∃ a : Fin (numericRankThreshold m + 1),
      (1 : Rat) / (2 : Rat) ^ (6 * (hBlock L m) ^ 2) <=
        ((Finset.univ.filter (fun Q : Grass (coordinateSpace
          (taggedSource I copies).support U'.1) a.val =>
            Q.val ⊓ H I copies U' = ⊥ ∧
            actualFullDecoderFavorable I copies U'
              (refreshThreshold m (hBlock L m)) (numericRankThreshold m)
              Traw s Q)).card : Rat) /
          gaussian (3 * blocks samplerA (hBlock L m)) a.val := by
  classical
  let h := hBlock L m
  let J' := blocks samplerA h
  let r := numericRankThreshold m
  let Tglobal := taggedSelectedDomainTable I copies Traw s
  let S : Rat := successMargin (badExponent m h)
  let p1 : Rat := 2 * S ^ 2 /
    ((m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * ((r : Rat) + 1))
  let p3 : Rat := 2 * S ^ 2 /
    ((2 : Rat) ^ (4 * h ^ 2) * (m : Rat) * ((r : Rat) + 1) ^ 3)
  have hbase := numericSourceBase_eq base
  have hsel' : selector
      (fun j => max (analyticSourceHeightFloor (numericBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat) := by
    simpa [numericSourceFloor, hbase] using hsel
  have hspectral := selected_spectral_parameters (numericBase base) cutoff hsel'
  rcases hspectral with ⟨_, _, _, _, _, hsplit0, _, _, _, _, _, _⟩
  have hsplit : leafT m h + leafK m h = 2 * h := by
    simpa [h] using hsplit0
  have hheight := selected_numeric_height (numericBase base) cutoff
    (by simpa only [hbase] using hsel')
  rcases hheight with ⟨hm, _hr, hbaseHeight, _, _⟩
  have hamp := actual_original_law_amplification
    (I := I) (copies := copies) (J := J') (U := U') base cutoff hA hsel rfl
    C Tglobal (by simpa [Tglobal, h] using hside)
  obtain ⟨a, hmass0⟩ := hamp
  let success : (A : SideComplement I copies U') → Grass A.1 a.val → Prop :=
    fun A QA => actualComplementSuccess (a := a.val)
      (d := leafT m h + leafK m h) I copies U' A QA Tglobal
      (refreshThreshold m h) r
  have hmass : p1 <= actualAfirstEventMass I copies U' success := by
    simpa [p1, S, success, Tglobal, h, r] using hmass0
  have hnuma : a.val <= r := Nat.le_of_lt_succ a.isLt
  have hfalse_imp (A : SideComplement I copies U') (QA : Grass A.1 a.val)
      (hs : success A QA) :
      actualFullDecoderFavorable I copies U' (refreshThreshold m h) r Traw s
        ⟨QA.val.map A.1.subtype, by
          rw [Submodule.finrank_map_subtype_eq]
          exact QA.property⟩ := by
    rcases hs with ⟨P0, hbudget0, hagree0⟩
    let P : DecodedPair QA (2 * h) :=
      Eq.mp (congrArg (DecodedPair QA) hsplit) P0
    have hbudget : a.val + codim P.W = r := by
      simpa [P] using hbudget0
    have hagree : refreshThreshold m h / 2 <
        (agreement (transportedLeafTable I copies U' A Tglobal) QA P : Real) := by
      simpa [P, Tglobal, h] using hagree0
    have hsuccess : actualComplementSuccess (a := a.val) (d := 2 * h)
        I copies U' A QA Tglobal (refreshThreshold m h) r :=
      ⟨P, hbudget, hagree⟩
    exact actual_success_implies_fullDecoderFavorable
      (I := I) (copies := copies) base cutoff hA hsel U' A QA Traw s hnuma hsuccess
  have hSpos : 0 < S := by
    dsimp [S, ActualStarAcceptedGoodMass.successMargin]
    positivity
  have hp1pos : 0 < p1 := by
    dsimp [p1]
    have hmpos : 0 < m := by omega
    positivity
  have hsuccessExists : ∃ A (QA : Grass A.1 a.val), success A QA := by
    by_contra hnone
    have hno : ∀ A (QA : Grass A.1 a.val), ¬ success A QA := by
      intro A QA hsuccess
      exact hnone ⟨A, QA, hsuccess⟩
    have hzero : actualAfirstEventMass I copies U' success = 0 := by
      unfold actualAfirstEventMass
      simp [success, hno]
    linarith [hmass, hp1pos, hzero]
  obtain ⟨A0, QA0, hs0⟩ := hsuccessExists
  let K0 := (centerInComplementEquiv I copies U' A0 a.val QA0).1
  let favorable : Grass (coordinateSpace (taggedSource I copies).support U'.1) a.val → Prop :=
    actualFullDecoderFavorable I copies U' (refreshThreshold m h) r Traw s
  have hpoint : ∀ A QA, success A QA →
      favorable ((centerInComplementEquiv I copies U' A a.val QA).1.1) := by
    intro A QA hs
    have hf := hfalse_imp A QA hs
    simpa [favorable, actualFullDecoderFavorable,
      centerInComplementEquiv, ordinaryCenterToSide] using hf
  have hinc := actual_original_Afirst_complementAdvice_event_le_transverse_event
    (I := I) (copies := copies) (J := J') (U := U') K0
    (by
      have guards := selected_robust_dimension_guards base cutoff hA hsel
      change RobustDimensionGuards m h samplerA at guards
      rcases guards with ⟨_, h8r, _, _, hdim, _, _⟩
      omega)
    favorable success hpoint
  have hmassInc : p1 <= eventMass (uniformLaw (SideCenter I copies U' a.val))
      (Finset.univ.filter fun K => favorable K.1) := by
    have hinc' : actualAfirstEventMass I copies U' success <=
        eventMass (uniformLaw (SideCenter I copies U' a.val))
          (Finset.univ.filter fun K => favorable K.1) := by
      simpa [actualAfirstEventMass, success, mul_ite, mul_one, mul_zero] using hinc
    exact hmass.trans hinc'
  have hh : numericHnum m <= h :=
    (Nat.le_max_right (base m) (numericHnum m)).trans hbaseHeight
  have guards := selected_robust_dimension_guards base cutoff hA hsel
  change RobustDimensionGuards m h samplerA at guards
  rcases guards with ⟨_hbsq, h8r, _h16, _hquad, hdim, _hlarge, _hcoef⟩
  have h2J : r + 1 <= 2 * J' := by omega
  have hslack : J' + a.val + 1 <= 3 * J' := by omega
  have hfactor : (r : Rat) + 1 <= ((r : Rat) + 1) ^ 3 := by
    have hr : 1 <= (r : Rat) + 1 := by exact_mod_cast Nat.le_add_left 1 r
    nlinarith [sq_nonneg (((r : Rat) + 1) - 1)]
  have hdenpos1 : 0 <
      (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * ((r : Rat) + 1) := by
    positivity
  have hdenpos3 : 0 <
      (2 : Rat) ^ (4 * h ^ 2) * (m : Rat) * ((r : Rat) + 1) ^ 3 := by
    positivity
  have hB3leB1 : p3 <= p1 := by
    apply (div_le_div_iff₀ hdenpos3 hdenpos1).2
    dsimp [p3, p1]
    have hnum : 0 <= 2 * S ^ 2 := by positivity
    have hden : (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * ((r : Rat) + 1) <=
        (2 : Rat) ^ (4 * h ^ 2) * (m : Rat) * ((r : Rat) + 1) ^ 3 := by
      calc
        _ = (2 : Rat) ^ (4 * h ^ 2) * (m : Rat) * ((r : Rat) + 1) := by ring
        _ <= (2 : Rat) ^ (4 * h ^ 2) * (m : Rat) * ((r : Rat) + 1) ^ 3 := by
          gcongr
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hp3pos : 0 <= p3 := by positivity
  have hShalf := ActualStarAcceptedGoodMass.successMargin_half_lt_one
    (badExponent m h)
  have hSlt2 : S < 2 := by
    dsimp [S]
    have := hShalf
    linarith
  have hmRat : (256 : Rat) <= m := by exact_mod_cast hm
  have hpow1 : (1 : Rat) <= (2 : Rat) ^ (4 * h ^ 2) := one_le_pow₀ (by norm_num)
  have hrplus1 : (1 : Rat) <= (r : Rat) + 1 := by exact_mod_cast Nat.le_add_left 1 r
  have hden256 : (256 : Rat) <=
      (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * ((r : Rat) + 1) := by
    calc
      _ = 256 * 1 * 1 := by ring
      _ <= (m : Rat) * 1 * 1 := by gcongr
      _ <= (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * 1 := by gcongr
      _ <= _ := by gcongr
  have hp1le1 : p1 <= 1 := by
    apply (div_le_one₀ hdenpos1).2
    dsimp [p1]
    nlinarith [sq_nonneg (S - 2), hSlt2, hden256]
  have hp3le1 : p3 <= 1 := hB3leB1.trans hp1le1
  let eTrans : SideCenter I copies U' a.val ≃
      {Q : Grass (coordinateSpace (taggedSource I copies).support U'.1) a.val //
        Q.val ⊓ H I copies U' = ⊥} :=
    sideCenterEquiv_allTransverseAdvice I copies U' a.val
  let transCarrier := {Q : Grass (coordinateSpace (taggedSource I copies).support U'.1) a.val //
    Q.val ⊓ H I copies U' = ⊥}
  let centerEvent : Finset (SideCenter I copies U' a.val) :=
    Finset.univ.filter fun K => favorable K.1
  let transverseEvent : Finset transCarrier :=
    Finset.univ.filter fun Q => favorable Q.1
  letI : Nonempty transCarrier := ⟨eTrans K0⟩
  have hpushLaw := uniform_sideCenter_pushforward_transverseAdvice
    (I := I) (copies := copies) (U := U') (a := a.val)
  have hpushEvent := eventMass_pushforward eTrans
    (uniformLaw (SideCenter I copies U' a.val)) transverseEvent
  rw [hpushLaw] at hpushEvent
  have hpre : preimageEvent eTrans transverseEvent = centerEvent := by
    ext K
    simp [preimageEvent, transverseEvent, centerEvent, eTrans, favorable]
  rw [hpre] at hpushEvent
  have hcenterRatio := eventMass_uniform_eq_card_ratio centerEvent
  have htransRatio := eventMass_uniform_eq_card_ratio transverseEvent
  have htransLower : p3 <=
      (transverseEvent.card : Rat) / Fintype.card transCarrier := by
    calc
      p3 <= eventMass (uniformLaw (SideCenter I copies U' a.val)) centerEvent := hB3leB1.trans hmassInc
      _ = eventMass (uniformLaw transCarrier) transverseEvent := hpushEvent.symm
      _ = (transverseEvent.card : Rat) / Fintype.card transCarrier := htransRatio
  have htrans :
      ((Finset.univ.filter fun Q : Grass (coordinateSpace (taggedSource I copies).support U'.1) a.val =>
        Q.val ⊓ H I copies U' = ⊥ ∧ favorable Q).card : Rat) /
        (Finset.univ.filter fun Q : Grass (coordinateSpace (taggedSource I copies).support U'.1) a.val =>
          Q.val ⊓ H I copies U' = ⊥).card >= p3 := by
    simpa [transverseEvent, transCarrier, Finset.card_filter] using htransLower
  have hbound := actualAllAdvice_transverseEvent_mass_lower
    (I := I) (copies := copies) (J := J') (U := U') K0
    (by omega) hslack favorable p3 hp3pos hp3le1 htrans
  have hnum := numeric_all_advice_probability_lower hm hh hA hnuma
  have hexp : a.val + 1 <= 2 * J' := by omega
  let delta : Rat := 1 / (2 : Rat) ^ (2 * J' - a.val - 1)
  have hdelta : delta = (2 : Rat) ^ (a.val + 1) /
      (2 : Rat) ^ (2 * J') := by
    dsimp [delta]
    have hNat : (2 * J' - a.val - 1) + (a.val + 1) = 2 * J' := by omega
    rw [← hNat, pow_add]
    field_simp
  have hnumRat :
      (1 : Rat) / (2 : Rat) ^ (6 * h ^ 2) <= p3 - delta := by
    have hnumCast := hnum
    exact_mod_cast (by
      simpa [p3, S, delta, hdelta, ActualStarAcceptedGoodMass.successMargin,
        Rat.cast_div, Rat.cast_pow] using hnumCast)
  have hfinal :
      (1 : Rat) / (2 : Rat) ^ (6 * h ^ 2) <=
        ((Finset.univ.filter (fun Q : Grass (coordinateSpace
          (taggedSource I copies).support U'.1) a.val =>
            Q.val ⊓ H I copies U' = ⊥ ∧ favorable Q)).card : Rat) /
          gaussian (3 * J') a.val := by
    exact hnumRat.trans (by simpa [delta] using hbound)
  exact ⟨a, by simpa [h, J', favorable, actualFullDecoderFavorable] using hfinal⟩

end
end PvNP.RealizableHardness.ActualOriginalLawFullDecoderIntegration
