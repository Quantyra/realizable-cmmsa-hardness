import PvNP.RealizableHardness.ActualComplementDensityMass
import PvNP.RealizableHardness.ActualDistinctAdviceAverage
import PvNP.RealizableHardness.ActualCoordinateStarDensity
import PvNP.RealizableHardness.ActualNumericSideExtension
import PvNP.RealizableHardness.ActualSelectedRefreshCoverAverage
import PvNP.RealizableHardness.ActualGlobalDensityBridge

/-! Actual complement-law averaging, followed by exact advice incidence and
H-side witness transport. This is an uncompiled source offer. -/
namespace PvNP.RealizableHardness.ActualOriginalLawAmplification

open PvNP.RealizableHardness
open ActualComplementDensityMass ActualDistinctAdviceAverage
open ActualCoordinateStarDensity ActualNumericSideExtension
open ActualComplementCoordinateMassBridge ActualDistinctAdviceCoverage
open ActualTaggedComplementIncidence ActualTaggedComplementStarDensityBridge
open ActualFiniteLaw ActualMaximalPairLadder ActualTaggedConcreteStarLaw
open ActualSelectedRefreshCoverAverageV2
open ActualGlobalDensityBridge
open ActualSelectedSpectralParameters ActualNumericExplicitHeight
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualNumericSourceHeight ActualNumericRobustReal
open ActualStarAcceptedGoodMass ActualStarFixedRhoDimensionGuard
open ActualStarSpanIntersection ActualTaggedFixedCenterGeometry
open GrassmannCounting ActualSourceStarLaw ActualTaggedMZSideDraw
open SamplerParameters
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat}
variable (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H := (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

/-- Success is defined on the actual complement and its actual advice space.
The decoded witness uses the same globally predrawn table restricted to the
ordinary complement leaf. -/
def actualComplementSuccess {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass A.1 a)
    (T : TaggedLeafTable I copies) (e : Real) (r : Nat) : Prop :=
  Exists fun P : DecodedPair Q d =>
    a + codim P.W = r /\
      e / 2 < (agreement (transportedLeafTable I copies U A T) Q P : Real)

/-- A successful witness has a canonical actual H-side window lift. The
statement retains the restriction identities on both summands of H+W'. -/
theorem actualComplementSuccess_has_H_extension {a d : Nat}
    (A : SideComplement I copies U) (Q : Grass A.1 a)
    (T : TaggedLeafTable I copies) (e : Real) (r : Nat)
    (hs : actualComplementSuccess (a := a) (d := d) I copies U A Q T e r) :
    Exists fun W' : Submodule (ZMod 2) A.1 =>
      Exists fun g : W' →ₗ[ZMod 2] ZMod 2 =>
        Exists fun F : sideWindow I copies U A W' →ₗ[ZMod 2] ZMod 2 =>
          Exists fun P : DecodedPair Q d =>
            a + codim P.W = r /\
            e / 2 < (agreement (transportedLeafTable I copies U A T) Q P : Real) /\
            W' = P.W /\ g = P.g /\
            F = sideExtensionOnWindow I copies U A W'
              (sideCanonicalRhs I copies U) g /\
            F.comp ((sideWindow I copies U A W').inclusion le_sup_left) =
              sideCanonicalRhs I copies U /\
            F.comp (sideWindowInclusionW I copies U A W') = g := by
  rcases hs with ⟨P, hbudget, hagree⟩
  refine ⟨P.W, P.g, sideExtensionOnWindow I copies U A P.W
    (sideCanonicalRhs I copies U) P.g, P, hbudget, hagree, rfl, rfl, rfl, ?_, ?_⟩
  · exact sideExtensionOnWindow_restrict_H I copies U A P.W
      (sideCanonicalRhs I copies U) P.g
  · exact sideExtensionOnWindow_restrict_W I copies U A P.W
      (sideCanonicalRhs I copies U) P.g

/-- The full-space favorable predicate is existential over actual complements.
It stores an actual advice subspace, exact-budget decoder, ordinary agreement,
and the canonical H-window extension; no complement is reweighted. -/
def actualHWindowFavorable {a d : Nat}
    (Q : Grass (E I copies U) a) (T : TaggedLeafTable I copies)
    (e : Real) (r : Nat) : Prop :=
  Exists fun A : SideComplement I copies U =>
    Exists fun QA : Grass A.1 a =>
      Exists fun P : DecodedPair QA d =>
        Exists fun F : sideWindow I copies U A P.W →ₗ[ZMod 2] ZMod 2 =>
          QA.val.map A.1.subtype = Q.val /\
          a + codim P.W = r /\
          e / 2 < (agreement (transportedLeafTable I copies U A T) QA P : Real) /\
          F = sideExtensionOnWindow I copies U A P.W
            (sideCanonicalRhs I copies U) P.g

/-- Every successful complement-first draw supplies the pointwise favorable
predicate on its embedded advice subspace. -/
theorem actualComplementSuccess_implies_HWindow {a d : Nat}
    (A : SideComplement I copies U) (QA : Grass A.1 a)
    (T : TaggedLeafTable I copies) (e : Real) (r : Nat)
    (hs : actualComplementSuccess (a := a) (d := d) I copies U A QA T e r) :
    actualHWindowFavorable (a := a) (d := d) I copies U
      (⟨QA.val.map A.1.subtype, by
        rw [Submodule.finrank_map_subtype_eq]
        exact QA.property⟩ : Grass (E I copies U) a) T e r := by
  rcases hs with ⟨P, hbudget, hagree⟩
  let QE : Grass (E I copies U) a :=
    ⟨QA.val.map A.1.subtype, by
      rw [Submodule.finrank_map_subtype_eq]
      exact QA.property⟩
  refine ⟨A, QA, P,
    sideExtensionOnWindow I copies U A P.W (sideCanonicalRhs I copies U) P.g,
    ?_, hbudget, hagree, rfl⟩
  change QE.val = (centerInComplementEquiv I copies U A a QA).1.1.val
  simp [QE, centerInComplementEquiv, ordinaryCenterToSide]

/-- The literal atom weights of the original complement-first, uniform-advice
law for an arbitrary success predicate depending on both A and Q. -/
def actualAfirstEventMass {a : Nat}
    (success : (A : SideComplement I copies U) → Grass A.1 a → Prop) : Rat :=
  ∑ A : SideComplement I copies U, ∑ Q : Grass A.1 a,
    ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
      ((1 : Rat) / Fintype.card (Grass A.1 a)) *
      (if success A Q then (1 : Rat) else 0)

/-- The actual complement-first mass of successful `(A,Q)` draws is bounded
by the uniform transverse full-space event whenever each success supplies the
same existential H-window witness. The exact complement dependence remains
inside the event and its original atom weights. -/
theorem actualHWindow_success_mass_le_transverse
    {a d : Nat} (K0 : SideCenter I copies U a) (ha : a ≤ 2 * J)
    (T : TaggedLeafTable I copies) (e : Real) (r : Nat) :
    actualAfirstEventMass I copies U
        (fun A Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r) ≤
      (letI : Nonempty (SideCenter I copies U a) := ⟨K0⟩
       eventMass (uniformLaw (SideCenter I copies U a))
         (Finset.univ.filter fun K =>
           actualHWindowFavorable (a := a) (d := d) I copies U K.1 T e r)) := by
  classical
  let success : (A : SideComplement I copies U) → Grass A.1 a → Prop :=
    fun A Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r
  let favorable : Grass (E I copies U) a → Prop :=
    fun Q => actualHWindowFavorable (a := a) (d := d) I copies U Q T e r
  have hpoint : ∀ A Q, success A Q →
      favorable ((centerInComplementEquiv I copies U A a Q).1.1) := by
    intro A Q hs
    have h := actualComplementSuccess_implies_HWindow (a := a) (d := d)
      I copies U A Q T e r hs
    simpa [success, favorable, actualHWindowFavorable,
      centerInComplementEquiv, ordinaryCenterToSide] using h
  have hmass := actual_original_Afirst_complementAdvice_event_le_transverse_event
    I copies U K0 ha favorable success hpoint
  simpa [actualAfirstEventMass, success, favorable, mul_ite, mul_one,
    mul_zero] using hmass

/-- Actual distinct-advice set for one sampled complement. -/
def actualComplementSuccessSet {a d : Nat}
    (A : SideComplement I copies U) (T : TaggedLeafTable I copies)
    (e : Real) (r : Nat) : Finset (Grass A.1 a) :=
  Finset.univ.filter fun Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r

def actualComplementSuccessFraction {a d : Nat}
    (A : SideComplement I copies U) (T : TaggedLeafTable I copies)
    (e : Real) (r : Nat) : Rat :=
  ((actualComplementSuccessSet (a := a) (d := d) I copies U A T e r).card : Rat) /
    Fintype.card (Grass A.1 a)

/-- A coordinate good-advice witness pulls back to an exact-budget actual
decoder with exactly the original agreement ratio on the same complement. -/
theorem coordinateGoodAdvice_to_actualComplementSuccess
    {r : Nat} (A : SideComplement I copies U)
    (T : TaggedLeafTable I copies) (e : Real) (d : Nat)
    (ia : Fin (r + 1)) (Qc : Grass (CoordAmbient J) ia.val)
    (hq : Qc ∈ goodAdvice (CoordAmbient J) d r
      (selectedCoordinateLeafTable I copies U A T) e ia) :
    actualComplementSuccess (a := ia.val) (d := d) I copies U A
      ((grassCoordinateEquiv I copies U A).symm Qc) T e r := by
  classical
  obtain ⟨Pc, hbudget, hagree⟩ :=
    (mem_goodAdvice_iff (CoordAmbient J) d r
      (selectedCoordinateLeafTable I copies U A T) e ia Qc).mp hq
  let P := pullbackDecodedPair I copies U A Qc Pc
  refine ⟨P, ?_, ?_⟩
  · rw [pullbackDecodedPair_codim I copies U A Qc Pc]
    exact hbudget
  · have hAgree := pullbackAgreement_eq I copies U A Qc Pc
      (transportedLeafTable I copies U A T)
    have hAgreeReal := congrArg (fun x : Rat => (x : Real)) hAgree
    rw [← hAgreeReal]
    simpa [selectedCoordinateLeafTable] using hagree
/-- Fixed-frame good advice injects into actual successful advice for each
complement. Pullback preserves the exact decoded-pair budget and agreement,
and the Grassmann equivalence preserves the uniform denominator. -/
theorem coordinate_fraction_le_actual_success_fraction
    {r : Nat} (A : SideComplement I copies U)
    (T : TaggedLeafTable I copies) (e : Real) (d : Nat)
    (ia : Fin (r + 1)) (ha : ia.val ≤ 2 * J) :
    goodAdviceFraction (CoordAmbient J) d r
        (selectedCoordinateLeafTable I copies U A T) e ia ≤
      actualComplementSuccessFraction (a := ia.val) (d := d) I copies U A T e r := by
  classical
  let ec := grassCoordinateEquiv I copies U A
  let gc := goodAdvice (CoordAmbient J) d r
    (selectedCoordinateLeafTable I copies U A T) e ia
  let ga := actualComplementSuccessSet (a := ia.val) (d := d) I copies U A T e r
  have hsubset : gc.image ec.symm ≤ ga := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨Qc, hQc, rfl⟩
    have hgood : Qc ∈ gc := by simpa [gc] using hQc
    simpa [ga, actualComplementSuccessSet] using
      coordinateGoodAdvice_to_actualComplementSuccess
        I copies U A T e d ia Qc hgood
  have hcard : gc.card ≤ ga.card := by
    calc
      gc.card = (gc.image ec.symm).card := by
        symm
        exact Finset.card_image_of_injective _ ec.symm.injective
      _ ≤ ga.card := Finset.card_le_card hsubset
  have hden : Fintype.card (Grass (CoordAmbient J) ia.val) =
      Fintype.card (Grass A.1 ia.val) := (Fintype.card_congr ec).symm
  have hcardActual : Fintype.card (Grass A.1 ia.val) = gaussian (2 * J) ia.val := by
    rw [card_grass, sideComplement_finrank I copies U A]
  have hdenpos : (Fintype.card (Grass A.1 ia.val) : Rat) > 0 := by
    rw [hcardActual]
    exact_mod_cast gaussian_pos ha
  rw [goodAdviceFraction, actualComplementSuccessFraction, hden]
  exact (div_le_div_iff_of_pos_right hdenpos).2 (by exact_mod_cast hcard)
/-- Literal conditional success fraction on one complement, with the actual
finite Grassmann denominator. -/
def actualComplementEventFraction {a : Nat}
    (A : SideComplement I copies U)
    (success : Grass A.1 a → Prop) : Rat :=
  ((Finset.univ.filter success).card : Rat) / Fintype.card (Grass A.1 a)

private theorem uniformIndicator_sum_eq_card_ratio
    {Ω : Type*} [Fintype Ω] (p : Ω → Prop)
    [DecidablePred p] :
    (∑ x : Ω, ((1 : Rat) / Fintype.card Ω) *
      (if p x then (1 : Rat) else 0)) =
      ((Finset.univ.filter p).card : Rat) / Fintype.card Ω := by
  classical
  calc
    _ = ∑ x in Finset.univ.filter p,
          (1 : Rat) / Fintype.card Ω := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    _ = _ := by
      simp [div_eq_mul_inv]

/-- The joint A-first draw law is exactly the expectation of the actual
conditional success fraction under the unchanged uniform-complement law. -/
theorem actualAfirstEventMass_eq_originalComplementExpectation
    {a : Nat}
    (success : (A : SideComplement I copies U) → Grass A.1 a → Prop) :
    actualAfirstEventMass I copies U success =
      ∑ A : SideComplement I copies U,
        (originalComplementLaw I copies U).mass A *
          actualComplementEventFraction I copies U A (success A) := by
  classical
  unfold actualAfirstEventMass
  calc
    _ = ∑ A : SideComplement I copies U,
          ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
            (∑ Q : Grass A.1 a,
              ((1 : Rat) / Fintype.card (Grass A.1 a)) *
                (if success A Q then (1 : Rat) else 0)) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q hQ
      ring
    _ = ∑ A : SideComplement I copies U,
          ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
            actualComplementEventFraction I copies U A (success A) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [uniformIndicator_sum_eq_card_ratio]
      rfl
    _ = _ := by
      simp_rw [originalComplementLaw_mass]
      rfl

/-- Average the actual fixed-frame good-advice fractions under the complete
original complement law, then select one dimension and lower-bound its actual
complement-first decoder-success mass. The event keeps the same original T. -/
theorem exists_dimension_actual_original_law_success_lower
    {d r : Nat} (T : TaggedLeafTable I copies) (e : Real)
    (G : Finset (SideComplement I copies U)) (D : Rat)
    (hlocal : ∀ A ∈ G, D ≤
      ∑ a : Fin (r + 1),
        goodAdviceFraction (CoordAmbient J) d r
          (selectedCoordinateLeafTable I copies U A T) e a)
    (hrd : r ≤ 2 * J) :
    ∃ a : Fin (r + 1),
      eventMass (originalComplementLaw I copies U) G * D / ((r : Rat) + 1) ≤
        actualAfirstEventMass I copies U
          (fun A Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r) := by
  classical
  obtain ⟨a, haverage⟩ := exists_dimension_original_law_fraction_lower
    (CoordAmbient J) d r (originalComplementLaw I copies U)
    (fun A => selectedCoordinateLeafTable I copies U A T) e G D hlocal
  have haDim : a.val ≤ 2 * J :=
    Nat.le_trans (Nat.le_of_lt_succ a.isLt) hrd
  have hpoint (A : SideComplement I copies U) :
      goodAdviceFraction (CoordAmbient J) d r
        (selectedCoordinateLeafTable I copies U A T) e a ≤
      actualComplementEventFraction I copies U A
        (fun Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r) := by
    simpa [actualComplementEventFraction, actualComplementSuccessFraction,
      actualComplementSuccessSet] using
      coordinate_fraction_le_actual_success_fraction
        I copies U A T e d a haDim
  have hsum :
      originalLawAdviceFraction (CoordAmbient J) d r
          (originalComplementLaw I copies U)
          (fun A => selectedCoordinateLeafTable I copies U A T) e a ≤
        ∑ A : SideComplement I copies U,
          (originalComplementLaw I copies U).mass A *
            actualComplementEventFraction I copies U A
              (fun Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r) := by
    unfold originalLawAdviceFraction
    apply Finset.sum_le_sum
    intro A hA
    exact mul_le_mul_of_nonneg_left (hpoint A)
      ((originalComplementLaw I copies U).nonneg A)
  have hevent := actualAfirstEventMass_eq_originalComplementExpectation
    I copies U (fun A Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r)
  refine ⟨a, ?_⟩
  calc
    _ ≤ originalLawAdviceFraction (CoordAmbient J) d r
          (originalComplementLaw I copies U)
          (fun A => selectedCoordinateLeafTable I copies U A T) e a := haverage
    _ ≤ actualAfirstEventMass I copies U
          (fun A Q => actualComplementSuccess (a := a) (d := d) I copies U A Q T e r) := by
      simpa only [hevent] using hsum

/-- Apply selected-refresh locally to an actual complement whose transported
ordinary star density is at least four times the selected success margin.
The star arity is the source repetition m, while samplerA sets only the
coordinate ambient dimension. -/
theorem actual_good_complement_local_advice_sum_lower
    {L m samplerA : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (hambient : J = blocks samplerA (hBlock L m))
    (A : SideComplement I copies U) (C : TaggedCenterTable I copies)
    (T : TaggedLeafTable I copies)
    (htd : leafT m (hBlock L m) <= 2 * hBlock L m)
    (hh : hBlock L m <= J)
    (hgood : 4 * (successMargin (badExponent m (hBlock L m)) : Rat) <= transportedStarDensity
      (t := leafT m (hBlock L m)) (h := hBlock L m) (k := m)
      I copies U A htd hh C T) :
    (successMargin (badExponent m (hBlock L m)) : Rat) /
      (2 * (m : Rat) * (2 : Rat) ^ (4 * (hBlock L m) ^ 2)) <=
      ∑ a : Fin (numericRankThreshold m + 1),
        goodAdviceFraction (CoordAmbient J)
          (leafT m (hBlock L m) + leafK m (hBlock L m))
          (numericRankThreshold m)
          (selectedCoordinateLeafTable I copies U A T)
          (refreshThreshold m (hBlock L m)) a := by
  classical
  subst J
  let h := hBlock L m
  let J' := blocks samplerA h
  let t := leafT m h
  let s := leafK m h
  let d := t + s
  let r := numericRankThreshold m
  let V := CoordAmbient J'
  let S : Rat := successMargin (badExponent m h)
  have hb := numericSourceBase_eq base
  have hsel' : selector
      (fun j => max (analyticSourceHeightFloor (numericBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat) := by
    simpa [numericSourceFloor, hb] using hsel
  have hp := selected_spectral_parameters (numericBase base) cutoff hsel'
  rcases hp with ⟨_, _, _, _, _, hsplit, _, _, _, _, _, _⟩
  have hsplit' : d = 2 * h := by
    dsimp [d, t, s, h]
    exact hsplit
  have htd' : t <= 2 * h := by
    rw [← hsplit']
    exact Nat.le_add_right _ _
  have hdA : 2 * h <= Module.finrank (ZMod 2) A.1 := by
    rw [sideComplement_finrank I copies U A]
    omega
  have hdV : 2 * h <= Module.finrank (ZMod 2) V := by
    rw [show Module.finrank (ZMod 2) V = 2 * J' by simp [V, CoordAmbient]]
    dsimp [J'] at hh
    omega
  have hcenter : Nonempty (Grass V t) := by
    apply Fintype.card_pos_iff.mp
    rw [card_grass]
    exact gaussian_pos (htd'.trans hdV)
  have hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d) := by
    intro K
    simpa only [hsplit'] using ActualSourceStarLaw.extension_nonempty K htd' hdV
  have hdimA : d <= Module.finrank (ZMod 2) A.1 := by
    rw [hsplit']
    exact hdA
  let Cc : CenterTable (V := V) t := selectedCoordinateCenterTable I copies U A C
  let Tc : LeafTable (V := V) d := selectedCoordinateLeafTable I copies U A T
  let T2 : LeafTable (V := V) (2 * h) :=
    Eq.mp (congrArg (fun q => LeafTable (V := V) q) hsplit') Tc
  have hcoord := starDensity_coordinate_eq (I := I) (copies := copies)
    (U := U) (J := J') (t := t) (d := 2 * h) (k := m) A htd' hdA
    (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T)
  have hstar : transportedStarDensity (t := t) (h := h) (k := m)
      I copies U A htd' (by simpa [J'] using hh) C T =
      StarDensity (V := V) (k := m) hcenter hleaf Cc Tc := by
    simpa [transportedStarDensity, V, Cc, Tc, T2, selectedCoordinateCenterTable,
      selectedCoordinateLeafTable, hsplit', hleaf] using hcoord
  have hscore : 4 * S <= StarDensity (V := V) (k := m) hcenter hleaf Cc Tc := by
    rw [← hstar]
    simpa [t, h, S] using hgood
  have hrefresh := selected_coordinate_refresh_cover_margin_four
    base cutoff hA hsel hcenter hleaf Cc Tc (by simpa [h, V, Cc, Tc] using hscore)
  have hstrict : S / (2 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) <
      ∑ a : Fin (numericRankThreshold m + 1),
        goodAdviceFraction V d r Tc (refreshThreshold m h) a := by
    simpa [h, d, r, V, Cc, Tc] using hrefresh
  exact le_of_lt (by simpa [h, d, r, V, Tc, S] using hstrict)

/-- Concrete original-complement-law amplification from the side-density
premise to one actual complement-first advice event. -/
theorem actual_original_law_amplification
    {L m samplerA : Nat} (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (hambient : J = blocks samplerA (hBlock L m))
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies)
    (hside : 8 * successMargin (badExponent m (hBlock L m)) <=
      sideConditionalDensity I copies U (leafT m (hBlock L m))
        (hBlock L m) m C T) :
    ∃ a : Fin (numericRankThreshold m + 1),
      (2 * (successMargin (badExponent m (hBlock L m)) : Rat) ^ 2) /
        ((m : Rat) * (2 : Rat) ^ (4 * (hBlock L m) ^ 2) *
          ((numericRankThreshold m : Rat) + 1)) <=
      actualAfirstEventMass I copies U
        (fun A Q => actualComplementSuccess (a := a.val)
          (d := leafT m (hBlock L m) + leafK m (hBlock L m))
          I copies U A Q T (refreshThreshold m (hBlock L m))
          (numericRankThreshold m)) := by
  classical
  subst J
  let h := hBlock L m
  let t := leafT m h
  let s := leafK m h
  let d := t + s
  let r := numericRankThreshold m
  let S : Rat := successMargin (badExponent m h)
  have hb := numericSourceBase_eq base
  have hsel' : selector
      (fun j => max (analyticSourceHeightFloor (numericBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat) := by
    simpa [numericSourceFloor, hb] using hsel
  have hp := selected_spectral_parameters (numericBase base) cutoff hsel'
  rcases hp with ⟨_, _, _, _, _, hsplit, _, _, _, _, _, _⟩
  have hsplit' : d = 2 * h := by
    dsimp [d, t, s, h]
    exact hsplit
  have hheight := selected_numeric_height (numericBase base) cutoff
    (by simpa only [hb] using hsel')
  rcases hheight with ⟨hm, hr, hbase, _, _⟩
  have hh : numericHnum m <= h :=
    (Nat.le_max_right (base m) (numericHnum m)).trans hbase
  have hJ : h <= blocks samplerA h := by
    have hsq : h ^ 2 < blocks samplerA h := by
      calc
        h ^ 2 = 1 * h ^ 2 := by simp
        _ <= samplerA * h ^ 2 := Nat.mul_le_mul_right _ hA
        _ < blocks samplerA h := numerator_lt_blocks samplerA h
    have hpos : 1 <= h := by omega
    have hle : h <= h ^ 2 := by nlinarith
    omega
  have htd : t <= 2 * h := by rw [← hsplit']; exact Nat.le_add_right _ _
  let G := goodComplementSet (t := t) (h := h) (k := m)
    I copies U htd hJ C T S
  have hmass := original_good_complement_mass_lower
    (t := t) (h := h) (k := m) I copies U htd hJ C T S
    (by dsimp [S]; positivity) (by simpa [t, h, S] using hside)
  have hmPos : 0 < m := by omega
  have hlocal : ∀ A ∈ G, S / (2 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) <=
      ∑ a : Fin (r + 1),
        goodAdviceFraction (CoordAmbient (blocks samplerA h)) d r
          (selectedCoordinateLeafTable I copies U A T)
          (refreshThreshold m h) a := by
    intro A hAin
    have hgood : 4 * S <= transportedStarDensity (t := t) (h := h) (k := m)
        I copies U A htd hJ C T :=
      (mem_goodComplementSet_iff (k := m) I copies U htd hJ C T S A).mp hAin
    simpa [t, h, d, r, S] using
      actual_good_complement_local_advice_sum_lower I copies U base cutoff hA hsel
        rfl A C T htd hJ (by simpa [S, h] using hgood)
  have hrd : r <= 2 * blocks samplerA h := by
    have hrank : r <= d := by
      dsimp [r, d, t, s]
      omega
    rw [hsplit'] at hrank
    omega
  have havg := exists_dimension_actual_original_law_success_lower
    I copies U (d := d) (r := r) T (refreshThreshold m h) G
    (S / (2 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2))) hlocal hrd
  rcases havg with ⟨a, hsuccess⟩
  have hD : 0 <= S / (2 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) := by positivity
  have hmassprod := mul_le_mul_of_nonneg_right hmass hD
  have hden : 0 < (r : Rat) + 1 := by positivity
  have hdenFactor : (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) ≠ 0 := by
    have hmRat : 0 < (m : Rat) := by exact_mod_cast hmPos
    positivity
  have hscale :
      (2 * S ^ 2) / ((m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * ((r : Rat) + 1)) <=
        eventMass (originalComplementLaw I copies U) G *
          (S / (2 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2))) / ((r : Rat) + 1) := by
    have hmassprod' := div_le_div_of_nonneg_right hmassprod (le_of_lt hden)
    have hEq : (4 * S) * (S / (2 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2))) /
        ((r : Rat) + 1) =
      (2 * S ^ 2) / ((m : Rat) * (2 : Rat) ^ (4 * h ^ 2) * ((r : Rat) + 1)) := by
      field_simp [hdenFactor, (ne_of_gt hden)]
      <;> ring
    rw [← hEq]
    exact hmassprod'
  refine ⟨a, ?_⟩
  exact hscale.trans (by simpa [r, h, d] using hsuccess)
end
end PvNP.RealizableHardness.ActualOriginalLawAmplification

