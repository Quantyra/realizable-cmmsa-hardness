import PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
import PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard
import PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
import PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
import PvNP.RealizableHardness.SamplerParameters

/-! Provisional B27/B29/B48 composition with separate source-row count and
ordered tuple arity. The selector, center, block height, increment dimension,
and threshold remain source-row indexed; `r ≤ nRows` is an explicit premise.
The law is the defined ordered `DomainDraw` law, not the manuscript physical
sampler. No acceptance, force-selection, or source-hardness claim is made. -/

namespace PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualStarFixedRhoTwoIndexGuard
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarDomainDrawTwoIndexEventBridge
open PvNP.RealizableHardness.SamplerParameters

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N nRows r L A : Nat}
variable {I : Instance N nRows}

/-- Full joint-rank failure for an ordered `r`-tuple under a fixed center
defined from the `nRows`-equation source instance. The quotient increment
rank is the source-row quantity `leafK nRows h`. -/
def domainDrawRankFailureEventTwoIndex
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (ht : leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows)
    (hh : hBlock L nRows ≤ blocks A (hBlock L nRows)) :
    Finset (Fin r → DomainDraw center (hBlock L nRows)) :=
  Finset.univ.filter fun draws =>
    Module.finrank (ZMod 2)
      (domainDrawJointImageArity center (hBlock L nRows) ht hh draws) ≠
        r * leafK nRows (hBlock L nRows)

/-- Two-index B49 bound: B27's tuple parameter is instantiated at `r`, while
all source-cutoff and numerical quantities stay at `nRows`. The selected
fixed center uses the actual same ordered `DomainDraw` law. -/
theorem selected_domainDraw_rankFailure_mass_lt_threshold_twoIndex
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (nRows : WithBot Nat)) (hr : r ≤ nRows)
    (center : QuestionCenter I (blocks A (hBlock L nRows))
      (leafT nRows (hBlock L nRows)))
    (ht : leafT nRows (hBlock L nRows) ≤ 2 * hBlock L nRows)
    (hh : hBlock L nRows ≤ blocks A (hBlock L nRows))
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin r → DomainDraw center (hBlock L nRows))]
    (witness : Fin r → DomainDraw center (hBlock L nRows)) :
    eventMass
        (uniformDomainTupleLaw center (hBlock L nRows) r witness)
        (domainDrawRankFailureEventTwoIndex center ht hh) <
      1 / (2 : ℚ) ^ (badExponent nRows (hBlock L nRows) + 1) := by
  classical
  let h := hBlock L nRows
  let J := blocks A h
  let t := leafT nRows h
  have hs := selector_spec hsel
  have hnRows : 256 ≤ nRows := hs.1.1
  have hcut : nRows + 2 ≤ h := by
    exact (Nat.le_max_right (sourceHMin nRows) (nRows + 2)).trans
      hs.1.2.2.2.2.2.2.2.1
  have hdiv : bOf nRows ∣ h := hs.1.2.2.2.2.2.1
  have hqpos : 0 < h / bOf nRows := by
    by_contra hq
    have hz : h / bOf nRows = 0 := Nat.eq_zero_of_not_pos hq
    have hmod : h % bOf nRows = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hdecomp := Nat.mod_add_div h (bOf nRows)
    rw [hmod, hz] at hdecomp
    simp at hdecomp
    omega
  have hk : 1 ≤ leafK nRows h := by
    dsimp [leafK, leafT]
    have hqle : h / bOf nRows ≤ h := Nat.div_le_self h (bOf nRows)
    have hsub : h - h / bOf nRows + h / bOf nRows = h :=
      Nat.sub_add_cancel hqle
    omega
  have hguard := selected_actual_center_quotient_dimension_guard_twoIndex
    (center := center) sourceHMin hA hsel hr
  have htd : J + t ≤ J + 2*h := by
    simpa [J, t, h] using Nat.add_le_add_left ht
      (blocks A (hBlock L nRows))
  let drawsToLeaves := domainDrawTupleExtensionEquiv center h r ht hh
  let extWitness := drawsToLeaves witness
  let badExt := fixedCenterBadEvent
    (V := questionCoordinateSpace center) (d := J + 2*h) (m := r)
      (coordinateCenterGrass center)
  let badDomain := preimageEvent drawsToLeaves badExt
  let rankBad : Finset (Fin r → DomainDraw center h) :=
    domainDrawRankFailureEventTwoIndex (r := r) center ht hh
  have hevents : rankBad = badDomain := by
    ext draws
    simp only [rankBad, badDomain, domainDrawRankFailureEventTwoIndex,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact (fixedCenterBad_preimage_iff_domainDraw_rankFailure_arity
      center h ht hh draws).symm
  letI : Fintype (CenterQuotient center) := Fintype.ofFinite _
  have hdim : (J + 2*h) - (J + t) = 2*h - t := by omega
  have hkdim : (J + 2*h) - (J + t) = leafK nRows (hBlock L nRows) := by
    calc
      (J + 2*h) - (J + t) = 2*h - t := hdim
      _ = leafK nRows (hBlock L nRows) := by
        simp [h, t, leafK, leafT]
  have hguard' :
      r * ((J + 2*h) - (J + t)) + badExponent nRows h + 2 ≤
        Module.finrank (ZMod 2) (CenterQuotient center) := by
    rw [hkdim]
    simpa [h] using hguard
  change r * ((J + 2*h) - (J + t)) + badExponent nRows h + 2 ≤
    Module.finrank (ZMod 2)
      (questionCoordinateSpace center ⧸ (coordinateCenterGrass center).val) at hguard'
  have hk' : 1 ≤ (J + 2*h) - (J + t) := by
    rw [hkdim]
    simpa [h] using hk
  have hdV : J + 2*h ≤ Module.finrank (ZMod 2)
      (questionCoordinateSpace center) := by
    rw [coordinateSpace_finrank center]
    have hh' : h ≤ J := by simpa [h, J] using hh
    change J + 2*h ≤ 3*J
    nlinarith [hh']
  have hscalar := fixedCenter_badEvent_mass_lt_threshold
    (V := questionCoordinateSpace center)
    (t := J + t) (d := J + 2*h) (m := r)
    (E := badExponent nRows h)
    htd hdV hk' (coordinateCenterGrass center) extWitness hguard'
  have htransport := extensionTuple_eventMass_eq_preimage
    center h r ht hh witness badExt
  have hmasses :
      eventMass (uniformDomainTupleLaw center h r witness) rankBad =
      eventMass
        (extensionTupleLaw (coordinateCenterGrass center) extWitness) badExt := by
    rw [hevents, ← htransport]
  change eventMass (uniformDomainTupleLaw center h r witness) rankBad < _
  rw [hmasses]
  simpa [h, J, t, extWitness, drawsToLeaves, badExt,
    coordinateCenterGrass] using hscalar

end
end PvNP.RealizableHardness.ActualStarSameLawTwoIndexComposition
