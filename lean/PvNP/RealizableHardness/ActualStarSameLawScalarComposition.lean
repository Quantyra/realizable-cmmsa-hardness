import PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
import PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
import PvNP.RealizableHardness.SamplerParameters

/-! Composition of the accepted fixed-center scalar estimate with the
actual ordered `DomainDraw` carrier law.  The result remains conditional on
the selected source cutoff and describes only the defined uniform domain-draw
law; it is not the manuscript physical sampler or a center average. -/

namespace PvNP.RealizableHardness.ActualStarSameLawScalarComposition

open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualStarFixedCenterScalarClosure
open PvNP.RealizableHardness.ActualStarFixedCenterFirstMoment
open PvNP.RealizableHardness.ActualStarExtensionProduct
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualStarCoordinateExtensionLawBridge
open PvNP.RealizableHardness.ActualStarDomainDrawEventBridge
open PvNP.RealizableHardness.SamplerParameters

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m L A : Nat}
variable {I : ActualOccurrenceAllocation.Instance N m}

/-- The full ordered-family rank-defect event on the actual domain-draw
carrier.  Its rank is measured in `CenterQuotient`, whose quotient is taken
once, at the fixed center. -/
def domainDrawRankFailureEvent
    (center : QuestionCenter I (blocks A (hBlock L m))
      (leafT m (hBlock L m)))
    (ht : leafT m (hBlock L m) ≤ 2 * hBlock L m)
    (hh : hBlock L m ≤ blocks A (hBlock L m)) :
    Finset (Fin m → DomainDraw center (hBlock L m)) :=
  Finset.univ.filter fun draws =>
    Module.finrank (ZMod 2)
      (domainDrawJointImage center (hBlock L m)
        ht hh draws) ≠
      m * leafK m (hBlock L m)

/-- Same fixed-center bad mass bound after transporting to the actual
ordered domain-draw tuple law and expressing failure in its quotient carrier.
All selector assumptions, including the source cutoff parameter, remain
explicit. -/
theorem selected_domainDraw_rankFailure_mass_lt_threshold
    (sourceHMin : Nat → Nat) (hA : 1 ≤ A)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L =
      (m : WithBot Nat))
    (center : QuestionCenter I (blocks A (hBlock L m))
      (leafT m (hBlock L m)))
    (ht : leafT m (hBlock L m) ≤ 2 * hBlock L m)
    (hh : hBlock L m ≤ blocks A (hBlock L m))
    [Finite (questionCoordinateSpace center)]
    [Fintype (Fin m → DomainDraw center (hBlock L m))]
    (witness : Fin m → DomainDraw center (hBlock L m)) :
    eventMass (uniformDomainTupleLaw center (hBlock L m) m witness)
      (domainDrawRankFailureEvent center ht hh) <
      1 / (2 : ℚ) ^ (badExponent m (hBlock L m) + 1) := by
  classical
  let h := hBlock L m
  let J := blocks A h
  let t := leafT m h
  have hs := selector_spec hsel
  have hm : 256 ≤ m := hs.1.1
  have hcut : m + 2 ≤ h := by
    exact (Nat.le_max_right (sourceHMin m) (m + 2)).trans
      hs.1.2.2.2.2.2.2.2.1
  have hhpos : 0 < h := by omega
  have hdiv : bOf m ∣ h := hs.1.2.2.2.2.2.1
  have hqpos : 0 < h / bOf m := by
    by_contra hq
    have hz : h / bOf m = 0 := Nat.eq_zero_of_not_pos hq
    have hmod : h % bOf m = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hdecomp := Nat.mod_add_div h (bOf m)
    rw [hmod, hz] at hdecomp
    simp at hdecomp
    omega
  have hk : 1 ≤ leafK m h := by
    dsimp [leafK, leafT]
    have hqle : h / bOf m ≤ h := Nat.div_le_self h (bOf m)
    have hsub : h - h / bOf m + h / bOf m = h := Nat.sub_add_cancel hqle
    omega
  have hguard := selected_actual_center_quotient_dimension_guard
    (center := center) sourceHMin hA hsel
  have htd : J + t ≤ J + 2*h := by
    simpa [J, t, h] using Nat.add_le_add_left ht (blocks A (hBlock L m))
  let drawsToLeaves := domainDrawTupleExtensionEquiv center h m ht hh
  let extWitness := drawsToLeaves witness
  let badExt := fixedCenterBadEvent
    (V := questionCoordinateSpace center) (d := J + 2*h) (m := m)
      (coordinateCenterGrass center)
  let badDomain := preimageEvent drawsToLeaves badExt
  let rankBad := domainDrawRankFailureEvent center ht hh
  have hevents : rankBad = badDomain := by
    ext draws
    simp only [rankBad, badDomain, domainDrawRankFailureEvent,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact (fixedCenterBad_preimage_iff_domainDraw_rankFailure
      center h ht hh draws).symm
  letI : Fintype (CenterQuotient center) := Fintype.ofFinite _
  have hdim : (J + 2*h) - (J + t) = 2*h - t := by omega
  have hkdim : (J + 2*h) - (J + t) = leafK m (hBlock L m) := by
    calc
      (J + 2*h) - (J + t) = 2*h - t := hdim
      _ = leafK m (hBlock L m) := by simp [h, t, leafK, leafT]
  have hguard' :
      m * ((J + 2*h) - (J + t)) + badExponent m h + 2 ≤
        Module.finrank (ZMod 2) (CenterQuotient center) := by
    rw [hkdim]
    simpa only [h] using hguard
  change m * ((J + 2*h) - (J + t)) + badExponent m h + 2 ≤
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
    (t := J + t) (d := J + 2*h) (m := m)
    (E := badExponent m h)
    htd
    hdV hk' (coordinateCenterGrass center) extWitness hguard'
  have htransport := extensionTuple_eventMass_eq_preimage
    center h m ht hh witness badExt
  have hmasses :
      eventMass (uniformDomainTupleLaw center h m witness) rankBad =
      eventMass (extensionTupleLaw (coordinateCenterGrass center) extWitness) badExt := by
    rw [hevents, ← htransport]
  change eventMass (uniformDomainTupleLaw center h m witness) rankBad < _
  rw [hmasses]
  simpa [h, J, t, extWitness, drawsToLeaves, badExt,
    coordinateCenterGrass] using hscalar

end
end PvNP.RealizableHardness.ActualStarSameLawScalarComposition
