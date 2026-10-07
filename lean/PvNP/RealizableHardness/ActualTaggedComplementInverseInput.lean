import PvNP.RealizableHardness.ActualTaggedComplementHighDensityInput
import PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection

namespace PvNP.RealizableHardness.ActualTaggedComplementInverseInput

open PvNP.RealizableHardness
open ActualTaggedComplementHighDensityInput
open ActualTaggedComplementIncidence
open ActualTaggedMZSideDraw
open ActualTaggedComplementStarDensityBridge
open ActualTaggedComplementStarDensityBound
open ActualTaggedConcreteStarLaw
open ActualTaggedFixedTableAcceptance
open ActualTaggedFixedCenterGeometry
open ActualStarSpanIntersection
open ActualBinaryGrassmannIncidence
open ActualSourceStarLaw
open ActualChangedAmbient8SBoundary
open ActualOrdinaryStarWeightedSelection
open ActualOrdinaryStarMatchingFiber
open ActualOrdinaryStarSelection
open ActualStarAcceptedGoodMass
open GrassmannCounting
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

/-- A star-density threshold q/2 yields q/4 matching mass on accepted,
jointly-direct tuples when the rank-failure budget is at most q/4. -/
theorem ordinary_good_mass_ge_of_density_threshold
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {t d k E : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hk : 1 ≤ d - t)
    (hguard : k * (d - t) + E + 2 ≤ Module.finrank (ZMod 2) V - t)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (q : Rat) (hqpos : 0 < q)
    (hmargin : successMargin E ≤ q / 2)
    (hdensity : q / 2 ≤ StarDensity (k := k) hcenter hleaf C T) :
    q / 4 ≤ goodStarMass (V := V) htd hdV k C T := by
  classical
  let mu := starLaw (V := V) (t := t) (d := d) (m := k) htd hdV
  have hbad := starLaw_bad_mass_lt_threshold (V := V) htd hdV hk hguard
  rw [← successMargin_half] at hbad
  have hgood0 := eventMass_accept_rankGood_ge mu (accepts C T) jointlyDirect
  have hset : (Finset.univ.filter fun z : StarTuple (V := V) t d k =>
      accepts C T z ∧ jointlyDirect z) =
      Finset.univ.filter (goodStar C T) := by
    ext z
    simp [goodStar]
  rw [hset] at hgood0
  have hgood : goodStarMass (V := V) htd hdV k C T ≥
      acceptanceMass (V := V) htd hdV k C T -
        eventMass mu (Finset.univ.filter fun z => ¬ jointlyDirect z) := by
    simpa only [mu, goodStarMass, acceptanceMass] using hgood0
  rw [← starDensity_eq_acceptanceMass htd hdV hcenter hleaf C T] at hgood
  have hbadq : eventMass mu (Finset.univ.filter fun z => ¬ jointlyDirect z) < q / 4 := by
    have hle : successMargin E / 2 ≤ q / 4 := by
      linarith
    exact hbad.trans_le hle
  linarith

/-- The two finite-count ratios simplify using the actual complement dimension
and the exponent guard. -/
theorem complement_weight_ratios
    {t h k E : Nat} (A : SideComplement I copies U)
    (hh : h ≤ J)
    (hguard : k * (2 * h - t) + E + 2 ≤ 2 * J - t) :
    (2 : Rat) ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) /
        (2 : Rat) ^ (Module.finrank (ZMod 2) A.1 - t) =
          1 / (2 : Rat) ^ (k * (2 * h - t)) ∧
    (2 : Rat) ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) /
        (2 : Rat) ^ Module.finrank (ZMod 2) A.1 =
          1 / (2 : Rat) ^ (t + k * (2 * h - t)) := by
  have hn : Module.finrank (ZMod 2) A.1 = 2 * J := sideComplement_finrank I copies U A
  have hta : t + k * (2 * h - t) ≤ Module.finrank (ZMod 2) A.1 := by
    rw [hn]
    omega
  have hsub₁ : Module.finrank (ZMod 2) A.1 - t =
      (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) +
        k * (2 * h - t) := by omega
  have hsub₂ : Module.finrank (ZMod 2) A.1 =
      (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) +
        (t + k * (2 * h - t)) := by omega
  have hpowB : (2 : Rat) ^ (Module.finrank (ZMod 2) A.1 - t) =
      (2 : Rat) ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) *
        (2 : Rat) ^ (k * (2 * h - t)) := by rw [hsub₁, pow_add]
  have hpowF : (2 : Rat) ^ Module.finrank (ZMod 2) A.1 =
      (2 : Rat) ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) *
        (2 : Rat) ^ (t + k * (2 * h - t)) := by rw [hsub₂, pow_add]
  have hnum : (2 : Rat) ^
      (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t))) ≠ 0 := by positivity
  have ha : (2 : Rat) ^ (k * (2 * h - t)) ≠ 0 := by positivity
  have htaPow : (2 : Rat) ^ (t + k * (2 * h - t)) ≠ 0 := by positivity
  constructor
  · rw [hpowB]
    field_simp [hnum, ha]
  · rw [hpowF]
    field_simp [hnum, htaPow]


/-- Every complement above q/2 supplies a same-table functional with q/8
weighted mass, provided the rank-failure budget is at most q/4. -/
theorem good_complement_selects_q_weighted_functional
    {t h k E : Nat} (A : SideComplement I copies U)
    (ht : t ≤ 2 * h) (hh : h ≤ J) (hk : 1 ≤ 2 * h - t)
    (hguard : k * (2 * h - t) + E + 2 ≤ 2 * J - t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) (hqpos : 0 < q)
    (hmargin : successMargin E ≤ q / 2)
    (hA : q / 2 ≤ complementStarDensity (k := k) I copies U A ht hh C T') :
    ∃ f : Module.Dual (ZMod 2) A.1,
      let Cₐ := transportedCenterTable I copies U A C
      let Tₐ := transportedLeafTable I copies U A T'
      let X := matchingStarMass (m := k) ht
        (by
          calc
            2 * h ≤ 2 * J := by omega
            _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm) Cₐ Tₐ f
      let β := matchingCenterMass (m := k) ht
        (by
          calc
            2 * h ≤ 2 * J := by omega
            _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm) Cₐ f
      let M : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t)))
      let B : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - t)
      let F : Rat := 2 ^ Module.finrank (ZMod 2) A.1
      (q / 8) * (1 / (2 : Rat) ^ (k * (2 * h - t))) * β +
        (q / 8) * (1 / (2 : Rat) ^ (t + k * (2 * h - t))) ≤ X ∧ X ≤ β := by
  have hdV : 2 * h ≤ Module.finrank (ZMod 2) A.1 := by
    calc
      2 * h ≤ 2 * J := by omega
      _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm
  have htA : t ≤ Module.finrank (ZMod 2) A.1 := by
    calc
      t ≤ 2 * h := ht
      _ ≤ 2 * J := by omega
      _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm
  have hcenter : Nonempty (Grass A.1 t) := grass_nonempty_of_le htA
  have hleaf : ∀ K : Grass A.1 t, Nonempty (LeafOver K (2 * h)) :=
    fun K => extension_nonempty K ht hdV
  have hden : q / 2 ≤ StarDensity (V := A.1) (k := k) hcenter hleaf
      (transportedCenterTable I copies U A C) (transportedLeafTable I copies U A T') := by
    change q / 2 ≤ StarDensity (V := A.1) (k := k) hcenter hleaf
      (transportedCenterTable I copies U A C) (transportedLeafTable I copies U A T') at hA
    exact hA
  have hgood := ordinary_good_mass_ge_of_density_threshold
    (V := A.1) (k := k) ht hdV hk
    (by
      rw [sideComplement_finrank I copies U A]
      exact hguard)
    hcenter hleaf (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T') q hqpos hmargin hden
  have hqnonneg : 0 ≤ q / 2 := by positivity
  have hweighted := exists_weighted_matching_functional
    (V := A.1) (t := t) (d := 2 * h) (m := k) ht hdV hcenter hleaf
    (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T') (q / 2) hqnonneg
    (by linarith)
  rcases hweighted with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  have hcoef : (q / 2) / 4 = q / 8 := by ring
  have hratio := complement_weight_ratios (I := I) (copies := copies)
    (U := U) A hh hguard
  rw [← hratio.1, ← hratio.2]
  simpa only [matchingStarMass, matchingCenterMass, hcoef] using hf

/-- The actual fixed-U density yields positive complement mass, and every
complement in that mass class has a same-table q/8 weighted functional.
The rank-margin comparison remains an explicit hypothesis for the next force
step to discharge. -/
theorem actual_density_positive_mass_with_q_functionals
    {t h k E : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hk : 1 ≤ 2 * h - t)
    (hguard : k * (2 * h - t) + E + 2 ≤ 2 * J - t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) (hqpos : 0 < q)
    (hq : q ≤ sideConditionalDensity I copies U t h k C T')
    (hmargin : successMargin E ≤ q / 2) :
    q / 2 ≤ goodComplementMass (k := k) I copies U ht hh C T' q ∧
    ∀ A : SideComplement I copies U,
      q / 2 ≤ complementStarDensity (k := k) I copies U A ht hh C T' →
      ∃ f : Module.Dual (ZMod 2) A.1,
        let Cₐ := transportedCenterTable I copies U A C
        let Tₐ := transportedLeafTable I copies U A T'
        let X := matchingStarMass (m := k) ht
          (by
            calc
              2 * h ≤ 2 * J := by omega
              _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm) Cₐ Tₐ f
        let β := matchingCenterMass (m := k) ht
          (by
            calc
              2 * h ≤ 2 * J := by omega
              _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm) Cₐ f
        let M : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t)))
        let B : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - t)
        let F : Rat := 2 ^ Module.finrank (ZMod 2) A.1
        (q / 8) * (1 / (2 : Rat) ^ (k * (2 * h - t))) * β +
          (q / 8) * (1 / (2 : Rat) ^ (t + k * (2 * h - t))) ≤ X ∧ X ≤ β := by
  constructor
  · exact half_threshold_good_complement_mass_ge (k := k) I copies U
      ht hh C T' q hqpos hq
  · intro A hA
    exact good_complement_selects_q_weighted_functional
      (I := I) (copies := copies) (U := U) A ht hh hk hguard C T' q
      hqpos hmargin hA
/-- A selected complement passes the actual density bound into the existing
weighted ordinary-star functional argument. All tables are transported from
the original fixed predraw pair. -/
theorem exists_actual_complement_weighted_functional
    {t h k E : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hk : 1 ≤ 2 * h - t)
    (hguard : k * (2 * h - t) + E + 2 ≤ 2 * J - t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (hscore : successMargin E ≤ sideConditionalDensity I copies U t h k C T') :
    ∃ (A : SideComplement I copies U) (f : Module.Dual (ZMod 2) A.1),
      let Cₐ := transportedCenterTable I copies U A C
      let Tₐ := transportedLeafTable I copies U A T'
      let X := matchingStarMass (m := k) ht
        (by
          calc
            2 * h ≤ 2 * J := by omega
            _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm) Cₐ Tₐ f
      let β := matchingCenterMass (m := k) ht
        (by
          calc
            2 * h ≤ 2 * J := by omega
            _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm) Cₐ f
      let M : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t)))
      let B : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - t)
      let F : Rat := 2 ^ Module.finrank (ZMod 2) A.1
      (successMargin E / 4) * (M / B) * β +
        (successMargin E / 4) * (M / F) ≤ X ∧ X ≤ β := by
  have hqpos : 0 < successMargin E := by
    unfold successMargin
    positivity
  obtain ⟨A, hA⟩ := exists_complement_StarDensity_ge_of_le_sideConditionalDensity
    I copies U ht hh C T' (successMargin E) hqpos hscore
  have hdV : 2 * h ≤ Module.finrank (ZMod 2) A.1 := by
    calc
      2 * h ≤ 2 * J := by omega
      _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm
  have htA : t ≤ Module.finrank (ZMod 2) A.1 := by
    calc
      t ≤ 2 * h := ht
      _ ≤ 2 * J := by omega
      _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm
  have hcenter : Nonempty (Grass A.1 t) := grass_nonempty_of_le htA
  have hleaf : ∀ K : Grass A.1 t, Nonempty (LeafOver K (2 * h)) :=
    fun K => extension_nonempty K ht hdV
  have hweighted := ordinary_star_selects_weighted_functional
    (V := A.1) (t := t) (d := 2 * h) (m := k) (E := E)
    ht hdV hk (by
      rw [sideComplement_finrank I copies U A]
      exact hguard)
    hcenter hleaf (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T') hA
  rcases hweighted with ⟨f, hf⟩
  refine ⟨A, f, ?_⟩
  simpa only [matchingStarMass, matchingCenterMass] using hf

end
end PvNP.RealizableHardness.ActualTaggedComplementInverseInput
