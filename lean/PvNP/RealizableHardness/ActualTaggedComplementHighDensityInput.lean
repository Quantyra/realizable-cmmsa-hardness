import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBound
import PvNP.RealizableHardness.ActualOrdinaryStarSelection
import PvNP.RealizableHardness.ActualFiniteUniformThreshold

/-! A concrete ordinary-star input selected from the actual fixed-U
complement experiment. This module stops before the all-ambient inverse. -/
namespace PvNP.RealizableHardness.ActualTaggedComplementHighDensityInput

open PvNP.RealizableHardness
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
open GrassmannCounting
open ActualChangedAmbient8SBoundary
open ActualOrdinaryStarSelection
open ActualStarAcceptedGoodMass
open ActualFiniteLaw
open ActualSourceStarLaw
open ActualFiniteUniformThreshold
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

private theorem sideComplement_nonempty : Nonempty (SideComplement I copies U) := by
  classical
  let E := coordinateSpace (taggedSource I copies).support U.1
  let H := (equationSpan (taggedSource I copies).support U.1).comap E.subtype
  obtain ⟨A, hA⟩ := Submodule.exists_isCompl H
  exact ⟨⟨A, hA⟩⟩

/-- The changed-ambient star density on one actual complement, using the
transport of the original fixed predraw tables. -/
def complementStarDensity {t h k : Nat} (A : SideComplement I copies U)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : Rat :=
  StarDensity (V := A.1) (k := k)
    (grass_nonempty_of_le (by
      calc
        t ≤ 2 * h := ht
        _ ≤ 2 * J := by omega
        _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
    (fun K => extension_nonempty K ht (by
      calc
        2 * h ≤ 2 * J := by omega
        _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
    (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T')

/-- Every ordinary star density is a probability of an acceptance event. -/
theorem starDensity_le_one {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {t d k : Nat}
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d) :
    StarDensity (k := k) hcenter hleaf C T ≤ 1 := by
  rw [starDensity_eq_acceptanceMass htd hdV hcenter hleaf C T]
  unfold acceptanceMass
  exact le_trans
    (eventMass_mono _ (Finset.subset_univ _))
    (by rw [eventMass_univ])

/-- The actual transported complement star is a normalized probability. -/
theorem complementStarDensity_le_one {t h k : Nat}
    (A : SideComplement I copies U) (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    complementStarDensity (k := k) I copies U A ht hh C T' ≤ 1 := by
  exact starDensity_le_one (k := k) ht
    (by
      calc
        2 * h ≤ 2 * J := by omega
        _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm)
    (grass_nonempty_of_le (by
      calc
        t ≤ 2 * h := ht
        _ ≤ 2 * J := by omega
        _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
    (fun K => extension_nonempty K ht (by
      calc
        2 * h ≤ 2 * J := by omega
        _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
    (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T')

/-- Any positive threshold below the actual conditional density is attained
by one of its actual complements, with the same predraw tables. -/
theorem exists_complement_StarDensity_ge_of_le_sideConditionalDensity
    {t h k : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) (hqpos : 0 < q)
    (hq : q ≤ sideConditionalDensity I copies U t h k C T') :
    ∃ A : SideComplement I copies U,
      q ≤ complementStarDensity (k := k) I copies U A ht hh C T' := by
  classical
  letI : Nonempty (SideComplement I copies U) := sideComplement_nonempty I copies U
  let D : SideComplement I copies U → Rat := fun A =>
    complementStarDensity (k := k) I copies U A ht hh C T'
  let c : Nat := Fintype.card (SideComplement I copies U)
  have hcpos : 0 < c := by
    dsimp [c]
    exact Fintype.card_pos_iff.mpr (sideComplement_nonempty I copies U)
  have hcne : (c : Rat) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hcpos.ne'
  have havg := sideConditionalDensity_le_uniformComplement_average_StarDensity
    (k := k) I copies U ht hh C T'
  have havgD : sideConditionalDensity I copies U t h k C T' ≤
      ∑ A : SideComplement I copies U, (1 / Fintype.card (SideComplement I copies U) : Rat) * D A := by
    change sideConditionalDensity I copies U t h k C T' ≤
      ∑ A : SideComplement I copies U,
        (1 / Fintype.card (SideComplement I copies U) : Rat) *
          StarDensity (V := A.1) (k := k)
            (grass_nonempty_of_le (by
              calc
                t ≤ 2 * h := ht
                _ ≤ 2 * J := by omega
                _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
            (fun K => extension_nonempty K ht (by
              calc
                2 * h ≤ 2 * J := by omega
                _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
            (transportedCenterTable I copies U A C)
            (transportedLeafTable I copies U A T')
    exact havg
  have hqavg : q ≤ ∑ A : SideComplement I copies U, (1 / (c : Rat)) * D A := by
    simpa [c] using le_trans hq havgD
  have hscale := mul_le_mul_of_nonneg_left hqavg (Nat.cast_nonneg c)
  have hnormalize : (c : Rat) *
      (∑ A : SideComplement I copies U, (1 / (c : Rat)) * D A) =
        ∑ A : SideComplement I copies U, D A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    field_simp [hcne]
  rw [hnormalize] at hscale
  have hsumq : (∑ _A : SideComplement I copies U, q) = (c : Rat) * q := by
    simp [c, Finset.sum_const, nsmul_eq_mul]
  have hsumle : (∑ _A : SideComplement I copies U, q) ≤
      ∑ A : SideComplement I copies U, D A := by
    rw [hsumq]
    exact hscale
  obtain ⟨A, _hAmem, hA⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _ : SideComplement I copies U => q)
    (g := D) Finset.univ_nonempty hsumle
  simpa only [D] using (show ∃ A : SideComplement I copies U, q ≤ D A from ⟨A, hA⟩)

/-- Uniform mass of complements whose same-table ordinary star density clears
the indicated threshold. -/
def goodComplementMass {t h k : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) (q : Rat) : Rat :=
  uniformGoodMass (fun A => complementStarDensity (k := k) I copies U A ht hh C T') q

/-- The actual fixed-U density bound forces a positive uniform fraction of
complements to have ordinary star density at least half the threshold. -/
theorem half_threshold_good_complement_mass_ge
    {t h k : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) (hqpos : 0 < q)
    (hq : q ≤ sideConditionalDensity I copies U t h k C T') :
    q / 2 ≤ goodComplementMass (k := k) I copies U ht hh C T' q := by
  classical
  letI : Nonempty (SideComplement I copies U) := sideComplement_nonempty I copies U
  let D : SideComplement I copies U → Rat := fun A =>
    complementStarDensity (k := k) I copies U A ht hh C T'
  have havg := sideConditionalDensity_le_uniformComplement_average_StarDensity
    (k := k) I copies U ht hh C T'
  have hmeanEq : ActualFiniteUniformThreshold.uniformMean D =
      ∑ A : SideComplement I copies U,
        (1 / Fintype.card (SideComplement I copies U) : Rat) * D A := by
    unfold ActualFiniteUniformThreshold.uniformMean
    calc
      (∑ A : SideComplement I copies U, D A) / Fintype.card (SideComplement I copies U) =
          (∑ A : SideComplement I copies U, D A) *
            (1 / Fintype.card (SideComplement I copies U) : Rat) := by ring
      _ = ∑ A : SideComplement I copies U,
          D A * (1 / Fintype.card (SideComplement I copies U) : Rat) := by
        rw [Finset.sum_mul]
      _ = ∑ A : SideComplement I copies U,
          (1 / Fintype.card (SideComplement I copies U) : Rat) * D A := by
        apply Finset.sum_congr rfl
        intro A _
        ring
  have havgAlias : sideConditionalDensity I copies U t h k C T' ≤
      ∑ A : SideComplement I copies U,
        (1 / Fintype.card (SideComplement I copies U) : Rat) *
          complementStarDensity (k := k) I copies U A ht hh C T' := by
    change sideConditionalDensity I copies U t h k C T' ≤
      ∑ A : SideComplement I copies U,
        (1 / Fintype.card (SideComplement I copies U) : Rat) *
          StarDensity (V := A.1) (k := k)
            (grass_nonempty_of_le (by
              calc
                t ≤ 2 * h := ht
                _ ≤ 2 * J := by omega
                _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
            (fun K => extension_nonempty K ht (by
              calc
                2 * h ≤ 2 * J := by omega
                _ = Module.finrank (ZMod 2) A.1 := (sideComplement_finrank I copies U A).symm))
            (transportedCenterTable I copies U A C)
            (transportedLeafTable I copies U A T')
    exact havg
  have hqmean : q ≤ ActualFiniteUniformThreshold.uniformMean D := by
    rw [hmeanEq]
    exact le_trans hq havgAlias
  have hDle : ∀ A : SideComplement I copies U, D A ≤ 1 := by
    intro A
    exact complementStarDensity_le_one (k := k) I copies U A ht hh C T'
  change q / 2 ≤ ActualFiniteUniformThreshold.uniformGoodMass D q
  exact ActualFiniteUniformThreshold.half_threshold_good_mass_ge D q hqpos hDle hqmean

end
end PvNP.RealizableHardness.ActualTaggedComplementHighDensityInput
