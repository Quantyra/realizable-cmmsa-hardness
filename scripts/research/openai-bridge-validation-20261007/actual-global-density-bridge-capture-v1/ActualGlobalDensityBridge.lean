import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualTaggedComplementIncidence
import PvNP.RealizableHardness.ActualTaggedMZSideDraw
import PvNP.RealizableHardness.ActualOrdinaryStarSelection
import PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
import PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualFiniteLaw

/-! A fixed-table, unconditioned finite-averaging bridge from the actual
side density to one ordinary complement star. -/

namespace PvNP.RealizableHardness.ActualGlobalDensityBridge

open scoped BigOperators
open PvNP.RealizableHardness
open ActualTaggedComplementIncidence
open ActualTaggedComplementStarDensityBridge
open ActualChangedAmbient8SBoundary
open ActualOrdinaryStarSelection
open ActualFiniteLaw
open ActualSourceStarLaw
open ActualBinaryGrassmannIncidence

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
  (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

/-- The ordinary star density on one fixed complement, using the same
globally predrawn tables and their deterministic restrictions. -/
def transportedStarDensity {t h k : Nat}
    (A : SideComplement I copies U) (ht : t <= 2 * h) (hh : h <= J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : Rat := by
  let hd : 2 * h <= Module.finrank (ZMod 2) A.1 := by
    rw [sideComplement_finrank I copies U A]
    omega
  let hcenter : Nonempty (Grass A.1 t) :=
    ActualBinaryGrassmannIncidence.grass_nonempty_of_le (le_trans ht hd)
  let hleaf : forall K : Grass A.1 t, Nonempty (LeafOver K (2 * h)) :=
    fun K => ActualSourceStarLaw.extension_nonempty K ht hd
  exact StarDensity (k := k) hcenter hleaf
    (transportedCenterTable I copies U A C)
    (transportedLeafTable I copies U A T')

/-- The actual acceptance mass inside one complement before the outer
uniform-complement factor. -/
def complementFullAcceptMass {t h k : Nat}
    (A : SideComplement I copies U) (C : TaggedCenterTable I copies)
    (T' : TaggedLeafTable I copies) : Rat :=
  sum Kc : CenterInComplement I copies U A t,
    sum Ls : Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
      (((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
        ((1 : Rat) / Fintype.card
          (Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h))) *
        (if fullAccepts I copies U Kc.1 C T'
          (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))
          then 1 else 0)

/-- Reindex the ordinary star carrier by the actual center and leaf carriers.
The event here is ordinary `StarAccepts`, while the weights are exactly the
uniform laws on the reindexed carriers. -/
private theorem transportedStarDensity_reindexed {t h k : Nat}
    (A : SideComplement I copies U) (ht : t <= 2 * h) (hh : h <= J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    transportedStarDensity I copies U A ht hh C T' =
      sum Kc : CenterInComplement I copies U A t,
        sum Ls : Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
          (((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
            ((1 : Rat) / Fintype.card
              (Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h))) *
            (if StarAccepts (transportedCenterTable I copies U A C)
                (transportedLeafTable I copies U A T')
                (sideCenterToOrdinary I copies U A Kc)
                (fun i => ordinaryToStarLeaf I copies U A Kc (Ls i))
              then 1 else 0) := by
  classical
  let hd : 2 * h <= Module.finrank (ZMod 2) A.1 := by
    rw [sideComplement_finrank I copies U A]
    omega
  let hcenter : Nonempty (Grass A.1 t) :=
    ActualBinaryGrassmannIncidence.grass_nonempty_of_le (le_trans ht hd)
  let hleaf : forall K : Grass A.1 t, Nonempty (LeafOver K (2 * h)) :=
    fun K => ActualSourceStarLaw.extension_nonempty K ht hd
  symm
  unfold transportedStarDensity
  dsimp only
  unfold StarDensity
  apply Fintype.sum_equiv (centerInComplementEquiv I copies U A t).symm
  intro Kc
  let e : (Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h) ≃
      (Fin k -> LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h)) :=
    Equiv.arrowCongr (Equiv.refl (Fin k))
      (ordinaryStarLeafEquiv I copies U A Kc)
  have hcenterCard : Fintype.card (Grass A.1 t) =
      Fintype.card (CenterInComplement I copies U A t) :=
    Fintype.card_congr (centerInComplementEquiv I copies U A t)
  have hleafCard : Fintype.card
      (Fin k -> LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h)) =
      Fintype.card (Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h) :=
    Fintype.card_congr e.symm
  apply Fintype.sum_equiv e
  intro Ls
  simp only [uniformLaw_apply, hcenterCard, hleafCard]

/-- In a fixed complement the actual full-domain event is contained in the
ordinary star event. Carrier changes preserve the same event's uniform mass;
only the pointwise predicate is enlarged. -/
theorem complementFullAcceptMass_le_transportedStarDensity {t h k : Nat}
    (A : SideComplement I copies U) (ht : t <= 2 * h) (hh : h <= J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    complementFullAcceptMass I copies U A C T' <=
      transportedStarDensity I copies U A ht hh C T' := by
  classical
  rw [transportedStarDensity_reindexed I copies U A ht hh C T']
  unfold complementFullAcceptMass
  apply Finset.sum_le_sum
  intro Kc _
  apply Finset.sum_le_sum
  intro Ls _
  have himp :
      fullAccepts I copies U Kc.1 C T'
          (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i)) ->
        StarAccepts (transportedCenterTable I copies U A C)
          (transportedLeafTable I copies U A T')
          (sideCenterToOrdinary I copies U A Kc)
          (fun i => ordinaryToStarLeaf I copies U A Kc (Ls i)) := by
    intro hactual
    exact actual_implies_ordinary_star_accepts
      I copies U A Kc Ls C T' hactual
  have hweight : 0 <=
      ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
        ((1 : Rat) / Fintype.card
          (Fin k -> OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) := by
    positivity
  by_cases hfull : fullAccepts I copies U Kc.1 C T'
      (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))
  · have hstar := himp hfull
    simp [hfull, hstar]
  · by_cases hstar : StarAccepts (transportedCenterTable I copies U A C)
        (transportedLeafTable I copies U A T')
        (sideCenterToOrdinary I copies U A Kc)
        (fun i => ordinaryToStarLeaf I copies U A Kc (Ls i))
    · simp [hfull, hstar, hweight]
    · simp [hfull, hstar]

/-- Expand the global A-first actual density as a normalized average of the
per-complement full-acceptance masses. -/
private theorem ordinaryComplementStarDensity_eq_average_fullMass {t h k : Nat}
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    ordinaryComplementStarDensity I copies U t h k C T' =
      ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
        sum A : SideComplement I copies U,
          complementFullAcceptMass I copies U A C T' := by
  classical
  unfold ordinaryComplementStarDensity complementFullAcceptMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro Kc _
  apply Finset.sum_congr rfl
  intro Ls _
  ring

/-- If the actual, unconditioned global side density is at least a rational
threshold, one fixed complement has at least that ordinary star density.
The globally predrawn tables and source instance are unchanged. -/
theorem exists_complement_with_star_density_ge {t h k : Nat}
    (ht : t <= 2 * h) (hh : h <= J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (e : Rat)
    (hscore : e <= sideConditionalDensity I copies U t h k C T') :
    exists A : SideComplement I copies U,
      e <= transportedStarDensity I copies U A ht hh C T' := by
  classical
  have htJ : t <= 2 * J := by omega
  have hsideCenter : Nonempty (SideCenter I copies U t) := by
    obtain ⟨K⟩ := ActualTaggedOrderedSampleNonempty.taggedCenterOver_nonempty
      I copies U htJ
    exact ⟨centerToSide I copies U K⟩
  have hsideComp : Nonempty (SideComplement I copies U) := by
    obtain ⟨K⟩ := hsideCenter
    have hover : 0 < Fintype.card (SideComplementOver I copies U K) := by
      rw [side_complements_over_card I copies U K]
      positivity
    obtain ⟨A⟩ := Fintype.card_pos_iff.mp hover
    exact ⟨A.1⟩
  have hcomp : 0 < Fintype.card (SideComplement I copies U) :=
    Fintype.card_pos_iff.mpr hsideComp
  have hcompRat : (Fintype.card (SideComplement I copies U) : Rat) > 0 :=
    Nat.cast_pos.mpr hcomp
  have htransport (A : SideComplement I copies U) :
      complementFullAcceptMass I copies U A C T' <=
        transportedStarDensity I copies U A ht hh C T' :=
    complementFullAcceptMass_le_transportedStarDensity I copies U A ht hh C T'
  have haverage : e <=
      ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
        sum A : SideComplement I copies U,
          transportedStarDensity I copies U A ht hh C T' := by
    calc
      e <= sideConditionalDensity I copies U t h k C T' := hscore
      _ = ordinaryComplementStarDensity I copies U t h k C T' :=
        sideConditionalDensity_eq_ordinaryComplementStarDensity
          I copies U ht hh C T'
      _ = ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
          sum A : SideComplement I copies U,
            complementFullAcceptMass I copies U A C T' :=
        ordinaryComplementStarDensity_eq_average_fullMass I copies U C T'
      _ <= ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
          sum A : SideComplement I copies U,
            transportedStarDensity I copies U A ht hh C T' := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun A _ => htransport A)
        · positivity
  have hsum :
      (Fintype.card (SideComplement I copies U) : Rat) * e <=
        sum A : SideComplement I copies U,
          transportedStarDensity I copies U A ht hh C T' := by
    calc
      _ <= (Fintype.card (SideComplement I copies U) : Rat) *
          (((1 : Rat) / Fintype.card (SideComplement I copies U)) *
            sum A : SideComplement I copies U,
              transportedStarDensity I copies U A ht hh C T') :=
        mul_le_mul_of_nonneg_left haverage (by positivity)
      _ = _ := by
        have hcardNe : (Fintype.card (SideComplement I copies U) : Rat) ≠ 0 :=
          ne_of_gt hcompRat
        field_simp [hcardNe] <;> ring
  obtain ⟨A, _, hA⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ)
    (f := fun _ : SideComplement I copies U => e)
    (g := fun A => transportedStarDensity I copies U A ht hh C T')
    Finset.univ_nonempty hsum
  exact ⟨A, hA⟩

end
end PvNP.RealizableHardness.ActualGlobalDensityBridge
