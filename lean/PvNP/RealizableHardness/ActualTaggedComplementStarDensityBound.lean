import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualTaggedComplementStarLeafMassBound
import PvNP.RealizableHardness.ActualFiniteScalarSumReindex

/-! Fixed-complement force bridge from the row-checked source experiment to
the ordinary changed-ambient star density. -/
namespace PvNP.RealizableHardness.ActualTaggedComplementStarDensityBound

open PvNP.RealizableHardness
open ActualTaggedComplementIncidence
open ActualTaggedMZSideDraw
open ActualTaggedComplementStarDensityBridge
open ActualTaggedComplementStarLeafMassBound
open ActualFiniteScalarSumReindex
open ActualChangedAmbient8SBoundary
open ActualTaggedFixedCenterGeometry
open ActualTaggedFixedTableAcceptance
open ActualTaggedConcreteStarLaw
open ActualFiniteLaw
open ActualBinaryGrassmannIncidence
open ActualSourceStarLaw
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

/-- The actual complement experiment at fixed `A`: center and leaf fibers
are the source complement carriers, with all row checks retained. -/
def actualComplementSideDensity (A : SideComplement I copies U)
    {t h k : Nat} (C : TaggedCenterTable I copies)
    (T' : TaggedLeafTable I copies) : Rat :=
  ∑ Kc : CenterInComplement I copies U A t,
    ∑ Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
      ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
        ((1 : Rat) / Fintype.card
          (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
          (if fullAccepts I copies U Kc.1 C T'
            (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i)) then 1 else 0)

theorem actualComplementSideDensity_le_StarDensity
    (A : SideComplement I copies U) {t h k : Nat}
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    actualComplementSideDensity I copies U A (t := t) (h := h) (k := k) C T' ≤
      StarDensity (V := A.1) (k := k)
        (grass_nonempty_of_le (by
          rw [sideComplement_finrank I copies U A]
          omega))
        (fun K => extension_nonempty K ht (by
          rw [sideComplement_finrank I copies U A]
          omega))
        (transportedCenterTable I copies U A C)
        (transportedLeafTable I copies U A T') := by
  classical
  let eCenter := centerInComplementEquiv I copies U A t
  let hcenter : Nonempty (Grass A.1 t) := grass_nonempty_of_le (by
    rw [sideComplement_finrank I copies U A]
    omega)
  let hleaf : ∀ K : Grass A.1 t, Nonempty (LeafOver K (2 * h)) := fun K =>
    extension_nonempty K ht (by
      rw [sideComplement_finrank I copies U A]
      omega)
  letI := hcenter
  let starMass : Grass A.1 t → Rat := fun K =>
    ∑ Ls : Fin k → LeafOver K (2 * h),
      ((1 : Rat) / Fintype.card (Grass A.1 t)) *
        ((1 : Rat) / Fintype.card (Fin k → LeafOver K (2 * h))) *
          (if StarAccepts (transportedCenterTable I copies U A C)
                (transportedLeafTable I copies U A T') K Ls then 1 else 0)
  unfold actualComplementSideDensity StarDensity
  simp only [uniformLaw_apply]
  calc
    (∑ Kc : CenterInComplement I copies U A t,
      ∑ Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
        ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
          ((1 : Rat) / Fintype.card
            (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
            (if fullAccepts I copies U Kc.1 C T'
              (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i)) then 1 else 0)) ≤
      ∑ Kc : CenterInComplement I copies U A t,
        starMass (sideCenterToOrdinary I copies U A Kc) := by
        apply Finset.sum_le_sum
        intro Kc _
        calc
          (∑ Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
            ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
              ((1 : Rat) / Fintype.card
                (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
                (if fullAccepts I copies U Kc.1 C T'
                  (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))
                 then 1 else 0)) ≤
          starLeafMassAtCenter I copies U A Kc C T' :=
            actualLeafMassAtCenter_le_starLeafMassAtCenter I copies U A Kc C T'
          _ = starMass (sideCenterToOrdinary I copies U A Kc) := by
            unfold starLeafMassAtCenter starMass
            rw [Fintype.card_congr eCenter]
    _ = ∑ K : Grass A.1 t, starMass K := by
        change (∑ Kc : CenterInComplement I copies U A t,
          starMass (eCenter.symm Kc)) = ∑ K : Grass A.1 t, starMass K
        exact sum_equiv_scalar eCenter.symm starMass
    _ = StarDensity (V := A.1) (k := k) hcenter hleaf
          (transportedCenterTable I copies U A C)
          (transportedLeafTable I copies U A T') := by
        simp only [starMass, StarDensity, uniformLaw_apply]

/-- The existing observed-law density is exactly the uniform complement
average of the actual per-complement density defined above. -/
theorem ordinaryComplementStarDensity_eq_uniform_actualComplementSideDensity
    {t h k : Nat} (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    ordinaryComplementStarDensity I copies U t h k C T' =
      ∑ A : SideComplement I copies U,
        ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
          actualComplementSideDensity I copies U A (t := t) (h := h) (k := k) C T' := by
  classical
  unfold ordinaryComplementStarDensity actualComplementSideDensity
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Kc _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Ls _
  ring

/-- Combine the exact source-law complement reindexing with each pointwise
complement domination. The same predraw center and leaf tables occur in every
transported star density. -/
theorem sideConditionalDensity_le_uniformComplement_average_StarDensity
    {t h k : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    sideConditionalDensity I copies U t h k C T' ≤
      ∑ A : SideComplement I copies U,
        ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
          StarDensity (V := A.1) (k := k)
            (grass_nonempty_of_le (by
              rw [sideComplement_finrank I copies U A]
              omega))
            (fun K => extension_nonempty K ht (by
              rw [sideComplement_finrank I copies U A]
              omega))
            (transportedCenterTable I copies U A C)
            (transportedLeafTable I copies U A T') := by
  calc
    sideConditionalDensity I copies U t h k C T' =
        ordinaryComplementStarDensity I copies U t h k C T' :=
      sideConditionalDensity_eq_ordinaryComplementStarDensity I copies U ht hh C T'
    _ = ∑ A : SideComplement I copies U,
          ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
            actualComplementSideDensity I copies U A (t := t) (h := h) (k := k) C T' :=
      ordinaryComplementStarDensity_eq_uniform_actualComplementSideDensity I copies U C T'
    _ ≤ ∑ A : SideComplement I copies U,
          ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
            StarDensity (V := A.1) (k := k)
              (grass_nonempty_of_le (by
                rw [sideComplement_finrank I copies U A]
                omega))
              (fun K => extension_nonempty K ht (by
                rw [sideComplement_finrank I copies U A]
                omega))
              (transportedCenterTable I copies U A C)
              (transportedLeafTable I copies U A T') := by
        apply Finset.sum_le_sum
        intro A _
        apply mul_le_mul_of_nonneg_left
        · exact actualComplementSideDensity_le_StarDensity I copies U A ht hh C T'
        · positivity

end
end PvNP.RealizableHardness.ActualTaggedComplementStarDensityBound


