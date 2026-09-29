import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge

/-! Fixed-center finite mass domination after transporting the actual leaves by
their exact equivalence to star leaves. The actual test retains every row
check; only its pointwise implication to ordinary star acceptance is used. -/
namespace PvNP.RealizableHardness.ActualTaggedComplementStarLeafMassBound

open PvNP.RealizableHardness
open ActualTaggedComplementIncidence
open ActualTaggedComplementStarDensityBridge
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

/-- Star mass at the center corresponding to a source complement center,
including the same uniform-center factor used by the actual complement law. -/
def starLeafMassAtCenter (A : SideComplement I copies U)
    {t h k : Nat} (Kc : CenterInComplement I copies U A t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : Rat :=
  ∑ Ls : Fin k → LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h),
    ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
      ((1 : Rat) / Fintype.card
        (Fin k → LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h))) *
        (if StarAccepts (transportedCenterTable I copies U A C)
              (transportedLeafTable I copies U A T')
              (sideCenterToOrdinary I copies U A Kc) Ls then 1 else 0)

/-- The actual source leaf mass at one fixed center is bounded by the star
leaf mass through the same transported tables. -/
theorem actualLeafMassAtCenter_le_starLeafMassAtCenter
    (A : SideComplement I copies U) {t h k : Nat}
    (Kc : CenterInComplement I copies U A t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    (∑ Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
      ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
        ((1 : Rat) / Fintype.card
          (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
          (if fullAccepts I copies U Kc.1 C T'
                (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))
           then 1 else 0)) ≤
      starLeafMassAtCenter I copies U A (t := t) (h := h) (k := k) Kc C T' := by
  classical
  let eLeaf := Equiv.arrowCongr (Equiv.refl (Fin k))
    (ordinaryStarLeafEquiv I copies U A (t := t) (h := h) Kc)
  calc
    (∑ Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
      ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
        ((1 : Rat) / Fintype.card
          (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
          (if fullAccepts I copies U Kc.1 C T'
                (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))
           then 1 else 0)) =
    ∑ Ls : Fin k → LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h),
      ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
        ((1 : Rat) / Fintype.card
          (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
          (if fullAccepts I copies U Kc.1 C T'
                (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (eLeaf.symm Ls i))
           then 1 else 0) := by
      apply Fintype.sum_equiv eLeaf
      intro Ls
      let mass := fun Ys : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h =>
        ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
          ((1 : Rat) / Fintype.card
            (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)) *
          (if fullAccepts I copies U Kc.1 C T'
                (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ys i))
           then 1 else 0)
      exact (congrArg mass (eLeaf.left_inv Ls)).symm
    _ ≤ starLeafMassAtCenter I copies U A Kc C T' := by
      unfold starLeafMassAtCenter
      rw [Fintype.card_congr eLeaf]
      apply Finset.sum_le_sum
      intro Ls _
      have hforce : fullAccepts I copies U Kc.1 C T'
          (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (eLeaf.symm Ls i)) →
          StarAccepts (transportedCenterTable I copies U A C)
            (transportedLeafTable I copies U A T')
            (sideCenterToOrdinary I copies U A Kc) Ls := by
        intro hactual
        have hbridge := actual_implies_ordinary_star_accepts I copies U A Kc
          (fun i => eLeaf.symm Ls i) C T' hactual
        have htuple : (fun i => ordinaryToStarLeaf I copies U A Kc
            (eLeaf.symm Ls i)) = Ls := by
          funext i
          exact (ordinaryStarLeafEquiv I copies U A (t := t) (h := h) Kc).left_inv (Ls i)
        simpa [htuple] using hbridge
      by_cases hacc : fullAccepts I copies U Kc.1 C T'
          (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (eLeaf.symm Ls i))
      · have hstar := hforce hacc
        simp [hacc, hstar]
      · have hw : 0 ≤
            ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
              ((1 : Rat) / Fintype.card
                (Fin k → LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h))) := by
          positivity
        simp [hacc]
        positivity

end
end PvNP.RealizableHardness.ActualTaggedComplementStarLeafMassBound
