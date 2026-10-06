import PvNP.RealizableHardness.ActualFixedFunctionalMatrixLift
import PvNP.RealizableHardness.ActualRankImageRightBasisInvariance

namespace PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualFixedFunctionalMatrixLift
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Ambient (n : Nat) := ActualFixedFunctionalMatrixLift.Ambient n

/-- The actual linear leaf table and the paper's pointwise matchingLeafSet
agree on precisely the same predrawn table and functional. -/
theorem leafMatchBit_eq_matchingLeafSet {n d : Nat}
    (T : LeafTable (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n)) (L : Grass (Ambient n) d) :
    leafMatchBit T f L =
      ActualFixedFunctionalMatrixLift.matchingLeafSet (fun L => T L) f L := by
  unfold ActualFixedFunctionalStarMoment.leafMatchBit
    ActualFixedFunctionalMatrixLift.matchingLeafSet
  apply Bool.decide_congr
  rw [LinearMap.ext_iff]
  simp only [LinearMap.comp_apply]
  constructor
  · intro h x
    exact (h x).symm
  · intro h x
    exact (h x).symm

/-- Equality of the actual and manuscript leaf predicates as Boolean
functions on the full Grassmannian. -/
theorem leafMatchBit_fun_eq_matchingLeafSet {n d : Nat}
    (T : LeafTable (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n)) :
    (fun L : Grass (Ambient n) d => leafMatchBit T f L) =
      ActualFixedFunctionalMatrixLift.matchingLeafSet (fun L => T L) f := by
  funext L
  exact leafMatchBit_eq_matchingLeafSet T f L

/-- The exact existing rank-image lift used by failed_zoom is the same
Boolean matrix function as the actual source leaf lift. -/
theorem actualLeafRankImage_eq_matchingLeafSet {n d : Nat}
    (T : LeafTable (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n)) :
    rankImageBoolean (leafMatchBit T f) =
      rankImageBoolean (ActualFixedFunctionalMatrixLift.matchingLeafSet
        (fun L => T L) f) := by
  exact congrArg rankImageBoolean (leafMatchBit_fun_eq_matchingLeafSet T f)

/-- The equality also holds after applying the matrix indicator used by the
accepted actual appendAverage. -/
theorem actualLeafRankImageIndicator_eq_matchingLeafSet {n d : Nat}
    (T : LeafTable (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n)) (M : BinaryMatrix n d) :
    indicator (rankImageBoolean (leafMatchBit T f)) M =
      indicator (rankImageBoolean (ActualFixedFunctionalMatrixLift.matchingLeafSet
        (fun L => T L) f)) M := by
  rw [actualLeafRankImage_eq_matchingLeafSet T f]

/-- The exact manuscript failed-zoom conclusion, transported onto the same
actual leaf Boolean used by the accepted append-column average. -/
theorem actual_leaf_failed_zoom_gives_nominal_pseudorandom {n d r : Nat}
    (hrd : r < d)
    (T : LeafTable (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n))
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : Grass (Ambient n) q)
      (P : ActualMaximalPairLadder.DecodedPair Q d),
      q + ActualMaximalPairLadder.codim P.W = r →
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
          ActualMaximalPairLadder.agreement (fun L => T L) Q P ≤ e) :
    PseudorandomExact r (2 * (e : Real)) (rankImageBoolean (leafMatchBit T f)) := by
  have hpr := ActualFixedFunctionalMatrixLift.failed_zoom_gives_nominal_pseudorandom
    hrd (fun L => T L) f e he hfail
  rw [actualLeafRankImage_eq_matchingLeafSet T f]
  exact hpr

end
end PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment
