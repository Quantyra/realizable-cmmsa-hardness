import PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant

/-! The actual selected-leaf HC46 consumer with the original analytic
contract discharged, rather than retained as a caller hypothesis. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementHC46OriginalApplication
open ActualSelectedComplementAnalyticMoment
open ActualBinaryMatrixHC46OriginalExactInhabitant
open BinaryMatrixFourier ActualFixedFunctionalBinaryMatrixMoment
open ActualComplementCoordinateMassBridge
open MatrixLiftNominalDirectComparison ActualFixedFunctionalStarMoment
set_option autoImplicit false
noncomputable section

theorem selected_leaf_HC46_original {n h r i p : Nat} {eta : Real}
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (2 * h))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (hPR : PseudorandomExact r eta (rankImageBoolean (leafMatchBit T f)))
    (hi : i ≤ r) (hp4 : 4 ≤ p) (hpDyadic : ∃ q : Nat, p = 2 ^ q) :
    lpNorm p (rankProjection i (indicator (rankImageBoolean (leafMatchBit T f)))) ≤
      (2 : Real) ^ (500 * i ^ 2 * p) * eta ^ (((p : Real) - 2) / (p : Real)) := by
  exact selected_leaf_HC46_of_exact_PR T f hPR hi hp4 hpDyadic original_HC46_exact

theorem selected_leaf_failed_zoom_HC46_original {n h r i p : Nat}
    (hrd : r < 2 * h)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (2 * h))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : GrassmannCounting.Grass (Fin n → ZMod 2) q)
      (P : ActualMaximalPairLadder.DecodedPair Q (2 * h)),
      q + ActualMaximalPairLadder.codim P.W = r →
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
          ActualMaximalPairLadder.agreement (fun L => T L) Q P ≤ e)
    (hi : i ≤ r) (hp4 : 4 ≤ p) (hpDyadic : ∃ q : Nat, p = 2 ^ q) :
    lpNorm p (rankProjection i (indicator (rankImageBoolean (leafMatchBit T f)))) ≤
      (2 : Real) ^ (500 * i ^ 2 * p) *
        (2 * (e : Real)) ^ (((p : Real) - 2) / (p : Real)) := by
  exact selected_leaf_HC46_original T f
    (selected_leaf_failed_zoom_PR hrd T f e he hfail) hi hp4 hpDyadic

end
end PvNP.RealizableHardness.ActualSelectedComplementHC46OriginalApplication
