import PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

/-! Original selected-leaf consumer with the Spectral47 oracle discharged.
All source-height, rho, split and exact squared-energy guards are retained.
This source is a candidate pending authoritative GCP kernel/axiom verification;
it does not close exact manuscript eigenvalue/G-Phi or source/runtime gates. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementSpectral47OriginalApplication

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.MatrixGrassmannIdentity
open PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

theorem selected_leaf_high_energy_le_spectral_original_application
    (sourceHeightCutoff : Real → Nat)
    {n c s h r : Nat} {rho : Real}
    (T : ActualSourceStarLaw.LeafTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (hEven : c + s = 2 * h) (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho ≤ h) :
    uniformMean (fun M : BinaryMatrix n c =>
      (appendAverage (selectedHigh (selectedF T f) (r := r)) M) ^ 2) ≤
      ∑ i ∈ selectedHighFinIndexSet (c + s) r,
        ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
          3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
          uniformMean (fun W =>
            (rankProjection i.val (indicator (selectedF T f)) W) ^ 2) := by
  exact selected_leaf_high_energy_le_spectral
    (n := n) (c := c) (s := s) (h := h) (r := r) (rho := rho)
    sourceHeightCutoff T f hEven hRho hc hs hHeight
    (spectral47_exact_contract_inhabitant sourceHeightCutoff)

end
end PvNP.RealizableHardness.ActualSelectedComplementSpectral47OriginalApplication
