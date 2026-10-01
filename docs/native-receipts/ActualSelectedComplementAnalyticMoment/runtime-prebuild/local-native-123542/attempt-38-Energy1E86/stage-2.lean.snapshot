import PvNP.RealizableHardness.ActualTypedABCanonicalProjection
import PvNP.RealizableHardness.ActualTypedABProjectionEnergy
import PvNP.RealizableHardness.ActualTypedABRankedTower
import PvNP.RealizableHardness.BinaryMatrixTypedA15Transport

namespace PvNP.RealizableHardness.ActualTypedABRankedProjectionEnergy

open ActualTypedABCanonicalProjection
open ActualTypedABProjectionEnergy
open ActualTypedABRankedTower
open BinaryMatrixTypedA15Transport
open BinaryMatrixTypedA14Line
open BinaryMatrixA1TypedFourier

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The complete composition of actual typed A14 selected filters along an
arbitrary legal ranked tower has the manuscript per-level energy bound. The
proof identifies that composition with the residual-rank projection of the
actual terminal A15 witness, contracts by typed Parseval, and applies the
terminal estimate from globalness of the original carrier function. -/
theorem ranked_selected_filters_projection_energy {n d r k D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    {f : ((V d ⧸ A) →ₗ[F] B) → Complex}
    (tower : ActualTypedABRankedTower A B f r k)
    (hlevel : r + k ≤ D)
    (eps : Real) (heps : 0 ≤ eps)
    (hglobal : UpToTypedNormSqGlobal A B (r + k) eps f) :
    carrierMean (rankedTerminalData tower).Aend
      (rankedTerminalData tower).Bend
      (fun M => Complex.normSq
        (applyCanonicalFilters tower
          (typedComplexRankProjection A B (r + k) f) M)) ≤
      (2 : Real) ^ (10 * D ^ 2) * eps := by
  have hidentity := ranked_terminal_projection_eq_canonicalFilters tower
  have hprojection := typedComplexRankProjection_energy_le
    (j := r) (rankedTerminalData tower).Aend
    (rankedTerminalData tower).Bend (rankedTerminalData tower).fend
  have hterminal := ranked_tower_terminal_energy tower hlevel eps heps hglobal
  calc
    carrierMean (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend
        (fun M => Complex.normSq
          (applyCanonicalFilters tower
            (typedComplexRankProjection A B (r + k) f) M)) =
      carrierMean (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend
        (fun M => Complex.normSq
          (typedComplexRankProjection (rankedTerminalData tower).Aend
            (rankedTerminalData tower).Bend r (rankedTerminalData tower).fend M)) := by
          congr 1
          funext M
          exact congrArg Complex.normSq (congrFun hidentity M).symm
    _ ≤ carrierMean (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend
        (fun M => Complex.normSq ((rankedTerminalData tower).fend M)) :=
          hprojection
    _ ≤ (2 : Real) ^ (10 * D ^ 2) * eps := by
          simpa [BinaryMatrixA1TypedFourier.carrierMean] using hterminal

end
end PvNP.RealizableHardness.ActualTypedABRankedProjectionEnergy
