import PvNP.RealizableHardness.ActualMZ24SourceCapGuards
import Mathlib.Tactic

/-! Signature, arithmetic, and kill checks for the conditional source-cap
guard increment.  These do not instantiate a source witness or assert a
negative conclusion about inequalities that may hold independently. -/

namespace PvNP.RealizableHardness.ActualMZ24SourceCapGuardsChecks

open PvNP.RealizableHardness.ActualMZ24SourceCapGuards
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualMZ24PointedSamplingProducer

set_option autoImplicit false

-- Existing generic zero-budget cutoff remains expressible, while zero cannot
-- satisfy the new explicit cap contract.
example : DominatingSamplingCutoff (fun _ : Nat => 1) (fun _ => 0)
    (fun _ => samplingHeightCutoff 1 0) := by
  refine ⟨by intro m; norm_num, ?_⟩
  intro m
  change samplingHeightCutoff 1 0 ≤ samplingHeightCutoff 1 0
  exact le_rfl

example : ¬ SourceCapGuardSpec (fun _ : Nat => 0) (fun _ => 0) 0 0 := by
  norm_num [SourceCapGuardSpec]

-- The old B2b lower condition R ≥ 1 cannot provide the new R ≥ 2 field.
example : ¬ (1 ≤ 1 ∧ 2 ≤ (1 : Nat)) := by norm_num

-- An over-cap advice dimension cannot meet the source-cap hypotheses.
example {R a0 advice : Nat}
    (hover : R < a0) : ¬ (a0 ≤ advice ∧ advice ≤ R) := by
  omega

-- An over-budget codimension cannot supply the codimension premise used by
-- the retained rank bridge; no claim is made about rank by itself.
example {R codimW : Nat}
    (hover : R < codimW) : ¬ (codimW ≤ R) := by
  omega

-- Exact positive fixture at the newly defined floor; D remains visible in
-- the floor's arguments and changes its value.
example : SourceCapGuardSpec (fun _ : Nat => 2) (fun _ => 1) 7 1 := by
  norm_num [SourceCapGuardSpec]

example : sourceCapReserveFloor (fun _ : Nat => 2) (fun _ : Nat => 1) 1 7 =
    3012 := by
  norm_num [sourceCapReserveFloor]

example : 3 * 2 + 1000 * (2 + 1) * 1^5 + 1 + 5 ≤ 10 *
    sourceCapReserveFloor (fun _ : Nat => 2) (fun _ : Nat => 1) 1 7 := by
  norm_num [sourceCapReserveFloor]

example : sourceCapReserveFloor (fun _ : Nat => 2) (fun _ : Nat => 1) 2 7 =
    96012 := by
  norm_num [sourceCapReserveFloor]

-- A one-dimensional cap cannot inhabit the guard bundle, for any height.
example {Aof budget base adviceCap : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget base)
    (D L m a0 : Nat)
    (hsel : selector (strengthenedHeightFloor base budget adviceCap D) L =
      (m : WithBot Nat))
    (draw : PvNP.RealizableHardness.TripleRestrictionRank.Draw
      (PvNP.RealizableHardness.SamplerParameters.blocks (Aof m)
        (PvNP.RealizableHardness.ActualCmmsaParameterReconciliation.hBlock L m)))
    (Q0 : PvNP.RealizableHardness.GrassmannCounting.Grass
      (PvNP.RealizableHardness.TripleRestrictionRank.retained draw) a0)
    {K : Type*} [Fintype K]
    (P : K → PvNP.RealizableHardness.ActualMaximalPairLadder.DecodedPair Q0
      (2 * PvNP.RealizableHardness.ActualCmmsaParameterReconciliation.hBlock L m)) :
    ¬ (budget m = 1 ∧
      SelectedSourceCapGuardBundle H D L m a0 hsel draw Q0 P) := by
  rintro ⟨hR, hBundle⟩
  have := hBundle.hR2
  omega

#check SourceCapGuardSpec
#check sourceCapReserveFloor
#check strengthenedHeightFloor
#check strengthenedSamplingCutoff
#check strengthened_selector_eventually_exists
#check selected_source_cap_reserve
#check SelectedSourceCapGuardBundle
#check selected_source_cap_guard_bundle
#check PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction.outputSelectedFamily
#check PvNP.RealizableHardness.ActualMZ24D3c5Precomposition.guarded_loss_ledger

end PvNP.RealizableHardness.ActualMZ24SourceCapGuardsChecks
