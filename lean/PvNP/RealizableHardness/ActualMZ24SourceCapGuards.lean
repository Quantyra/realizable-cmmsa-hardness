import PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
import PvNP.RealizableHardness.ActualMZ24D3c5Precomposition
import Mathlib.Tactic

/-! Conditional source-cap guards for the retained MZ24 lane.

This module strengthens an existing sampling cutoff by a stated natural
reserve floor.  The cap specification is only a parameter contract: it does
not assert existence of a source family, a B2b witness, or a D3c5 conclusion.
-/

namespace PvNP.RealizableHardness.ActualMZ24SourceCapGuards

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.GrassmannCounting

set_option maxRecDepth 1000000
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The only extra source-parameter facts asserted by this guard increment. -/
def SourceCapGuardSpec (budget adviceCap : Nat → Nat) (m a0 : Nat) : Prop :=
  2 ≤ budget m ∧ a0 ≤ adviceCap m ∧ adviceCap m ≤ budget m

/-- Conservative undivided height sufficient for the exact retained reserve.
The degree parameter is an explicit argument fixed before selection. -/
def sourceCapReserveFloor (budget adviceCap : Nat → Nat) (D m : Nat) : Nat :=
  3 * budget m + 1000 * (budget m + 1) * D^5 + adviceCap m + 5

/-- Maximum of the established sampling/source floor and the explicit
source-cap reserve floor. -/
def strengthenedHeightFloor (base budget adviceCap : Nat → Nat)
    (D m : Nat) : Nat :=
  max (base m) (sourceCapReserveFloor budget adviceCap D m)

/-- Construct the strengthened cutoff only by domination from the accepted
sampling cutoff contract. -/
def strengthenedSamplingCutoff {Aof budget base adviceCap : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget base) (D : Nat) :
    DominatingSamplingCutoff Aof budget (strengthenedHeightFloor base budget adviceCap D) := by
  refine ⟨H.A_pos, ?_⟩
  intro m
  exact (H.sampling_le m).trans (Nat.le_max_left _ _)

/-- The new exact selector is eventually populated for each fixed threshold.
This theorem gives no computable or runtime bound. -/
theorem strengthened_selector_eventually_exists
    {Aof budget base adviceCap : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget base) (D : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      selector (strengthenedHeightFloor base budget adviceCap D) L ≠ ⊥ := by
  exact selector_eventually_exists
    (strengthenedHeightFloor base budget adviceCap D)

/-- At the selected admissible height, the explicit cap/advice contract
supplies the exact precomposition reserve. -/
theorem selected_source_cap_reserve
    {Aof budget base adviceCap : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget base) (D L m a0 : Nat)
    (hsel : selector (strengthenedHeightFloor base budget adviceCap D) L = (m : WithBot Nat))
    (hcap : SourceCapGuardSpec budget adviceCap m a0) :
    3 * budget m + 1000 * (budget m + 1) * D^5 + a0 + 5 ≤
      10 * hBlock L m := by
  have hAd := (selector_spec hsel).1
  have hsource := hAd.2.2.2.2.2.2.2
  have hfloor := hsource.1
  have hreserve : sourceCapReserveFloor budget adviceCap D m ≤ hBlock L m :=
    (Nat.le_max_right _ _).trans hfloor
  have hadvice : a0 ≤ adviceCap m := hcap.2.1
  dsimp [sourceCapReserveFloor] at hreserve ⊢
  omega

/-- Conditional bundle aligned with the four existing B2b/precomposition
guard arguments.  Codimension remains an explicit upstream obligation. -/
structure SelectedSourceCapGuardBundle
    {Aof budget base adviceCap : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget base)
    (D L m a0 : Nat)
    (hsel : selector (strengthenedHeightFloor base budget adviceCap D) L = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock L m)))
    (Q0 : Grass (retained draw) a0)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock L m)) : Prop where
  had_gap : a0 < 2 * hBlock L m
  hlarge : ∀ i, 10 * (2 * hBlock L m) ≤ Module.finrank (ZMod 2) (P i).W
  hR2 : 2 ≤ budget m
  hreserve : 3 * budget m + 1000 * (budget m + 1) * D^5 + a0 + 5 ≤
    10 * hBlock L m

/-- Derive the selected guard bundle from the explicit cap, advice, and
codimension contracts on the actual retained draw and decoded pairs. -/
theorem selected_source_cap_guard_bundle
    {Aof budget base adviceCap : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget base) (D L m a0 : Nat)
    (hsel : selector (strengthenedHeightFloor base budget adviceCap D) L = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock L m)))
    (Q0 : Grass (retained draw) a0)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock L m))
    (hcap : SourceCapGuardSpec budget adviceCap m a0)
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ budget m) :
    SelectedSourceCapGuardBundle H D L m a0 hsel draw Q0 P := by
  have hAd := (selector_spec hsel).1
  have hsource := hAd.2.2.2.2.2.2.2
  have hfloor := hsource.1
  have hheight : sourceCapReserveFloor budget adviceCap D m ≤ hBlock L m :=
    (Nat.le_max_right _ _).trans hfloor
  have hR : 2 ≤ budget m := hcap.1
  have ha0R : a0 ≤ budget m := hcap.2.1.trans hcap.2.2
  have had_gap : a0 < 2 * hBlock L m := by
    rcases admissible_retained_height_gates
        (strengthenedSamplingCutoff H D) hAd draw with ⟨_, hstrict, _⟩
    omega
  have hreserve :
      3 * budget m + 1000 * (budget m + 1) * D^5 + a0 + 5 ≤
        10 * hBlock L m := by
    have hreserve' := selected_source_cap_reserve H D L m a0 hsel hcap
    omega
  have hlarge : ∀ i, 10 * (2 * hBlock L m) ≤
      Module.finrank (ZMod 2) (P i).W := by
    intro i
    let V := retained draw
    let W := (P i).W
    have hambient : 20 * hBlock L m + budget m ≤
        Module.finrank (ZMod 2) V :=
      (admissible_retained_height_gates
        (strengthenedSamplingCutoff H D) hAd draw).2.2
    have hWle : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V :=
      W.finrank_le
    have hcod : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W ≤
        budget m := by
      simpa [W, ActualMaximalPairLadder.codim] using hcodim i
    have hadd : (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W) +
        Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V :=
      Nat.sub_add_cancel hWle
    have hdim : 20 * hBlock L m ≤ Module.finrank (ZMod 2) W := by omega
    nlinarith
  exact ⟨had_gap, hlarge, hR, hreserve⟩

end
end PvNP.RealizableHardness.ActualMZ24SourceCapGuards
