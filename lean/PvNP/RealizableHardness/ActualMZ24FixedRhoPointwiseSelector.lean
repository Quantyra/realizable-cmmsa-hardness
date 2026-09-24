import PvNP.RealizableHardness.ActualMZ24SourceCapGuards
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! Fixed-rho arithmetic and a pointwise selector/cap bridge.

The source cap is supplied by the caller.  This module does not construct a
decoder, retained family, draw, or source-force statement.  Here the
manuscript's `xi` and fixed `rho` are distinct from the predecessor's MZ24
`tD D` and `inputExponent D c h`: this file does not identify that independent
scalar D with `Dof m`. -/

namespace PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24SourceCapGuards
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualMaximalPairLadder

set_option autoImplicit false
set_option maxRecDepth 1000000
noncomputable section
attribute [local instance] Classical.propDecidable

def manuscriptXi (m : Nat) : Rat := 1 / (m : Rat)^2
def fixedRho (m : Nat) : Rat := 1 / (4000 * (m : Rat)^2)
def fixedDeltaCount (m : Nat) : Rat := fixedRho m / (m : Rat)
def Dof (m : Nat) : Nat := 4000 * m^3
def Rof (m : Nat) : Nat := 10 * Dof m

theorem fixedRho_pos {m : Nat} (hm : 0 < m) : 0 < fixedRho m := by
  dsimp [fixedRho]
  positivity

theorem fixedRho_le_xi_div_4000 {m : Nat} (hm : 0 < m) :
    fixedRho m ≤ manuscriptXi m / 4000 := by
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  dsimp [fixedRho, manuscriptXi]
  field_simp
  <;> norm_num

theorem fixedRho_le_one_div_4000 {m : Nat} (hm : 0 < m) :
    fixedRho m ≤ (1 : Rat) / 4000 := by
  have hm1 : (1 : Rat) ≤ (m : Rat)^2 := by
    have hmr : (1 : Rat) ≤ (m : Rat) := by exact_mod_cast hm
    nlinarith [sq_nonneg ((m : Rat) - 1)]
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  dsimp [fixedRho]
  field_simp
  nlinarith [hm1]

theorem thousand_mul_fixedRho_le_xi_div_four {m : Nat} (hm : 0 < m) :
    1000 * fixedRho m ≤ manuscriptXi m / 4 := by
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  dsimp [fixedRho, manuscriptXi]
  field_simp
  <;> norm_num

theorem fixedDeltaCount_eq (m : Nat) :
    fixedDeltaCount m = 1 / (4000 * (m : Rat)^3) := by
  dsimp [fixedDeltaCount, fixedRho]
  field_simp
  <;> ring

theorem fixedRho_eq_inverse_bOf {m : Nat} (hm : 0 < m) :
    fixedRho m = 1 / (bOf m : Rat) := by
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  dsimp [fixedRho, bOf]
  push_cast
  field_simp
  <;> ring

theorem Dof_eq_denominator_deltaCount {m : Nat} (hm : 0 < m) :
    (Dof m : Rat) = 1 / fixedDeltaCount m := by
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [fixedDeltaCount_eq]
  dsimp [Dof]
  push_cast
  field_simp
  <;> ring

theorem Rof_eq_ten_Dof (m : Nat) : Rof m = 10 * Dof m := rfl

theorem Rof_eq_ten_m_div_fixedRho {m : Nat} (hm : 0 < m) :
    (Rof m : Rat) = 10 * (m : Rat) / fixedRho m := by
  have hm0 : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [fixedRho_eq_inverse_bOf hm]
  dsimp [Rof, Dof, bOf]
  push_cast
  field_simp
  <;> ring

theorem Rof_integral (m : Nat) : ∃ n : Nat, Rof m = n := ⟨Rof m, rfl⟩

theorem two_le_Rof {m : Nat} (hm : 256 ≤ m) : 2 ≤ Rof m := by
  have hmpos : 0 < m := by omega
  have hpow : 1 ≤ m^3 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos hmpos))
  dsimp [Rof, Dof]
  omega

theorem bOf_dvd_hBlock_fixed (L m : Nat) : bOf m ∣ hBlock L m :=
  bOf_dvd_hBlock L m

private theorem fixedRho_mul_hBlock_eq_quotient (L m : Nat) :
    fixedRho m * (hBlock L m : Rat) = (hBlock L m / bOf m : Nat) := by
  by_cases hmpos : 0 < m
  · have hbpos : 0 < bOf m := by dsimp [bOf]; positivity
    have hbne : (bOf m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hbpos)
    have hdvd := bOf_dvd_hBlock_fixed L m
    rw [fixedRho_eq_inverse_bOf hmpos]
    rw [show ((hBlock L m / bOf m : Nat) : Rat) =
        (hBlock L m : Rat) / (bOf m : Rat) from
      Nat.cast_div hdvd hbne]
    field_simp
  · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
    subst m
    norm_num [fixedRho, bOf, hBlock]

/-- The selected block height is divisible by the fixed-rho denominator. -/
theorem fixedRho_hBlock_integral (L m : Nat) :
    ∃ n : Nat, fixedRho m * (hBlock L m : Rat) = n := by
  exact ⟨hBlock L m / bOf m, fixedRho_mul_hBlock_eq_quotient L m⟩

theorem fixedRho_source_cap_guard_spec {m a0 c : Nat}
    (hm : 256 ≤ m) (hdecoder : a0 + c ≤ Rof m) :
    SourceCapGuardSpec Rof Rof m a0 := by
  refine ⟨two_le_Rof hm, ?_, le_rfl⟩
  omega

/-- The complementary fixed-rho height has the same denominator compatibility. -/
theorem twice_complement_fixedRho_hBlock_integral (L m : Nat) :
    ∃ n : Nat, (2 : Rat) * (1 - fixedRho m) * (hBlock L m : Rat) = n := by
  let q := hBlock L m / bOf m
  have hq : fixedRho m * (hBlock L m : Rat) = (q : Rat) :=
    fixedRho_mul_hBlock_eq_quotient L m
  have hqle : q ≤ hBlock L m := Nat.div_le_self _ _
  refine ⟨2 * (hBlock L m - q), ?_⟩
  calc
    (2 : Rat) * (1 - fixedRho m) * (hBlock L m : Rat) =
        2 * ((hBlock L m : Rat) - q) := by rw [← hq]; ring
    _ = (2 * (hBlock L m - q) : Nat) := by
      push_cast
      norm_cast

/-- Pointwise strengthening: `Dof m` is evaluated at the same candidate m
inside the function handed to the existing selector. -/
def fixedRhoHeightFloor (base : Nat → Nat) (m : Nat) : Nat :=
  max (base m) (sourceCapReserveFloor Rof Rof (Dof m) m)

theorem fixedRhoCutoff {Aof base : Nat → Nat}
    (H : DominatingSamplingCutoff Aof Rof base) :
    DominatingSamplingCutoff Aof Rof (fixedRhoHeightFloor base) := by
  refine ⟨H.A_pos, ?_⟩
  intro m
  exact (H.sampling_le m).trans (Nat.le_max_left _ _)

theorem fixedRho_selector_eventually_exists (base : Nat → Nat) :
    ∃ L0, ∀ L, L0 ≤ L → selector (fixedRhoHeightFloor base) L ≠ ⊥ :=
  selector_eventually_exists (fixedRhoHeightFloor base)

theorem fixedRho_selector_eventually_ge_256 (base : Nat → Nat) :
    ∃ L0, ∀ L, L0 ≤ L → ∃ m : Nat,
      selector (fixedRhoHeightFloor base) L = (m : WithBot Nat) ∧
      256 ≤ m ∧ Admissible (fixedRhoHeightFloor base) L m :=
  selector_unbounded (fixedRhoHeightFloor base) 256

theorem fixedRho_selected_reserve {base : Nat → Nat}
    (L m a0 c : Nat)
    (hsel : selector (fixedRhoHeightFloor base) L = (m : WithBot Nat))
    (hdecoder : a0 + c ≤ Rof m) :
    3 * Rof m + 1000 * (Rof m + 1) * (Dof m)^5 + a0 + 5 ≤
      10 * hBlock L m := by
  have hAd := (selector_spec hsel).1
  have hsource := hAd.2.2.2.2.2.2.2
  have hfloor : fixedRhoHeightFloor base m ≤ hBlock L m := hsource.1
  have hcapfloor : sourceCapReserveFloor Rof Rof (Dof m) m ≤ hBlock L m :=
    (Nat.le_max_right _ _).trans hfloor
  dsimp [sourceCapReserveFloor] at hcapfloor ⊢
  omega

/-- Caller-provided decoder/codimension facts are enough for the old cap
contract and the pointwise retained-space proof ingredients. -/
structure FixedRhoSelectedGuardBundle
    {Aof base : Nat → Nat}
    (H : DominatingSamplingCutoff Aof Rof base)
    (L m a0 c : Nat)
    (hsel : selector (fixedRhoHeightFloor base) L = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock L m)))
    (Q0 : Grass (retained draw) a0)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock L m)) : Prop where
  had_gap : a0 < 2 * hBlock L m
  hlarge : ∀ i, 10 * (2 * hBlock L m) ≤ Module.finrank (ZMod 2) (P i).W
  hR2 : 2 ≤ Rof m
  hreserve : 3 * Rof m + 1000 * (Rof m + 1) * (Dof m)^5 + a0 + 5 ≤
    10 * hBlock L m
  hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ Rof m

theorem fixedRho_selected_guard_bundle
    {Aof base : Nat → Nat}
    (H : DominatingSamplingCutoff Aof Rof base)
    (L m a0 c : Nat)
    (hsel : selector (fixedRhoHeightFloor base) L = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock L m)))
    (Q0 : Grass (retained draw) a0)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock L m))
    (hdecoder : a0 + c ≤ Rof m)
    (hcodim : ∀ i, ActualMaximalPairLadder.codim (P i).W ≤ c)
    (hm : 256 ≤ m) :
    FixedRhoSelectedGuardBundle H L m a0 c hsel draw Q0 P := by
  have hAd := (selector_spec hsel).1
  have hadmiss := admissible_retained_height_gates (fixedRhoCutoff H) hAd draw
  have hreserve : 3 * Rof m + 1000 * (Rof m + 1) * (Dof m)^5 + a0 + 5 ≤
      10 * hBlock L m := fixedRho_selected_reserve L m a0 c hsel hdecoder
  have ha0 : a0 ≤ Rof m := by omega
  have hlarge : ∀ i, 10 * (2 * hBlock L m) ≤ Module.finrank (ZMod 2) (P i).W := by
    intro i
    let V := retained draw
    let W := (P i).W
    have hambient : 20 * hBlock L m + Rof m ≤ Module.finrank (ZMod 2) V := by
      exact hadmiss.2.2
    have hWle : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V := W.finrank_le
    have hcod : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W ≤ Rof m := by
      simpa [W, ActualMaximalPairLadder.codim] using (hcodim i).trans (by omega : c ≤ Rof m)
    have hadd : (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W) +
      Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V := Nat.sub_add_cancel hWle
    nlinarith [hambient, hcod, hadd]
  exact ⟨by omega, hlarge, two_le_Rof hm, hreserve, fun i =>
    (hcodim i).trans (by omega : c ≤ Rof m)⟩

end
end PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
