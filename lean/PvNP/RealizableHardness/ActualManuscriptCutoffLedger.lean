import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector
import Mathlib.Tactic

/-!
The finite fixed-parameter height ledger in manuscript Section 10.

The manuscript does not print one closed formula for `h_min`. It requires
`h(L,m)` to exceed every fixed lower bound in the inverse, robust-local,
covering/posterior, and decoder comparisons. In particular, the source's
`O_{m,ρ}` constants and the fixed outer NO constant are chosen before `h`.
The named entries below are *parameters*, not proved source bounds. This
module proves only their finite maximum and its selector consequences.

The concrete guards `Rof m + 4`, `16`, and `4*m` encode respectively the
robust-local conditions `h ≥ r+4`, `h ≥ 16` (body.tex, robust-local proof),
and a conservative form of the amplification condition
`2hm(ξ-1000ρ) ≥ 5` for `ξ=1/m²`, `ρ=1/(4000m²)` (body.tex, Section 7).
The existing selector already includes `σ_base ≥ 8`, denominator
divisibility and leaf fit. No statement here certifies the full numerical
ledger or the source-to-CMMSA reduction.
-/

namespace PvNP.RealizableHardness.ActualManuscriptCutoffLedger

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualMZ24FixedRhoPointwiseSelector

/-- Fixed cutoffs that still require separate proofs against the exact
inequalities in body.tex. They depend on the fixed source and outer
constants, including the fixed `A`, but never on the later `τ`. -/
structure SourceHeightBounds where
  inverse : Nat → Nat
  robustHistory : Nat → Nat
  covering : Nat → Nat
  posterior : Nat → Nat
  maximalCount : Nat → Nat
  outerDecoder : Nat → Nat
  compilation : Nat → Nat

/-- A finite, pointwise height floor. The entries are distinct so that a
certificate can enumerate which numeric obligations remain conditional. -/
def sourceHeightFloor (bounds : SourceHeightBounds) (m : Nat) : Nat :=
  max (Rof m + 4)
    (max 16
      (max (4 * m)
        (max (bounds.inverse m)
          (max (bounds.robustHistory m)
            (max (bounds.covering m)
              (max (bounds.posterior m)
                (max (bounds.maximalCount m)
                  (max (bounds.outerDecoder m) (bounds.compilation m)))))))))

/-- The fixed-parameter ledger at a selected block. This does not claim
that the named entries have been proved sufficient for the source bounds. -/
def HeightLedgerReady (bounds : SourceHeightBounds) (m h : Nat) : Prop :=
  Rof m + 4 ≤ h ∧ 16 ≤ h ∧ 4 * m ≤ h ∧
  bounds.inverse m ≤ h ∧ bounds.robustHistory m ≤ h ∧
  bounds.covering m ≤ h ∧ bounds.posterior m ≤ h ∧
  bounds.maximalCount m ≤ h ∧ bounds.outerDecoder m ≤ h ∧
  bounds.compilation m ≤ h

/-- The explicit `4m` guard implies the manuscript's fixed-rho
amplification margin `2hm(ξ-1000ρ) ≥ 5`. It is deliberately stronger
than the exact lower cutoff and has no dependence on the late `τ`. -/
theorem amplification_margin_of_four_mul_m {m h : Nat}
    (hm : 0 < m) (hh : 4 * m ≤ h) :
    (5 : Rat) ≤
      2 * (h : Rat) * (m : Rat) * (manuscriptXi m - 1000 * fixedRho m) := by
  have hmrat : (0 : Rat) < m := by exact_mod_cast hm
  have hhrat : 4 * (m : Rat) ≤ h := by exact_mod_cast hh
  have hmne : (m : Rat) ≠ 0 := ne_of_gt hmrat
  have hprod : 4 * (m : Rat)^2 ≤ (h : Rat) * m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhrat) hmrat.le]
  dsimp [manuscriptXi, fixedRho]
  field_simp
  nlinarith [hprod, sq_pos_of_pos hmrat]

theorem ready_of_floor {bounds : SourceHeightBounds} {m h : Nat}
    (hh : sourceHeightFloor bounds m ≤ h) : HeightLedgerReady bounds m h := by
  simpa only [sourceHeightFloor, HeightLedgerReady, max_le_iff] using hh

/-- The same manuscript selector, with the finite ledger in place of the
placeholder `n+2`, is eventually populated for every fixed `m`. The
quantifier on `bounds` is outside the eventual `L` quantifier. -/
theorem selected_ledger_eventually (bounds : SourceHeightBounds) (M : Nat) :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ m : Nat,
        selector (sourceHeightFloor bounds) L = (m : WithBot Nat) ∧
        M ≤ m ∧ Admissible (sourceHeightFloor bounds) L m ∧
        HeightLedgerReady bounds m (hBlock L m) := by
  obtain ⟨L0, hL0⟩ := selector_unbounded (sourceHeightFloor bounds) M
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hsel, hM, hAd⟩ := hL0 L hL
  refine ⟨m, hsel, hM, hAd, ?_⟩
  exact ready_of_floor hAd.2.2.2.2.2.2.2.1

end PvNP.RealizableHardness.ActualManuscriptCutoffLedger
