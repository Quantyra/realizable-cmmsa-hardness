import PvNP.RealizableHardness.ActualMaximalPairLadder
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Typed **external** source contracts for the conditional Theorem 1 certificate.

This module currently records only the MZ24 maximal-pair counting contract at
the actual Grassmann-table semantics available in Lean. An inhabitant is an
explicit hypothesis supplied to a later theorem; this file constructs none.
It does not import a source-to-CMMSA reduction or a changed-ambient 8S decoder.

The other five cited contracts are not represented here until their source
games, tagged transverse test, fixed-U decoder output, triple-deletion joint
law, and weighted general star compiler have source-faithful Lean domains.
An abstract proposition field for any of those would hide manuscript-new work.
-/

namespace PvNP.RealizableHardness.ActualTheorem1ExternalContracts

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder

set_option autoImplicit false
noncomputable section

/-- External MZ24 revision 1, Theorem 5.26, specialized to F₂ and the
manuscript's fixed δ = ρ/m. The source fixes ξ = δ⁵, δ₂ = ξ/100 and its
subsidiary integer `t` before taking `h` sufficiently large. Its explicit
`160/δ · B⁻² · 2^[100(t−1)!(10/δ)² h ξ⁻¹]` bound implies the displayed
coarser `B⁻² · 2^(exponentConstant*h)` for a fixed natural constant and
sufficiently large positive `h`. Both that constant and the height cutoff
may depend on fixed `m, ρ`, never on the ambient, table, advice space, or `B`.

The predicate is the actual `(B,1/5)` maximal agreement predicate on uniform
`Zoom[Q,W]`; the codimension bound is imposed on each counted pair. -/
structure ExternalMZ24MaximalPairCount (m r : Nat) (ρ : ℚ) where
  m_pos : 0 < m
  m_ge_two : 2 ≤ m
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  rho_le_small : ρ ≤ 1 / 4000
  /-- The integer advice budget is exactly the manuscript's `10m/ρ`. -/
  budget_eq : (r : ℚ) * ρ = 10 * (m : ℚ)
  heightCutoff : Nat
  exponentConstant : Nat
  bound :
    ∀ (h : Nat), heightCutoff ≤ h →
    ∀ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V],
    2 ^ h ≤ Module.finrank (ZMod 2) V →
    ∀ (a : Nat), a ≤ r →
    ∀ (Q : Grass V a)
      (T : (L : Grass V (2 * h)) → Module.Dual (ZMod 2) L.val)
      (B : ℚ),
      0 < B →
      ((1 / 2 : ℝ) ^
        (2 * (1 - ((ρ : ℝ) / (m : ℝ)) ^ 3) * (h : ℝ)) ≤ (B : ℝ)) →
      ((Set.ncard {P : DecodedPair Q (2 * h) |
        codim P.W ≤ r ∧ MaximalAt T Q B (1 / 5) P} : Nat) : ℝ) ≤
        ((B⁻¹ : ℚ) : ℝ) ^ 2 * (2 : ℝ) ^ (exponentConstant * h)

end
end PvNP.RealizableHardness.ActualTheorem1ExternalContracts
