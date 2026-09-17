/- UNCOMPILED checks: no axiom query or example has been executed. -/
import PvNP.RealizableHardness.ZoomOutParameters
open PvNP.RealizableHardness
open ZoomOutParameters SamplerParameters GaussianNearOne GrassmannCounting

#print axioms ratio_bounds
#print axioms retained_dimension_lower
#print axioms ready_budget
#print axioms eventual_budget
#print axioms dimension_budget
#print axioms retained_bounds
#print axioms ambient_bounds
#print axioms eventual_zoom_out

example : Bounds 4 4 1 1 ((gaussian 3 1 : ℚ) / gaussian 4 1) :=
  ratio_bounds (by omega) (by omega) (by omega)

-- J/2 remains floor division at odd J.
example : Bounds 5 5 1 1 ((gaussian 4 1 : ℚ) / gaussian 5 1) :=
  ratio_bounds (by omega) (by omega) (by omega)

example : Bounds 2 2 0 0 (1 : ℚ) := by
  simpa [gaussian_zero] using
    (ratio_bounds (J := 2) (n := 2) (b := 0) (c := 0)
      (by omega) (by omega) (by omega))

example (r : ℕ) : ∃ N : ℕ, ∀ h : ℕ, N ≤ h → r < h := by
  obtain ⟨N, hN⟩ := eventual_budget 1 r (by omega)
  exact ⟨N, fun h hh => (hN h hh).1⟩

example : 0 < 2*1 ∧ 2*1 ≤ 6 ∧ 0 ≤ 6-0 ∧
    (2*1-0)+1 ≤ (6-0)-0 ∧ (2*1-0)+0+6/2 ≤ 6-0 :=
  dimension_budget (J := 6) (n := 6) (h := 1) (r := 0)
    (a := 0) (c := 0) (by omega) (by omega) (by omega) (by omega) (by omega)

example (s : TripleRestrictionRank.Draw 0) :
    0 ≤ Module.finrank (ZMod 2) (TripleRestrictionRank.retained s) :=
  retained_dimension_lower s

example {J n b c : ℕ} {p : ℚ} (h : Bounds J n b c p) : leading b c / 2 ≤ p :=
  h.2.2.2.2

example {J n b c : ℕ} {p : ℚ} (h : Bounds J n b c p) :
    error (n-c) b ≤ 1/(2 : ℚ)^(J/2) := h.1
