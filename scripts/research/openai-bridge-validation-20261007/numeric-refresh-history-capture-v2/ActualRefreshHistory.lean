import PvNP.RealizableHardness.ActualRefreshCandidates
import Mathlib.Tactic

/-!
Concrete numeric and finite-history continuation for the actual refresh
candidate carrier. This disjoint offer does not edit any captured predecessor.
The theorem inputs expose the remaining Gaussian-cardinality bridge instead of
assuming it has been accepted by a kernel.
-/
namespace PvNP.RealizableHardness.ActualRefreshHistory

open PvNP.RealizableHardness.ActualRefreshCandidates
open PvNP.RealizableHardness.NumericRefreshTailOffer
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualFiniteLaw
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable (d r n h : Nat)

/-- The manuscript's exponent, with the subtraction guards retained as
explicit arithmetic hypotheses at the point of use. -/
def candidateExponent : Nat :=
  (2 * h - r) * (n - r - 2 * h) + 2 - 4 * h

def candidateCountBound : Real :=
  16 * ((r : Real) + 1)^2 * (2 : Real)^(n * (r + 1))

def candidateTailBound : Real :=
  Real.exp (-((2 : Real)^candidateExponent h r n) / 12)

def candidateUnionBound : Real := candidateCountBound r n * candidateTailBound h r n

/-- Uniform lower bounds on all large actual intersections turn the exact
per-candidate product-law tail into the manuscript's common tail. The premise
is precisely the zoom/intersection estimate that must be supplied from the
actual Gaussian incidence count. -/
theorem candidate_tail_uniform
    (X : Finset (Grass V d))
    (hlarge : ∀ c : Candidate V d r,
      (1 / (2 : Real)^d) * (candidateZoom V d r c).card ≤
        (candidateCoordinates V d r X c).card →
      (2 : Real)^candidateExponent h r n / 4 ≤
        (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card) :
    ∀ c : Candidate V d r,
      realEventMass V d (freshFullLabelLaw V d)
        (candidateFreshFailure V d r X c) ≤ candidateTailBound h r n := by
  intro c
  have hbase := candidateFreshFailure_mass_bound V d r X c
  by_cases hsmall :
      ((candidateCoordinates V d r X c).card : Real) <
        (1 / (2 : Real)^d) * (candidateZoom V d r c).card
  · simp [candidateFreshFailure, hsmall, realEventMass_eq_cast]
  · have hmass := hlarge c (le_of_not_gt hsmall)
    have hexp := Real.exp_le_exp.mpr (by linarith)
    exact le_trans hbase hexp

/-- The all-candidate union is at most the number of candidates times the
uniform tail. The full candidate type was fixed before the fresh table. -/
theorem actual_union_bound_of_card
    (X : Finset (Grass V d))
    (hlarge : ∀ c : Candidate V d r,
      (1 / (2 : Real)^d) * (candidateZoom V d r c).card ≤
        (candidateCoordinates V d r X c).card →
      (2 : Real)^candidateExponent h r n / 4 ≤
        (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card)
    (hcount : (Fintype.card (Candidate V d r) : Real) ≤ candidateCountBound r n) :
    realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r X) ≤ candidateUnionBound h r n := by
  have hsum := allCandidateFreshFailures_mass_bound V d r X
  have hterm := candidate_tail_uniform V d r n h X hlarge
  have hsum' :
      (∑ c : Candidate V d r,
        Real.exp (-((1 / (2 : Real)^d) *
          (candidateCoordinates V d r X c).card) / 3)) ≤
        (Fintype.card (Candidate V d r) : Real) * candidateTailBound h r n := by
    calc
      _ ≤ ∑ _c : Candidate V d r, candidateTailBound h r n :=
        Finset.sum_le_sum (fun c _ => hterm c)
      _ = _ := by simp
  unfold candidateUnionBound
  exact le_trans hsum (hsum'.trans
    (mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)))

/-- Any statewise numeric cutoff for the manuscript's `F_n` makes the actual
all-candidate failure mass strictly below one and therefore gives a positive
mass preserving refresh for every fixed accumulated set X. -/
theorem actual_positive_mass_refresh
    (X : Finset (Grass V d))
    (hlarge : ∀ c : Candidate V d r,
      (1 / (2 : Real)^d) * (candidateZoom V d r c).card ≤
        (candidateCoordinates V d r X c).card →
      (2 : Real)^candidateExponent h r n / 4 ≤
        (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card)
    (hcount : (Fintype.card (Candidate V d r) : Real) ≤ candidateCountBound r n)
    (hcut : candidateUnionBound h r n < 1) :
    ∃ F : RefreshTable V d,
      F ∉ allCandidateFreshFailures V d r X := by
  apply exists_actual_preserving_refresh V d r X
  exact lt_of_le_of_lt
    (actual_union_bound_of_card V d r n h X hlarge hcount) hcut

/-- State-dependent actual failure carrier used by the finite history. The
transition may inspect the selected fresh table, so it can represent an
adaptive inverse choice. -/
def actualStateFailures (X : Finset (Grass V d)) :
    Candidate V d r → Finset (RefreshTable V d) :=
  candidateFreshFailure V d r X

theorem actual_history_mass_lt_one
    (X : Finset (Grass V d))
    (hlarge : ∀ c : Candidate V d r,
      (1 / (2 : Real)^d) * (candidateZoom V d r c).card ≤
        (candidateCoordinates V d r X c).card →
      (2 : Real)^candidateExponent h r n / 4 ≤
        (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card)
    (hcount : (Fintype.card (Candidate V d r) : Real) ≤ candidateCountBound r n)
    (hcut : candidateUnionBound h r n < 1) :
    eventMass (freshFullLabelLaw V d)
      (candidateFailureSet V d (actualStateFailures V d r X)) < 1 := by
  have hreal : realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r X) < 1 :=
    lt_of_le_of_lt (actual_union_bound_of_card V d r n h X hlarge hcount) hcut
  rw [realEventMass_eq_cast] at hreal
  exact_mod_cast hreal

/-- A finite successful history of actual uniform fresh tables exists whenever
the statewise zoom and candidate bounds hold for every reachable accumulated
set. `step` may depend on each selected table; all candidates are protected at
each prior state before the next transition. -/
noncomputable def actualPreservingHistory
    (step : Finset (Grass V d) → RefreshTable V d → Finset (Grass V d))
    (hlarge : ∀ X c,
      (1 / (2 : Real)^d) * (candidateZoom V d r c).card ≤
        (candidateCoordinates V d r X c).card →
      (2 : Real)^candidateExponent h r n / 4 ≤
        (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card)
    (hcount : (Fintype.card (Candidate V d r) : Real) ≤ candidateCountBound r n)
    (hcut : candidateUnionBound h r n < 1)
    (B : Nat) (initial : Finset (Grass V d)) : Fin B → RefreshTable V d :=
  preservingHistory V d step (actualStateFailures V d r) (by
    intro X
    exact actual_history_mass_lt_one V d r n h X (hlarge X) hcount hcut)
    B initial

theorem actualPreservingHistory_protects_every_candidate
    (step : Finset (Grass V d) → RefreshTable V d → Finset (Grass V d))
    (hlarge : ∀ X c,
      (1 / (2 : Real)^d) * (candidateZoom V d r c).card ≤
        (candidateCoordinates V d r X c).card →
      (2 : Real)^candidateExponent h r n / 4 ≤
        (1 / (2 : Real)^d) * (candidateCoordinates V d r X c).card)
    (hcount : (Fintype.card (Candidate V d r) : Real) ≤ candidateCountBound r n)
    (hcut : candidateUnionBound h r n < 1)
    (B : Nat) (initial : Finset (Grass V d)) (i : Fin B) :
    ∀ c : Candidate V d r,
      actualPreservingHistory V d r n h step hlarge hcount hcut B initial i ∉
        actualStateFailures V d r
          (preservingRun V d step (actualStateFailures V d r)
            (fun X => actual_history_mass_lt_one V d r n h X (hlarge X) hcount hcut)
            i.val initial) c := by
  exact preservingHistory_step V d step (actualStateFailures V d r)
    (fun X => actual_history_mass_lt_one V d r n h X (hlarge X) hcount hcut)
    B initial i
/-- If each active inverse step adds more than `epsilon * 2^(-r*n)/8` to a
set of mass at most one, a horizon whose accumulated guaranteed growth
exceeds one cannot consist entirely of active steps. This is an existence-path
conclusion, separate from a random-history failure-probability estimate. -/
theorem active_steps_cannot_fill_horizon
    {epsilon : Real} (heps : 0 < epsilon)
    (B : Nat) (horizonGrowth :
      1 < (B : Real) * (epsilon / (8 * (2 : Real)^(r*n))))
    (activeMass : Nat → Real)
    (hzero : activeMass 0 = 0)
    (hstep : ∀ i, i < B →
      activeMass (i + 1) >
        activeMass i + epsilon / (8 * (2 : Real)^(r*n)))
    (hbounded : ∀ i, activeMass i ≤ 1) :
    ∃ i, i < B ∧
      ¬ (activeMass (i + 1) >
        activeMass i + epsilon / (8 * (2 : Real)^(r*n))) := by
  by_contra h
  push_neg at h
  let delta : Real := epsilon / (8 * (2 : Real)^(r*n))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hlow : ∀ k, k ≤ B → activeMass k ≥ (k : Real) * delta := by
    intro k
    induction k with
    | zero => intro _; simp [hzero]
    | succ k ih =>
      intro hk
      have hklt : k < B := by omega
      have hprev := ih (by omega)
      have hnext := h k hklt
      dsimp [delta] at *
      rw [Nat.cast_succ]
      nlinarith
  have hlast := hlow B (le_refl B)
  have hbound := hbounded B
  dsimp [delta] at horizonGrowth hlast
  linarith
end PvNP.RealizableHardness.ActualRefreshHistory