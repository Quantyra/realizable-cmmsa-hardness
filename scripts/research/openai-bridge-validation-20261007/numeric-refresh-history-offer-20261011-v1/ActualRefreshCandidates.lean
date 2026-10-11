import PvNP.RealizableHardness.NumericRefreshTailOffer
import PvNP.RealizableHardness.ActualMaximalPairLadder
import Mathlib.Tactic

/-!
Actual candidate universe for one refresh state. Every advice subspace, decoded
pair, and linear functional is included before the fresh table is drawn. Each
candidate's strict-tail event is computed on the distinct actual Grassmann
coordinates in `X ∩ Zoom`; the target is the actual restriction of its decoded
functional. The finite union theorem is prior to any adaptive inverse choice.

This module does not yet supply the Gaussian lower bound on every large
intersection, the candidate-cardinality estimate, the numeric `F_n` cutoff,
or the potential stopping and many-Q composition.
-/

namespace PvNP.RealizableHardness.ActualRefreshCandidates

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.NumericRefreshFormalOffer
open PvNP.RealizableHardness.NumericRefreshTailOffer
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable (d r : Nat)

/-- All actual manuscript inverse candidates of budget `r`. The advice
dimension is bounded by `r`, so the index type is finite. -/
abbrev Candidate :=
  Σ a : Fin (r + 1),
    Σ Q : Grass V a.val,
      {P : DecodedPair Q d // a.val + codim P.W ≤ r}

noncomputable instance candidateFintype : Fintype (Candidate V d r) :=
  Fintype.ofFinite _

def candidatePair (c : Candidate V d r) : DecodedPair c.2.1 d := c.2.2.1

def candidateAdvice (c : Candidate V d r) : Grass V c.1.val := c.2.1

def candidateZoom (c : Candidate V d r) : Finset (Grass V d) :=
  Finset.univ.filter fun L =>
    (candidateAdvice V d r c).val ≤ L.val ∧
      L.val ≤ (candidatePair V d r c).W

/-- Distinct coordinates of the current accumulated set which lie in this
candidate's actual zoom. -/
def candidateCoordinates (X : Finset (Grass V d))
    (c : Candidate V d r) : Finset (Grass V d) :=
  X.filter fun L => L ∈ candidateZoom V d r c

/-- Actual dual-label target induced by the decoded functional on `W`. -/
def candidateTarget (c : Candidate V d r) : RefreshTable V d :=
  targetFromMap V d (candidatePair V d r c).W (candidatePair V d r c).g

theorem candidateTarget_restrict (c : Candidate V d r)
    (L : Grass V d) (hL : L.val ≤ (candidatePair V d r c).W) :
    candidateTarget V d r c L =
      (candidatePair V d r c).g.comp (Submodule.inclusion hL) := by
  exact targetFromMap_restrict V d (candidatePair V d r c).W
    (candidatePair V d r c).g L hL

/-- A fresh full table is exceptional for a candidate if more than twice the
actual dual-label mean agrees on its refreshed zoom coordinates. -/
def candidateFreshFailure (X : Finset (Grass V d))
    (c : Candidate V d r) : Finset (RefreshTable V d) :=
  let Z := candidateCoordinates V d r X c
  if (Z.card : Real) < (1 / (2 : Real) ^ d) *
      (candidateZoom V d r c).card then ∅ else
    matchTailEvent V d Z (candidateTarget V d r c)
      (2 * (1 / (2 : Real) ^ d) * Z.card)

/-- Union over every admissible `(Q,W,g)` before inspecting the fresh table. -/
def allCandidateFreshFailures (X : Finset (Grass V d)) :
    Finset (RefreshTable V d) :=
  candidateFailureSet V d (candidateFreshFailure V d r X)

theorem candidateFreshFailure_mass_bound
    (X : Finset (Grass V d)) (c : Candidate V d r) :
    realEventMass V d (freshFullLabelLaw V d)
      (candidateFreshFailure V d r X c) ≤
        Real.exp (-((1 / (2 : Real) ^ d) *
          (candidateCoordinates V d r X c).card) / 3) := by
  classical
  rw [realEventMass_eq_cast]
  unfold candidateFreshFailure
  split_ifs with hsmall
  · simp only [eventMass_empty, Rat.cast_zero]
    exact (Real.exp_pos _).le
  · simpa [candidateCoordinates, candidateTarget] using
      actual_match_tail_bound V d (candidateCoordinates V d r X c)
        (candidateTarget V d r c)

theorem allCandidateFreshFailures_mass_bound
    (X : Finset (Grass V d)) :
    realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r X) ≤
        ∑ c : Candidate V d r,
          Real.exp (-((1 / (2 : Real) ^ d) *
            (candidateCoordinates V d r X c).card) / 3) := by
  classical
  let μ := freshFullLabelLaw V d
  let bad := candidateFreshFailure V d r X
  have hUnion := eventMass_candidateFailureSet_le V d μ bad
  rw [realEventMass_eq_cast]
  calc
    (eventMass μ (candidateFailureSet V d bad) : Real) ≤
        ((∑ c : Candidate V d r, eventMass μ (bad c) : Rat) : Real) := by
          exact_mod_cast hUnion
    _ = ∑ c : Candidate V d r, (eventMass μ (bad c) : Real) := by norm_cast
    _ ≤ ∑ c : Candidate V d r,
          Real.exp (-((1 / (2 : Real) ^ d) *
            (candidateCoordinates V d r X c).card) / 3) :=
          Finset.sum_le_sum (fun c _ => candidateFreshFailure_mass_bound V d r X c)

/-- If the actual all-candidate failure mass is below one, some actual uniform
fresh table preserves every candidate simultaneously for this fixed X. -/
theorem exists_actual_preserving_refresh
    (X : Finset (Grass V d))
    (hbound : realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r X) < 1) :
    ∃ F : RefreshTable V d, F ∉ allCandidateFreshFailures V d r X := by
  have hReal := hbound
  rw [realEventMass_eq_cast] at hReal
  have hRat : eventMass (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r X) < 1 := by
    exact_mod_cast hReal
  exact exists_outside_event_of_mass_lt_one
    (freshFullLabelLaw V d) (allCandidateFreshFailures V d r X) hRat

end
end PvNP.RealizableHardness.ActualRefreshCandidates
