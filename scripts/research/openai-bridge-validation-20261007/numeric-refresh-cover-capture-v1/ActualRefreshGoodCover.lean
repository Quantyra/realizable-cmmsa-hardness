import PvNP.RealizableHardness.ActualRefreshCandidates
import PvNP.RealizableHardness.ActualRefreshProgress
import PvNP.RealizableHardness.ActualOrdinaryStarLeafMarginal

/-! One-refresh finite-cover proof of the robust existential. The actual
all-candidate failure mass supplies the fresh table. This proof does not
assert a bound on a random adaptive history. -/
namespace PvNP.RealizableHardness.ActualRefreshGoodCover

open PvNP.RealizableHardness
open GrassmannCounting ActualMaximalPairLadder ActualChangedAmbient8SBoundary
open NumericRefreshFormalOffer NumericRefreshTailOffer ActualRefreshCandidates
open ActualRefreshProgress ActualOrdinaryStarLeafMarginal

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable (d r : Nat)

def originallyGood (T : RefreshTable V d) (e : Real) (c : Candidate V d r) : Prop :=
  c.1.val + codim (candidatePair V d r c).W = r ∧
    e / 2 < (agreement T (candidateAdvice V d r c) (candidatePair V d r c) : Real)

def originalGoodZoomCover (T : RefreshTable V d) (e : Real) : Finset (Grass V d) :=
  Finset.univ.biUnion fun c : Candidate V d r =>
    if originallyGood V d r T e c then candidateZoom V d r c else ∅

theorem good_zoom_subset_cover
    (T : RefreshTable V d) (e : Real) (c : Candidate V d r)
    (hc : originallyGood V d r T e c) :
    candidateZoom V d r c ⊆ originalGoodZoomCover V d r T e := by
  intro L hL
  apply Finset.mem_biUnion.mpr
  exact ⟨c, Finset.mem_univ c, by simpa only [if_pos hc] using hL⟩

theorem candidateCoordinates_eq_zoom_inter
    (X : Finset (Grass V d)) (c : Candidate V d r) :
    candidateCoordinates V d r X c = candidateZoom V d r c ∩ X := by
  ext L
  simp only [candidateCoordinates, Finset.mem_filter, Finset.mem_inter, and_comm]

theorem candidateZoom_eq_progress_zoom (c : Candidate V d r) :
    candidateZoom V d r c =
      zoomFinset (candidateAdvice V d r c) (candidatePair V d r c) := rfl

/-- The actual simultaneous nonexceptional event bounds refreshed matches
for every candidate, including candidates selected after inspecting F. -/
theorem preserving_refresh_match_bound
    (X : Finset (Grass V d)) (F : RefreshTable V d)
    (hF : F ∉ allCandidateFreshFailures V d r X)
    (c : Candidate V d r) :
    (matchCount V d (candidateZoom V d r c ∩ X) (candidateTarget V d r c) F : Real) ≤
      2 * (1 / (2 : Real)^d) * (candidateZoom V d r c).card := by
  have hc : F ∉ candidateFreshFailure V d r X c := by
    intro hbad
    apply hF
    change F ∈ candidateFailureSet V d (candidateFreshFailure V d r X)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ F, ⟨c, hbad⟩⟩
  let Z := candidateCoordinates V d r X c
  have hsub : Z ⊆ candidateZoom V d r c := by
    intro L hL
    exact (Finset.mem_filter.mp hL).2
  have hcard : (Z.card : Real) ≤ (candidateZoom V d r c).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hmatch : (matchCount V d Z (candidateTarget V d r c) F : Real) ≤ Z.card := by
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset (fun L => F L = candidateTarget V d r c L) Z)
  have hp : (0 : Real) ≤ 1 / (2 : Real)^d := by positivity
  have hbound : (matchCount V d Z (candidateTarget V d r c) F : Real) ≤
      2 * (1 / (2 : Real)^d) * (candidateZoom V d r c).card := by
    by_cases hsmall : (Z.card : Real) <
        (1 / (2 : Real)^d) * (candidateZoom V d r c).card
    · have hnonneg : (0 : Real) ≤
          (1 / (2 : Real)^d) * (candidateZoom V d r c).card := by positivity
      linarith
    · have htail : ¬ (2 * (1 / (2 : Real)^d) * Z.card <
          (matchCount V d Z (candidateTarget V d r c) F : Real)) := by
        change F ∉ (if (Z.card : Real) <
          (1 / (2 : Real)^d) * (candidateZoom V d r c).card then ∅ else
            matchTailEvent V d Z (candidateTarget V d r c)
              (2 * (1 / (2 : Real)^d) * Z.card)) at hc
        rw [if_neg hsmall] at hc
        simpa only [matchTailEvent, Finset.mem_filter, Finset.mem_univ, true_and] using hc
      exact (le_of_not_gt htail).trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  simpa only [Z, candidateCoordinates_eq_zoom_inter] using hbound

def candidateOfExactBudget {a : Nat} (Q : Grass V a) (P : DecodedPair Q d)
    (hbudget : a + codim P.W = r) : Candidate V d r :=
  ⟨⟨a, by omega⟩, Q, ⟨P, hbudget.le⟩⟩

/-- The union of all original-good exact-budget zooms has a preserving
refresh whose actual ordinary-star density falls below half the original.
The fresh table is obtained from a strict bound on the actual bad-event mass. -/
theorem exists_density_halving_refresh_of_good_cover
    {t m : Nat}
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : RefreshTable V d)
    (e : Real) (he : 0 < e)
    (hnoise : 2 * (1 / (2 : Real)^d) ≤ e / 2)
    (hinverse : ∀ T' : RefreshTable V d,
      StarDensity (k := m) hcenter hleaf C T / 2 ≤
        StarDensity (k := m) hcenter hleaf C T' →
      ∃ a : Nat, ∃ Q : Grass V a, ∃ P : DecodedPair Q d,
        a + codim P.W = r ∧ Fintype.card (Zoom Q P) ≠ 0 ∧
          e < (agreement T' Q P : Real))
    (hbad : realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r (originalGoodZoomCover V d r T e)) < 1) :
    ∃ F : RefreshTable V d,
      F ∉ allCandidateFreshFailures V d r (originalGoodZoomCover V d r T e) ∧
      StarDensity (k := m) hcenter hleaf C
        (refresh V d (originalGoodZoomCover V d r T e) T F) <
          StarDensity (k := m) hcenter hleaf C T / 2 := by
  obtain ⟨F, hF⟩ := exists_actual_preserving_refresh V d r
    (originalGoodZoomCover V d r T e) hbad
  refine ⟨F, hF, ?_⟩
  by_contra hnot
  obtain ⟨a, Q, P, hbudget, hne, hagree⟩ := hinverse
    (refresh V d (originalGoodZoomCover V d r T e) T F) (le_of_not_gt hnot)
  let c := candidateOfExactBudget V d r Q P hbudget
  have hpreserve := preserving_refresh_match_bound V d r
    (originalGoodZoomCover V d r T e) F hF c
  have hsmall :
      (matchCount V d (zoomFinset Q P ∩ originalGoodZoomCover V d r T e)
        (targetFromMap V d P.W P.g) F : Real) ≤ e / 2 * (zoomFinset Q P).card := by
    apply le_trans hpreserve
    exact mul_le_mul_of_nonneg_right hnoise (by positivity)
  have hprogress := refreshed_inverse_original_agreement_and_growth
    (originalGoodZoomCover V d r T e) T F Q P e hne hagree hsmall
  have hc : originallyGood V d r T e c := ⟨hbudget, hprogress.2.1⟩
  have hsub : zoomFinset Q P ⊆ originalGoodZoomCover V d r T e :=
    good_zoom_subset_cover V d r T e c hc
  have hout := hprogress.1
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at hout
  simp only [matchCount, Finset.filter_empty, Finset.card_empty, Nat.cast_zero] at hout
  exact (not_lt_of_ge (by positivity)) hout

theorem good_cover_mass_lower_bound
    {t m : Nat} (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) (hm : 0 < m)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : RefreshTable V d)
    (e : Real) (he : 0 < e)
    (hnoise : 2 * (1 / (2 : Real)^d) ≤ e / 2)
    (hinverse : ∀ T' : RefreshTable V d,
      StarDensity (k := m) hcenter hleaf C T / 2 ≤
        StarDensity (k := m) hcenter hleaf C T' →
      ∃ a : Nat, ∃ Q : Grass V a, ∃ P : DecodedPair Q d,
        a + codim P.W = r ∧ Fintype.card (Zoom Q P) ≠ 0 ∧
          e < (agreement T' Q P : Real))
    (hbad : realEventMass V d (freshFullLabelLaw V d)
      (allCandidateFreshFailures V d r (originalGoodZoomCover V d r T e)) < 1) :
    StarDensity (k := m) hcenter hleaf C T / (2 * (m : Rat)) <
      ((originalGoodZoomCover V d r T e).card : Rat) / Fintype.card (Grass V d) := by
  obtain ⟨F, _hF, hdrop⟩ := exists_density_halving_refresh_of_good_cover
    V d r hcenter hleaf C T e he hnoise hinverse hbad
  refine density_halving_forces_changed_mass htd hdV hm hcenter hleaf C T
    (refresh V d (originalGoodZoomCover V d r T e) T F)
    (originalGoodZoomCover V d r T e) ?_ hdrop
  intro L hL
  simp [refresh, hL]

end
end PvNP.RealizableHardness.ActualRefreshGoodCover
