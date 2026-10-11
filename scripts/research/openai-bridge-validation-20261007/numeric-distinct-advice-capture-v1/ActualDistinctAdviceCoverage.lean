import PvNP.RealizableHardness.ActualRefreshGoodCover
import PvNP.RealizableHardness.GrassmannFlagPosterior

/-! Distinct advice counting for the original-good finite zoom cover.
Each Q is counted once regardless of its number of decoded witnesses.
The exact incidence identity precedes any Gaussian estimate or averaging. -/
namespace PvNP.RealizableHardness.ActualDistinctAdviceCoverage

open PvNP.RealizableHardness
open GrassmannCounting GrassmannFlagPosterior ActualMaximalPairLadder
open NumericRefreshFormalOffer ActualRefreshCandidates ActualRefreshGoodCover
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable (d r : Nat)

/-- A set of distinct Q, with the exact-budget witness retained existentially. -/
def goodAdvice (T : RefreshTable V d) (e : Real) (a : Fin (r + 1)) :
    Finset (Grass V a.val) :=
  Finset.univ.filter fun Q => ∃ P : DecodedPair Q d,
    a.val + codim P.W = r ∧ e / 2 < (agreement T Q P : Real)

def goodAdviceFraction (T : RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) : Rat :=
  ((goodAdvice V d r T e a).card : Rat) / Fintype.card (Grass V a.val)

def upperCone {a : Nat} (Q : Grass V a) : Finset (Grass V d) :=
  Finset.univ.filter fun L => Q.val ≤ L.val

def adviceUpperCover (T : RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) : Finset (Grass V d) :=
  (goodAdvice V d r T e a).biUnion (upperCone V d)

theorem mem_goodAdvice_iff (T : RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) (Q : Grass V a.val) :
    Q ∈ goodAdvice V d r T e a ↔ ∃ P : DecodedPair Q d,
      a.val + codim P.W = r ∧ e / 2 < (agreement T Q P : Real) := by
  simp only [goodAdvice, Finset.mem_filter, Finset.mem_univ, true_and]

theorem goodAdviceFraction_nonneg (T : RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) : 0 ≤ goodAdviceFraction V d r T e a := by
  unfold goodAdviceFraction
  positivity

theorem goodAdviceFraction_le_one (T : RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) : goodAdviceFraction V d r T e a ≤ 1 := by
  unfold goodAdviceFraction
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_le_univ (goodAdvice V d r T e a)
  · positivity

theorem upperCone_card {a : Nat} (Q : Grass V a) (had : a ≤ d) :
    (upperCone V d Q).card =
      gaussian (Module.finrank (ZMod 2) V - a) (d - a) := by
  have h := upperCount_eq Q had
  simpa only [upperCount, upperCone, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, Nat.cast_id, mul_one] using h

/-- Membership in the zoom cover supplies a genuine witness for its Q;
the upper-cone cover forgets W and g only after deduplicating Q. -/
theorem goodZoomCover_subset_adviceUpperCover
    (T : RefreshTable V d) (e : Real) :
    originalGoodZoomCover V d r T e ⊆
      Finset.univ.biUnion (adviceUpperCover V d r T e) := by
  intro L hL
  obtain ⟨c, _hc, hLc⟩ := Finset.mem_biUnion.mp hL
  by_cases hg : originallyGood V d r T e c
  · rw [if_pos hg] at hLc
    apply Finset.mem_biUnion.mpr
    refine ⟨c.1, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
    refine ⟨candidateAdvice V d r c, ?_, ?_⟩
    · exact (mem_goodAdvice_iff V d r T e c.1 _).mpr
        ⟨candidatePair V d r c, hg⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ L, (Finset.mem_filter.mp hLc).2.1⟩
  · simp only [if_neg hg, Finset.not_mem_empty] at hLc

theorem adviceUpperCover_card_le (T : RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) (had : a.val ≤ d) :
    (adviceUpperCover V d r T e a).card ≤
      (goodAdvice V d r T e a).card *
        gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val) := by
  apply Finset.card_biUnion_le_card_mul
  intro Q _hQ
  exact (upperCone_card V d Q had).le

theorem goodZoomCover_card_le (T : RefreshTable V d) (e : Real)
    (hrd : r ≤ d) :
    (originalGoodZoomCover V d r T e).card ≤
      ∑ a : Fin (r + 1), (goodAdvice V d r T e a).card *
        gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val) := by
  calc
    _ ≤ (Finset.univ.biUnion (adviceUpperCover V d r T e)).card :=
      Finset.card_le_card (goodZoomCover_subset_adviceUpperCover V d r T e)
    _ ≤ ∑ a : Fin (r + 1), (adviceUpperCover V d r T e a).card :=
      Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun a _ =>
      adviceUpperCover_card_le V d r T e a (by omega)

theorem distinct_advice_incidence_ratio
    (T : RefreshTable V d) (e : Real) (a : Fin (r + 1))
    (had : a.val ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    ((goodAdvice V d r T e a).card : Rat) *
        gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val) /
          Fintype.card (Grass V d) =
      goodAdviceFraction V d r T e a * gaussian d a.val := by
  have hflag : (gaussian (Module.finrank (ZMod 2) V) a.val : Rat) *
      gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val) =
        (gaussian (Module.finrank (ZMod 2) V) d : Rat) * gaussian d a.val := by
    exact_mod_cast flag_product (V := V) had
  have ha : (gaussian (Module.finrank (ZMod 2) V) a.val : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos (had.trans hdV))
  have hd : (gaussian (Module.finrank (ZMod 2) V) d : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos hdV)
  have hratio :
      (gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val) : Rat) /
        gaussian (Module.finrank (ZMod 2) V) d =
      (gaussian d a.val : Rat) / gaussian (Module.finrank (ZMod 2) V) a.val := by
    apply (div_eq_div_iff hd ha).mpr
    nlinarith [hflag]
  unfold goodAdviceFraction
  simp only [card_grass]
  calc
    _ = ((goodAdvice V d r T e a).card : Rat) *
        ((gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val) : Rat) /
          gaussian (Module.finrank (ZMod 2) V) d) := by ring
    _ = ((goodAdvice V d r T e a).card : Rat) *
        ((gaussian d a.val : Rat) / gaussian (Module.finrank (ZMod 2) V) a.val) := by
          rw [hratio]
    _ = _ := by ring

/-- Exact distinct-Q incidence bound; no candidate multiplicity remains. -/
theorem goodZoomCover_mass_le_weighted_advice_fraction
    (T : RefreshTable V d) (e : Real) (hrd : r ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V) :
    ((originalGoodZoomCover V d r T e).card : Rat) / Fintype.card (Grass V d) ≤
      ∑ a : Fin (r + 1), goodAdviceFraction V d r T e a * gaussian d a.val := by
  calc
    _ ≤ (∑ a : Fin (r + 1), ((goodAdvice V d r T e a).card : Rat) *
          gaussian (Module.finrank (ZMod 2) V - a.val) (d - a.val)) /
            Fintype.card (Grass V d) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast goodZoomCover_card_le V d r T e hrd
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      exact distinct_advice_incidence_ratio V d r T e a (by omega) hdV

/-- A supplied numerical Gaussian bound is applied only to the actual
distinct-Q incidence expression; the concrete bound is a separate dependency. -/
theorem goodZoomCover_mass_le_advice_fraction
    (T : RefreshTable V d) (e : Real) (hrd : r ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V) (B : Rat)
    (hB : ∀ a : Fin (r + 1), (gaussian d a.val : Rat) ≤ B) :
    ((originalGoodZoomCover V d r T e).card : Rat) / Fintype.card (Grass V d) ≤
      B * ∑ a : Fin (r + 1), goodAdviceFraction V d r T e a := by
  apply (goodZoomCover_mass_le_weighted_advice_fraction V d r T e hrd hdV).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB a)
      (goodAdviceFraction_nonneg V d r T e a)

theorem summed_good_advice_fraction_lower
    (T : RefreshTable V d) (e : Real) (hrd : r ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V)
    (B D : Rat) (hBpos : 0 < B)
    (hB : ∀ a : Fin (r + 1), (gaussian d a.val : Rat) ≤ B)
    (hcover : D < ((originalGoodZoomCover V d r T e).card : Rat) /
      Fintype.card (Grass V d)) :
    D / B < ∑ a : Fin (r + 1), goodAdviceFraction V d r T e a := by
  apply (div_lt_iff₀ hBpos).mpr
  simpa only [mul_comm] using hcover.trans_le
    (goodZoomCover_mass_le_advice_fraction V d r T e hrd hdV B hB)

end
end PvNP.RealizableHardness.ActualDistinctAdviceCoverage
