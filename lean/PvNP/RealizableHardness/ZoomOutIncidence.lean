/- UNCOMPILED draft. Proof scripts await author compilation and independent review. -/
import PvNP.RealizableHardness.ConditionedCovering

namespace PvNP.RealizableHardness.ZoomOutIncidence
open scoped BigOperators
open TripleRestrictionRank GrassmannIncidence GrassmannCounting
open GrassmannFlagPosterior ConditionedCovering PosteriorDensity
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J a d : ℕ}

/-- Count actual flags, using the accepted relative quotient equivalence. -/
lemma relative_indicator_sum (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (Q : Advice J a) (hQ : Q.val ≤ W) (had : a ≤ d) :
    (∑ L : Advice J d, if Q.val ≤ L.val ∧ L.val ≤ W then (1 : ℚ) else 0) =
      gaussian (Module.finrank (ZMod 2) W - a) (d - a) := by
  have hn : (∑ L : Advice J d,
      if Q.val ≤ L.val ∧ L.val ≤ W then (1 : ℕ) else 0) =
      gaussian (Module.finrank (ZMod 2) W - a) (d - a) := by
    have hc := card_relativeUpper W Q hQ had
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    let e : Advice J d ≃ Grass (TripleRestrictionRank.Vector J) d := Equiv.refl _
    calc
      _ = ∑ L : Grass (TripleRestrictionRank.Vector J) d,
          if Q.val ≤ L.val ∧ L.val ≤ W then (1 : ℕ) else 0 :=
        e.sum_comp (fun L => if Q.val ≤ L.val ∧ L.val ≤ W then (1 : ℕ) else 0)
      _ = _ := by
        simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          Nat.cast_id, mul_one] using hc
  exact_mod_cast hn

/-- Exact conditioning mass, valid up to the actual retained dimension. -/
lemma retained_event_mass (s : Draw J) (Q : Advice J a)
    (hQ : Q.val ≤ retained s) (had : a ≤ d) :
    containmentProbability s d Q =
      (gaussian (Module.finrank (ZMod 2) (retained s) - a) (d - a) : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained s)) d := by
  rw [containmentProbability_count, card_relativeUpper (retained s) Q hQ had,
    incidenceCount_eq]

lemma retained_event_pos (s : Draw J) (Q : Advice J a)
    (hQ : Q.val ≤ retained s) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s)) :
    0 < containmentProbability s d Q := by
  rw [retained_event_mass s Q hQ had]
  apply div_pos
  · exact_mod_cast GaussianRatio.gaussian_pos (show d - a ≤
      Module.finrank (ZMod 2) (retained s) - a by omega)
  · exact_mod_cast GaussianRatio.gaussian_pos hd

/-- The existing retained conditional law is uniform on its concrete flag fibre. -/
lemma retainedConditional_uniform (s : Draw J) (Q : Advice J a) (L : Advice J d)
    (hQ : Q.val ≤ retained s) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s)) :
    retainedConditional s Q L =
      (if Q.val ≤ L.val ∧ L.val ≤ retained s then (1 : ℚ) else 0) /
        gaussian (Module.finrank (ZMod 2) (retained s) - a) (d - a) := by
  have hn : (gaussian (Module.finrank (ZMod 2) (retained s)) d : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos hd)
  have hg : (gaussian (Module.finrank (ZMod 2) (retained s) - a) (d - a) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos
      (show d - a ≤ Module.finrank (ZMod 2) (retained s) - a by omega))
  unfold retainedConditional
  rw [retained_event_mass s Q hQ had]
  by_cases hQL : Q.val ≤ L.val <;> by_cases hLV : L.val ≤ retained s <;>
    simp [kernel, incidenceCount_eq, hQL, hLV] <;> field_simp [hn, hg]

/-- The event is measured under the accepted retainedConditional, not a surrogate law. -/
def retainedZoomMass (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (d : ℕ) : ℚ :=
  ∑ L : Advice J d, if L.val ≤ W then retainedConditional s Q L else 0

lemma retainedZoomMass_null (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hz : containmentProbability s d Q = 0) : retainedZoomMass s Q W d = 0 := by
  simp [retainedZoomMass, retainedConditional, hz]

lemma retainedZoomMass_noncontainment (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQ : ¬ Q.val ≤ retained s) : retainedZoomMass s Q W d = 0 :=
  retainedZoomMass_null s Q W (containmentProbability_noncontainment s d Q hQ)

lemma retainedZoomMass_dimension_null (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hd : Module.finrank (ZMod 2) (retained s) < d) : retainedZoomMass s Q W d = 0 := by
  apply retainedZoomMass_null
  rw [containmentProbability_count, incidenceCount_of_lt s hd]
  simp

lemma retainedZoomMass_outside (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQW : ¬ Q.val ≤ W) : retainedZoomMass s Q W d = 0 := by
  apply Finset.sum_eq_zero
  intro L _
  by_cases hLW : L.val ≤ W
  · have hQL : ¬ Q.val ≤ L.val := fun h => hQW (h.trans hLW)
    simp [hLW, retainedConditional, hQL]
  · simp [hLW]

/-- Exact zoom-out probability from actual flags in V intersection W.
No rank-stability or ratio premise is assumed. -/
theorem retainedZoomMass_ratio (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ W) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s)) :
    retainedZoomMass s Q W d =
      (gaussian (Module.finrank (ZMod 2) ↥(retained s ⊓ W) - a) (d - a) : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained s) - a) (d - a) := by
  calc
    _ = (∑ L : Advice J d,
        if Q.val ≤ L.val ∧ L.val ≤ retained s ⊓ W then (1 : ℚ) else 0) /
        gaussian (Module.finrank (ZMod 2) (retained s) - a) (d - a) := by
      unfold retainedZoomMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro L _
      rw [retainedConditional_uniform s Q L hQV had hd]
      by_cases hQL : Q.val ≤ L.val <;> by_cases hLV : L.val ≤ retained s <;>
        by_cases hLW : L.val ≤ W <;> simp [hQL, hLV, hLW, le_inf_iff]
    _ = _ := by rw [relative_indicator_sum (retained s ⊓ W) Q (le_inf hQV hQW) had]

/-- Rank stability identifies the numerator dimension by an explicit codimension equation. -/
theorem retainedZoomMass_rank_stable (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (c : ℕ)
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ W) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s))
    (hc : Module.finrank (ZMod 2) ↥(retained s ⊓ W) + c =
      Module.finrank (ZMod 2) (retained s)) :
    retainedZoomMass s Q W d =
      (gaussian (Module.finrank (ZMod 2) (retained s) - a - c) (d - a) : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained s) - a) (d - a) := by
  rw [retainedZoomMass_ratio s Q W hQV hQW had hd]
  have he : Module.finrank (ZMod 2) ↥(retained s ⊓ W) - a =
      Module.finrank (ZMod 2) (retained s) - a - c := by omega
  rw [he]

lemma retainedZoomMass_top (s : Draw J) (Q : Advice J a)
    (hQV : Q.val ≤ retained s) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s)) :
    retainedZoomMass s Q ⊤ d = 1 := by
  simpa [retainedZoomMass] using
    retainedConditional_normalized s Q (retained_event_pos s Q hQV had hd)

/-- The existing ambient conditional law has the same concrete upper-flag formula. -/
lemma ambientConditional_uniform (Q : Advice J a) (L : Advice J d)
    (had : a ≤ d) (hdJ : d ≤ J) :
    ambientConditional Q L = (if Q.val ≤ L.val then (1 : ℚ) else 0) /
      gaussian (3 * J - a) (d - a) := by
  have hn : Module.finrank (ZMod 2) (TripleRestrictionRank.Vector J) = 3 * J := by
    simp [TripleRestrictionRank.Vector, Coord, Module.finrank_pi, Nat.mul_comm]
  have hp : (gaussian (3 * J) a : ℚ) * gaussian (3 * J - a) (d - a) =
      (gaussian (3 * J) d : ℚ) * gaussian d a := by
    have h := flag_product (V := TripleRestrictionRank.Vector J) had
    rw [hn] at h
    exact_mod_cast h
  have ha : (gaussian (3 * J) a : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos (show a ≤ 3 * J by omega))
  have hd : (gaussian (3 * J) d : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos (show d ≤ 3 * J by omega))
  have hb : (gaussian d a : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos had)
  have hu : (gaussian (3 * J - a) (d - a) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GaussianRatio.gaussian_pos (show d - a ≤ 3 * J - a by omega))
  rw [ambientConditional_formula Q L had hdJ]
  by_cases hQL : Q.val ≤ L.val
  · simp only [hQL, ite_true, ambientMass_eq]
    field_simp [ha, hd, hb, hu] <;> nlinarith [hp]
  · simp [hQL]

def ambientZoomMass (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (d : ℕ) : ℚ :=
  ∑ L : Advice J d, if L.val ≤ W then ambientConditional Q L else 0

theorem ambientZoomMass_ratio (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQW : Q.val ≤ W) (had : a ≤ d) (hdJ : d ≤ J) :
    ambientZoomMass Q W d =
      (gaussian (Module.finrank (ZMod 2) W - a) (d - a) : ℚ) /
        gaussian (3 * J - a) (d - a) := by
  calc
    _ = (∑ L : Advice J d,
        if Q.val ≤ L.val ∧ L.val ≤ W then (1 : ℚ) else 0) /
        gaussian (3 * J - a) (d - a) := by
      unfold ambientZoomMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro L _
      rw [ambientConditional_uniform Q L had hdJ]
      by_cases hQL : Q.val ≤ L.val <;> by_cases hLW : L.val ≤ W <;> simp [hQL, hLW]
    _ = _ := by rw [relative_indicator_sum W Q hQW had]

theorem ambientZoomMass_codimension (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (c : ℕ)
    (hQW : Q.val ≤ W) (had : a ≤ d) (hdJ : d ≤ J)
    (hc : Module.finrank (ZMod 2) W + c = 3 * J) :
    ambientZoomMass Q W d =
      (gaussian (3 * J - a - c) (d - a) : ℚ) / gaussian (3 * J - a) (d - a) := by
  rw [ambientZoomMass_ratio Q W hQW had hdJ]
  have he : Module.finrank (ZMod 2) W - a = 3 * J - a - c := by omega
  rw [he]

end
end PvNP.RealizableHardness.ZoomOutIncidence
