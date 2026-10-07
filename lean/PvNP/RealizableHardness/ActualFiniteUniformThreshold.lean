import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-! A scalar finite-law threshold bound. -/
namespace PvNP.RealizableHardness.ActualFiniteUniformThreshold

open scoped BigOperators

noncomputable section

def uniformMean {α : Type*} [Fintype α] (F : α → Rat) : Rat :=
  (∑ a, F a) / Fintype.card α

def uniformGoodMass {α : Type*} [Fintype α] (F : α → Rat) (q : Rat) : Rat :=
  ∑ a, if q / 2 ≤ F a then (1 : Rat) / Fintype.card α else 0

/-- If a uniform finite mean clears q and every value is at most one, at
least q/2 of the uniform mass lies on values at least q/2. -/
theorem half_threshold_good_mass_ge {α : Type*} [Fintype α] [Nonempty α]
    (F : α → Rat) (q : Rat) (hqpos : 0 < q)
    (hF : ∀ a, F a ≤ 1) (hmean : q ≤ uniformMean F) :
    q / 2 ≤ uniformGoodMass F q := by
  classical
  let c : Nat := Fintype.card α
  let w : Rat := 1 / (c : Rat)
  have hcpos : 0 < c := by
    dsimp [c]
    exact Fintype.card_pos
  have hcne : (c : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hcpos.ne'
  have hweight : (∑ _a : α, w) = 1 := by
    change (∑ _a : α, (1 : Rat) / (Fintype.card α : Rat)) = 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr hcpos.ne']
  have hmean_weighted : (∑ a, w * F a) = uniformMean F := by
    unfold uniformMean
    calc
      (∑ a, w * F a) = ∑ a, F a * w := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ a, F a) * w := by rw [← Finset.sum_mul]
      _ = (∑ a, F a) / Fintype.card α := by
        dsimp [w, c]
        ring
  have hqavg : q ≤ ∑ a, w * F a := by
    rw [hmean_weighted]
    exact hmean
  have hwpos : 0 ≤ w := by dsimp [w]; positivity
  let G : Finset α := Finset.univ.filter (fun a => q / 2 ≤ F a)
  have hpoint (a : α) : F a ≤ q / 2 + if a ∈ G then 1 else 0 := by
    by_cases ha : a ∈ G
    · simp [ha]
      linarith [hqpos, hF a]
    · have hlt : F a < q / 2 := by
        have hnot : ¬ q / 2 ≤ F a := by
          simpa [G] using ha
        exact lt_of_not_ge hnot
      simp [ha]
      exact hlt.le
  have hsumPoint : (∑ a, w * F a) ≤
      ∑ a, w * (q / 2 + if a ∈ G then 1 else 0) := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (hpoint a) hwpos
  have hgood : (∑ a, w * (if a ∈ G then 1 else 0)) = uniformGoodMass F q := by
    unfold uniformGoodMass
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ G
    · have hthreshold : q / 2 ≤ F a := (Finset.mem_filter.mp ha).2
      simp [ha, hthreshold, w, c]
    · have hthreshold : ¬ q / 2 ≤ F a := by
        intro h
        exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [ha, hthreshold, w, c]
  have hupper : (∑ a, w * (q / 2 + if a ∈ G then 1 else 0)) =
      q / 2 + uniformGoodMass F q := by
    calc
      _ = ∑ a, (w * (q / 2) + w * (if a ∈ G then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ a, w * (q / 2)) + (∑ a, w * (if a ∈ G then 1 else 0)) :=
        Finset.sum_add_distrib
      _ = q / 2 + uniformGoodMass F q := by
        have hfirst : (∑ a : α, w * (q / 2)) = q / 2 := by
          calc
            _ = (∑ a : α, w) * (q / 2) := by rw [← Finset.sum_mul]
            _ = q / 2 := by rw [hweight]; ring
        rw [hfirst, hgood]
  have hfinal : q ≤ q / 2 + uniformGoodMass F q :=
    le_trans hqavg (le_trans hsumPoint (le_of_eq hupper))
  linarith

end
end PvNP.RealizableHardness.ActualFiniteUniformThreshold
