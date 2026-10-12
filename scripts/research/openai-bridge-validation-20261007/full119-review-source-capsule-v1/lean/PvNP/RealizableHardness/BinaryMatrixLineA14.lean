import PvNP.RealizableHardness.BinaryMatrixLineTranslation

namespace PvNP.RealizableHardness.BinaryMatrixLineA14

open BinaryMatrixFourier BinaryMatrixFirstDerivative
  BinaryMatrixHybridSelector BinaryMatrixLineTranslation
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem fourierCoeff_mul {n d : ℕ} (a : ℝ)
    (f : BinaryMatrix n d → ℝ) (Y : BinaryMatrix n d) :
    fourierCoeff (fun M => a * f M) Y = a * fourierCoeff f Y := by
  unfold fourierCoeff uniformMean
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

private theorem rankProjection_mul {n d j : ℕ} (a : ℝ)
    (f : BinaryMatrix n d → ℝ) (M : BinaryMatrix n d) :
    rankProjection j (fun N => a * f N) M =
      a * rankProjection j f M := by
  unfold rankProjection
  simp_rw [fourierCoeff_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

private theorem rankProjection_finset_sum {n d j : ℕ}
    {α : Type*} (s : Finset α) (g : α → BinaryMatrix n d → ℝ)
    (M : BinaryMatrix n d) :
    rankProjection j (fun N => ∑ a ∈ s, g a N) M =
      ∑ a ∈ s, rankProjection j (g a) M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rankProjection, fourierCoeff, uniformMean]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [rankProjection_add, ih]

private theorem rankProjection_character {n d j : ℕ}
    (Y M : BinaryMatrix n d) :
    rankProjection j (character Y) M =
      if Y.rank = j then character Y M else 0 := by
  unfold rankProjection
  simp_rw [fourierCoeff_character]
  by_cases h : Y.rank = j <;> simp [h]

/-- Restricting a frequency along one final codomain line loses either
zero or one rank, with the hybrid selector deciding which. -/
theorem input_rank_of_drop_rank {n d j : ℕ}
    (Y : BinaryMatrix n (d + 1))
    (h : (dropLastFrequency Y).rank = j) :
    Y.rank = j ∨ Y.rank = j + 1 := by
  have hh := rank_eq_drop_add_hybrid_indicator Y
  change Y.rank = (dropLastFrequency Y).rank +
    (if hybridLineSelected Y then 1 else 0) at hh
  rw [h] at hh
  by_cases hs : hybridLineSelected Y
  · exact Or.inr (by simpa [hs] using hh)
  · exact Or.inl (by simpa [hs] using hh)

/-- Character-level A14 after the *actual* polynomial, raw restriction,
and output rank projection. The reduced-space orthogonality theorem in
`rankProjection_character` already aggregates equal induced frequencies. -/
theorem rankProjection_restrict_lineP_character {n d j : ℕ}
    (t : Fin n → ZMod 2) (Y : BinaryMatrix n (d + 1))
    (M : BinaryMatrix n d) :
    rankProjection j (rawLastColumnRestrict t (lineP j (character Y))) M =
      if hybridLineSelected Y ∧ Y.rank = j + 1 then
        lastColumnPhase Y t * character (dropLastFrequency Y) M
      else 0 := by
  let c : ℝ :=
    (1 - (2 : ℝ) ^ (j + 1) * lineTranslationMultiplier Y) *
      (1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y)
  have hfun : rawLastColumnRestrict t (lineP j (character Y)) =
      fun N => (c * lastColumnPhase Y t) *
        character (dropLastFrequency Y) N := by
    funext N
    unfold rawLastColumnRestrict
    rw [lineP_character, character_rawLastColumn]
    ring
  rw [hfun, rankProjection_mul, rankProjection_character]
  by_cases hd : (dropLastFrequency Y).rank = j
  · have hr := input_rank_of_drop_rank Y hd
    have hc := lineP_scalar_at_adjacent_rank Y hr
    change c = (if hybridLineSelected Y then 1 else 0) at hc
    rw [if_pos hd, hc]
    by_cases hs : hybridLineSelected Y
    · have hy : Y.rank = j + 1 := by
        have hh := rank_eq_drop_add_hybrid_indicator Y
        change Y.rank = (dropLastFrequency Y).rank +
          (if hybridLineSelected Y then 1 else 0) at hh
        simpa [hd, hs] using hh
      simp [hs, hy]
    · simp [hs]
  · rw [if_neg hd]
    have hn : ¬(hybridLineSelected Y ∧ Y.rank = j + 1) := by
      rintro ⟨hs, hy⟩
      have hh := rank_eq_drop_add_hybrid_indicator Y
      change Y.rank = (dropLastFrequency Y).rank +
        (if hybridLineSelected Y then 1 else 0) at hh
      simp [hs] at hh
      omega
    simp [hn]

private theorem lineP_fourier_expansion {n d j : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ)
    (N : BinaryMatrix n (d + 1)) :
    lineP j f N =
      ∑ Y : BinaryMatrix n (d + 1),
        fourierCoeff f Y * lineP j (character Y) N := by
  calc
    lineP j f N = lineP j
        (fun X => ∑ Y : BinaryMatrix n (d + 1),
          fourierCoeff f Y * character Y X) N := by
            congr 1
            funext X
            exact (fourier_inversion f X).symm
    _ = ∑ Y : BinaryMatrix n (d + 1),
          lineP j (fun X => fourierCoeff f Y * character Y X) N := by
            exact lineP_finset_sum Finset.univ _ N
    _ = ∑ Y : BinaryMatrix n (d + 1),
          fourierCoeff f Y * lineP j (character Y) N := by
            apply Finset.sum_congr rfl
            intro Y _
            exact lineP_mul (j := j) (fourierCoeff f Y) (character Y) N

/-- Exact final-line/full-domain instance of Appendix (A14). The proof
projects the *entire* raw-restricted Fourier expansion on the reduced
matrix space, so frequencies with the same induced frequency are added
before comparison. No unproved collision-disjointness assumption occurs. -/
theorem rankProjection_rawRestrict_lineP_eq_hybridDerivative {n d j : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n d) :
    rankProjection j (rawLastColumnRestrict t (lineP j f)) M =
      hybridLineDerivative t (rankProjection (j + 1) f) M := by
  have hraw : rawLastColumnRestrict t (lineP j f) =
      fun N => ∑ Y : BinaryMatrix n (d + 1),
        fourierCoeff f Y *
          rawLastColumnRestrict t (lineP j (character Y)) N := by
    funext N
    change lineP j f (rawLastColumn N t) =
      ∑ Y : BinaryMatrix n (d + 1),
        fourierCoeff f Y * lineP j (character Y) (rawLastColumn N t)
    exact lineP_fourier_expansion f (rawLastColumn N t)
  rw [hraw, rankProjection_finset_sum]
  simp_rw [rankProjection_mul, rankProjection_restrict_lineP_character]
  rw [hybridLineDerivative_rankProjection]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hs : hybridLineSelected Y <;>
    by_cases hr : Y.rank = j + 1 <;> simp [hs, hr, mul_assoc]

end
end PvNP.RealizableHardness.BinaryMatrixLineA14
