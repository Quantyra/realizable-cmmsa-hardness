import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import PvNP.RealizableHardness.GrassmannCounting
import PvNP.RealizableHardness.ActualFiniteAppendImageWeighted

/-! Exact frame-product survivor ratio, including zero-width edge cases. -/
namespace PvNP.RealizableHardness.ActualFiniteFrameProductRatio

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualFiniteAppendImageWeighted

set_option autoImplicit false
noncomputable section

private theorem frameProduct_pos_of_le {n i : Nat} (hi : i ≤ n) :
    0 < frameProduct n i := by
  apply Finset.prod_pos
  intro j hj
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

/-- The scaled frame-product inequality also holds when the requested rank
exceeds the base width: that fibre is empty, so its product has a zero factor. -/
theorem frameProduct_scaled_le_all {c s i : Nat} :
    2 ^ (s * i) * frameProduct c i ≤ frameProduct (c + s) i := by
  by_cases hi : i ≤ c
  · exact frameProduct_scaled_le hi
  · have hzero : frameProduct c i = 0 := by
      unfold frameProduct
      let j : Fin i := ⟨c, by omega⟩
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [j]
    simp [hzero]

/-- The fixed-image survivor proportion is bounded by the exact
`2^(-i*s)` term. No `i≤c` hypothesis is required; for `i>c` the numerator
vanishes. -/
theorem frameProduct_ratio_le {c s i : Nat} :
    (frameProduct c i : Real) / (frameProduct (c + s) i : Real) ≤
      (2 : Real) ^ (-((i : Real) * (s : Real))) := by
  have hscaled := frameProduct_scaled_le_all (c := c) (s := s) (i := i)
  have hscaledR :
      (2 : Real) ^ ((s * i : Nat) : Real) * (frameProduct c i : Real) ≤
        (frameProduct (c + s) i : Real) := by
    exact_mod_cast hscaled
  have hden : 0 < (frameProduct (c + s) i : Real) := by
    exact_mod_cast frameProduct_pos_of_le (by omega : i ≤ c + s)
  have hq : 0 ≤ (2 : Real) ^ (-((i : Real) * (s : Real))) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow :
      (2 : Real) ^ (-((i : Real) * (s : Real))) *
          (2 : Real) ^ ((s * i : Nat) : Real) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    have hexp : -((i : Real) * (s : Real)) + ((s * i : Nat) : Real) = 0 := by
      push_cast
      ring
    rw [hexp, Real.rpow_zero]
  apply (div_le_iff₀ hden).2
  calc
    (frameProduct c i : Real) =
        (2 : Real) ^ (-((i : Real) * (s : Real))) *
          ((2 : Real) ^ ((s * i : Nat) : Real) * (frameProduct c i : Real)) := by
            rw [← mul_assoc, hpow, one_mul]
    _ ≤ (2 : Real) ^ (-((i : Real) * (s : Real))) *
          (frameProduct (c + s) i : Real) :=
            mul_le_mul_of_nonneg_left hscaledR hq

end
end PvNP.RealizableHardness.ActualFiniteFrameProductRatio
