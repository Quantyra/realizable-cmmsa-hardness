import PvNP.RealizableHardness.ActualFiniteAppendExactImageEnergy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! Uncompiled successor candidate: exact frame duality and the manuscript's
s-factor projected-energy formula for the actual unconditional append.
No G/Phi, adjoint, source witness, runtime or manuscript acceptance is asserted. -/
namespace PvNP.RealizableHardness.ActualFiniteFrameProductDuality

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47
open PvNP.RealizableHardness.ActualFiniteAppendExactImageEnergy

set_option autoImplicit false
noncomputable section

private theorem frame_zero {n k : Nat} (h : n < k) : frameProduct n k = 0 := by
  unfold frameProduct
  let j : Fin k := ⟨n, h⟩
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [j]

private theorem frame_pos {n k : Nat} (h : k ≤ n) : 0 < frameProduct n k := by
  apply Finset.prod_pos
  intro j hj
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

private theorem frame_append (n k : Nat) :
    frameProduct n (k + 1) = frameProduct n k * (2 ^ n - 2 ^ k) := by
  simpa only [frameProduct, Fin.val_castSucc, Fin.val_last] using
    (Fin.prod_univ_castSucc (fun j : Fin (k + 1) => 2 ^ n - 2 ^ j.val))

private theorem frame_diagonal (n k : Nat) :
    frameProduct (n + 1) (k + 1) =
      (2 ^ (n + 1) - 1) * 2 ^ k * frameProduct n k := by
  unfold frameProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero]
  have factors (j : Fin k) :
      2 ^ (n + 1) - 2 ^ (j.val + 1) = 2 * (2 ^ n - 2 ^ j.val) := by
    rw [pow_succ, pow_succ, ← Nat.mul_sub_right_distrib, mul_comm]
  simp_rw [factors]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem width_shift {n s : Nat} (hs : s ≤ n + 1) :
    frameProduct (n + 1) s * (2 ^ (n + 1 - s) - 1) =
      frameProduct n s * (2 ^ (n + 1) - 1) := by
  have factor : 2 ^ (n + 1) - 2 ^ s = 2 ^ s * (2 ^ (n + 1 - s) - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add]
    congr 2
    omega
  have equal := (frame_append (n + 1) s).symm.trans (frame_diagonal n s)
  rw [factor] at equal
  have positive : 0 < (2 : Nat) ^ s := pow_pos (by decide) _
  apply Nat.eq_of_mul_eq_mul_left positive
  calc
    2 ^ s * (frameProduct (n + 1) s * (2 ^ (n + 1 - s) - 1)) =
        frameProduct (n + 1) s * (2 ^ s * (2 ^ (n + 1 - s) - 1)) := by ring
    _ = (2 ^ (n + 1) - 1) * 2 ^ s * frameProduct n s := equal
    _ = 2 ^ s * (frameProduct n s * (2 ^ (n + 1) - 1)) := by ring

private theorem frame_duality_nat {c s i : Nat} (hi : i ≤ c + s) :
    frameProduct c i * frameProduct (c + s) s =
      frameProduct (c + s) i * frameProduct (c + s - i) s := by
  induction i generalizing c with
  | zero => simp [frameProduct]
  | succ i ih =>
    cases c with
    | zero =>
      have hleft := frame_zero (n := 0) (k := i + 1) (by omega)
      have hright := frame_zero (n := s - (i + 1)) (k := s) (by omega)
      simp only [Nat.zero_add, hleft, hright, zero_mul, mul_zero]
    | succ c =>
      have bound : i ≤ c + s := by omega
      have old := ih (c := c) bound
      have shift := width_shift (n := c + s) (s := s) (by omega)
      have sub : c + s + 1 - s = c + 1 := by omega
      rw [sub] at shift
      have width : c + 1 + s = c + s + 1 := by omega
      have rank : c + s + 1 - (i + 1) = c + s - i := by omega
      change frameProduct (c + 1) (i + 1) * frameProduct (c + 1 + s) s = _
      rw [width, rank, frame_diagonal c i, frame_diagonal (c + s) i]
      calc
        (2 ^ (c + 1) - 1) * 2 ^ i * frameProduct c i * frameProduct (c + s + 1) s =
            2 ^ i * frameProduct c i *
              (frameProduct (c + s + 1) s * (2 ^ (c + 1) - 1)) := by ring
        _ = 2 ^ i * frameProduct c i *
              (frameProduct (c + s) s * (2 ^ (c + s + 1) - 1)) := by rw [shift]
        _ = (2 ^ (c + s + 1) - 1) * 2 ^ i *
              (frameProduct c i * frameProduct (c + s) s) := by ring
        _ = (2 ^ (c + s + 1) - 1) * 2 ^ i *
              (frameProduct (c + s) i * frameProduct (c + s - i) s) := by rw [old]
        _ = _ := by ring

/-- Dual survivor counts. Both denominators are positive under the rank guard. -/
theorem frameProduct_ratio_duality {c s i : Nat} (hi : i ≤ c + s) :
    (frameProduct c i : Real) / (frameProduct (c + s) i : Real) =
      (frameProduct (c + s - i) s : Real) / (frameProduct (c + s) s : Real) := by
  have di : 0 < (frameProduct (c + s) i : Real) := by exact_mod_cast frame_pos hi
  have ds : 0 < (frameProduct (c + s) s : Real) := by
    exact_mod_cast frame_pos (show s ≤ c + s by omega)
  apply (div_eq_div_iff (ne_of_gt di) (ne_of_gt ds)).2
  have h := frame_duality_nat hi
  rw [mul_comm (frameProduct (c + s) i)] at h
  exact_mod_cast h

private theorem cast_frame {n k : Nat} (hk : k ≤ n) :
    (frameProduct n k : Real) = ∏ j : Fin k, ((2 : Real) ^ n - (2 : Real) ^ j.val) := by
  unfold frameProduct
  push_cast
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))]
  norm_cast

/-- Exact s-factor eigenvalue product, including the genuine zero-factor branch. -/
theorem frameProduct_ratio_eq_product {c s i : Nat} (hi : i ≤ c + s) :
    (frameProduct c i : Real) / (frameProduct (c + s) i : Real) =
      ∏ j : Fin s, (((2 : Real) ^ (c + s - i) - (2 : Real) ^ j.val) /
        ((2 : Real) ^ (c + s) - (2 : Real) ^ j.val)) := by
  classical
  rw [frameProduct_ratio_duality hi]
  by_cases hpos : i ≤ c
  · rw [cast_frame (show s ≤ c + s - i by omega), cast_frame (show s ≤ c + s by omega)]
    exact (Finset.prod_div_distrib _ _).symm
  · have empty := frame_zero (n := c + s - i) (k := s) (by omega)
    rw [empty]
    simp only [Nat.cast_zero, zero_div]
    symm
    let j : Fin s := ⟨c + s - i, by omega⟩
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [j]

/-- The manuscript's exact product-form energy law for invariant real functions,
using the original unconditional append and each carrier's own normalized mean. -/
theorem append_rank_projection_energy_eq_product {n c s i : Nat}
    (hi : i ≤ c + s) (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s)) (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    uniformMean (fun M : BinaryMatrix n c => (appendAverage (rankProjection i F) M) ^ 2) =
      (∏ j : Fin s, (((2 : Real) ^ (c + s - i) - (2 : Real) ^ j.val) /
        ((2 : Real) ^ (c + s) - (2 : Real) ^ j.val))) *
      uniformMean (fun W : BinaryMatrix n (c + s) => (rankProjection i F W) ^ 2) := by
  rw [append_rank_projection_energy_eq_frame_ratio hi F basisInv,
    frameProduct_ratio_eq_product hi]

end
end PvNP.RealizableHardness.ActualFiniteFrameProductDuality
