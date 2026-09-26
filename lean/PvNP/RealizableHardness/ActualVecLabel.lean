import PvNP.RealizableHardness.ActualBitRestriction
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Encode `Fin (2^(2h))` labels as `F2^{2h}` vectors (standard dual basis).
This is the large-alphabet Grassmann/Hadamard coordinate chart.

Does not compile stars, does not prove `No σ_L γ_L`, does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualVecLabel

open ActualBitRestriction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 200000

def vecOfFin {h : Nat} (a : Fin (alph h)) : Fin (2 * h) → ZMod 2 :=
  fun i => if bit a i then 1 else 0

def finOfBits {h : Nat} (p : Fin (2 * h) → Bool) : Nat :=
  ∑ i : Fin (2 * h), if p i then 2 ^ i.val else 0

private theorem two_pow_coord_sum_lt :
    ∀ n : Nat, (∑ i : Fin n, 2 ^ i.val) < 2 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have ih := two_pow_coord_sum_lt n
      calc
        (∑ i : Fin n, 2 ^ i.val) + 2 ^ n
            < 2 ^ n + 2 ^ n := Nat.add_lt_add_right ih _
        _ = 2 * 2 ^ n := (two_mul (2 ^ n)).symm
        _ = 2 ^ n * 2 := Nat.mul_comm _ _
        _ = 2 ^ (n + 1) := (Nat.pow_succ 2 n).symm

theorem finOfBits_lt {h : Nat} (p : Fin (2 * h) → Bool) :
    finOfBits p < alph h := by
  unfold finOfBits alph
  have hbound :
      (∑ i : Fin (2 * h), if p i then 2 ^ i.val else 0) ≤
        ∑ i : Fin (2 * h), 2 ^ i.val := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp
  exact lt_of_le_of_lt hbound (two_pow_coord_sum_lt (2 * h))

def finOfVec {h : Nat} (x : Fin (2 * h) → ZMod 2) : Fin (alph h) :=
  ⟨finOfBits (fun i => decide (x i = 1)), finOfBits_lt _⟩

theorem vecOfFin_zero {h : Nat} :
    vecOfFin (h := h) ⟨0, alph_pos h⟩ = fun _ => 0 := by
  funext i
  simp [vecOfFin, bit, Nat.zero_testBit]

end PvNP.RealizableHardness.ActualVecLabel
