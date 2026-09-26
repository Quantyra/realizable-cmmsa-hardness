import PvNP.RealizableHardness.ActualHeadlineParameters

/-!
Large-alphabet label bits and coordinate restriction for Grassmann/star
projections.  Alphabet `2^(2h)` matches manuscript `ROf L` at `h = hOf L (mOf L)`.

Restriction to the low `k < 2h` bits is not the identity map.  This file does
not compile stars, pack CMMSA data, or inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualBitRestriction

open ActualHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 200000

def alph (h : Nat) : Nat := 2 ^ (2 * h)

theorem alph_eq_ROf (L : Nat) :
    alph (hOf L (mOf L)) = ROf L :=
  rfl

theorem alph_pos (h : Nat) : 0 < alph h :=
  Nat.two_pow_pos _

def bit {h : Nat} (a : Fin (alph h)) (i : Fin (2 * h)) : Bool :=
  a.val.testBit i.val

def restrictLow {h k : Nat} (hk : k ≤ 2 * h) (a : Fin (alph h)) :
    Fin (alph h) :=
  ⟨a.val % 2 ^ k,
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k))
      (Nat.pow_le_pow_right (by decide : 0 < 2) hk)⟩

theorem restrictLow_val {h k : Nat} (hk : k ≤ 2 * h) (a : Fin (alph h)) :
    (restrictLow hk a).val = a.val % 2 ^ k :=
  rfl

theorem two_pow_lt_two_pow {k n : Nat} (h : k < n) : 2 ^ k < 2 ^ n :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) h

theorem restrictLow_ne_id {h k : Nat} (hk : k < 2 * h) :
    restrictLow (le_of_lt hk)
        ⟨2 ^ k, two_pow_lt_two_pow hk⟩ ≠
      ⟨2 ^ k, two_pow_lt_two_pow hk⟩ := by
  intro heq
  have hval : 2 ^ k % 2 ^ k = 2 ^ k := congrArg Fin.val heq
  rw [Nat.mod_self] at hval
  exact (Nat.two_pow_pos k).ne hval

end PvNP.RealizableHardness.ActualBitRestriction
