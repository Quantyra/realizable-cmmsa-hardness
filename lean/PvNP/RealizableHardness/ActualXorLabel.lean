import PvNP.RealizableHardness.ActualBitRestriction

/-!
Bitwise XOR on `Fin (2^(2h))` labels.  This is the affine shift used to
fold 3LIN/3SAT right-hand sides into the Grassmann alphabet.

Does not compile stars, does not prove `No σ_L γ_L`, does not inhabit
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualXorLabel

open ActualBitRestriction
set_option autoImplicit false
set_option maxHeartbeats 200000

def xorFin {h : Nat} (a b : Fin (alph h)) : Fin (alph h) :=
  ⟨a.val.xor b.val, Nat.xor_lt_two_pow a.isLt b.isLt⟩

theorem xorFin_val {h : Nat} (a b : Fin (alph h)) :
    (xorFin a b).val = a.val.xor b.val :=
  rfl

theorem xorFin_comm {h : Nat} (a b : Fin (alph h)) :
    xorFin a b = xorFin b a :=
  Fin.ext (Nat.xor_comm _ _)

theorem xorFin_self {h : Nat} (a : Fin (alph h)) :
    xorFin a a = ⟨0, alph_pos h⟩ :=
  Fin.ext (Nat.xor_self _)

theorem xorFin_zero {h : Nat} (a : Fin (alph h)) :
    xorFin a ⟨0, alph_pos h⟩ = a :=
  Fin.ext (Nat.xor_zero a.val)

end PvNP.RealizableHardness.ActualXorLabel
