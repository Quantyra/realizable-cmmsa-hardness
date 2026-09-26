import PvNP.RealizableHardness.ActualDecodeInputFP
import Mathlib.Algebra.Order.Floor.Div

/-!
Packed unsigned arithmetic wires for the selected CMMSA rounding path.

The input to the arithmetic wires is a pairing of little-endian natural
bitstrings.  The public arithmetic wires in `ActualDecodeInputFP` are total on
all tapes; the semantic statements below intentionally assume only a positive
denominator and canonical input bits.  Thus malformed tapes remain harmless
total FP functions, while valid fraction arithmetic is exposed to the
executor.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaRoundingFP

open Complexity
open CMMSACodec hiding Tree
open CMMSAEncoding
open ActualDecodeInputFP
open ExecutableRounding
set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ## Packed ceil division -/

def quotientTimesDenominator (z : List Bool) : List Bool :=
  mulCanonPair (pair (quotBitsPair z) (pairSnd z))

def remainderBits (z : List Bool) : List Bool :=
  subCanonPair (pair (pairFst z) (quotientTimesDenominator z))

def remainderPositiveFlag (z : List Bool) : List Bool :=
  ltCanonPair (pair [] (remainderBits z))

def incrementedQuotient (z : List Bool) : List Bool :=
  addCanonPair (pair (quotBitsPair z) [true])

/-- Total ceil wire.  A zero denominator inherits the total behavior of the
underlying quotient wire; the semantic theorem below is stated for positive
denominators only. -/
def ceilBits (z : List Bool) : List Bool :=
  Cobham.selectHead (remainderPositiveFlag z)
    (incrementedQuotient z) (quotBitsPair z)

set_option maxHeartbeats 800000 in
theorem quotientTimesDenominator_mem_FP : quotientTimesDenominator ∈ FP := by
  change (fun z : List Bool =>
    mulCanonPair (pair (quotBitsPair z) (pairSnd z))) ∈ FP
  have hpair : (fun z : List Bool =>
      pair (quotBitsPair z) (pairSnd z)) ∈ FP :=
    Cobham.pairFn_mem_FP quotBitsPair_mem_FP Cobham.sndBlock_mem_FP
  exact mulCanonPair_comp_mem_FP hpair

set_option maxHeartbeats 800000 in
theorem remainderBits_mem_FP : remainderBits ∈ FP := by
  change (fun z : List Bool =>
    subCanonPair (pair (pairFst z) (quotientTimesDenominator z))) ∈ FP
  have hpair : (fun z : List Bool =>
      pair (pairFst z) (quotientTimesDenominator z)) ∈ FP :=
    Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
      quotientTimesDenominator_mem_FP
  exact subCanonPair_comp_mem_FP hpair

set_option maxHeartbeats 800000 in
theorem remainderPositiveFlag_mem_FP : remainderPositiveFlag ∈ FP := by
  change (fun z : List Bool =>
    ltCanonPair (pair [] (remainderBits z))) ∈ FP
  have hpair : (fun z : List Bool => pair [] (remainderBits z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) remainderBits_mem_FP
  exact ltCanonPair_comp_mem_FP hpair

set_option maxHeartbeats 800000 in
theorem incrementedQuotient_mem_FP : incrementedQuotient ∈ FP := by
  change (fun z : List Bool =>
    addCanonPair (pair (quotBitsPair z) [true])) ∈ FP
  have hpair : (fun z : List Bool => pair (quotBitsPair z) [true]) ∈ FP :=
    Cobham.pairFn_mem_FP quotBitsPair_mem_FP (constFn_mem_FP [true])
  exact addCanonPair_comp_mem_FP hpair

set_option maxHeartbeats 800000 in
theorem ceilBits_mem_FP : ceilBits ∈ FP := by
  change (fun z : List Bool =>
    Cobham.selectHead (remainderPositiveFlag z)
      (incrementedQuotient z) (quotBitsPair z)) ∈ FP
  exact Cobham.selectHeadFn_mem_FP remainderPositiveFlag_mem_FP
    incrementedQuotient_mem_FP quotBitsPair_mem_FP

theorem quotientTimesDenominator_bitValue (z : List Bool)
    (hb : 0 < bitValue (pairSnd z)) :
    bitValue (quotientTimesDenominator z) =
      (bitValue (pairFst z) / bitValue (pairSnd z)) * bitValue (pairSnd z) := by
  rw [quotientTimesDenominator, mulCanonPair_bitValue,
    quotBitsPair_eq_bits z hb]
  simp [pairFst_pair, pairSnd_pair, bitValue_bits]

set_option maxHeartbeats 800000 in
theorem remainderBits_bitValue (z : List Bool)
    (hb : 0 < bitValue (pairSnd z)) :
    bitValue (remainderBits z) =
      bitValue (pairFst z) -
        (bitValue (pairFst z) / bitValue (pairSnd z)) * bitValue (pairSnd z) := by
  have hprod :
      bitValue (quotientTimesDenominator z) ≤ bitValue (pairFst z) := by
    rw [quotientTimesDenominator_bitValue z hb]
    exact Nat.div_mul_le_self _ _
  calc
    bitValue (remainderBits z) =
        bitValue (pairFst z) - bitValue (quotientTimesDenominator z) := by
      change bitValue (subCanonPair
          (pair (pairFst z) (quotientTimesDenominator z))) = _
      exact subCanonPair_on_pair_bitValue
        (pairFst z) (quotientTimesDenominator z) hprod
    _ = bitValue (pairFst z) -
        (bitValue (pairFst z) / bitValue (pairSnd z)) *
          bitValue (pairSnd z) := by
      rw [quotientTimesDenominator_bitValue z hb]

theorem remainderBits_mod (z : List Bool)
    (hb : 0 < bitValue (pairSnd z)) :
    bitValue (remainderBits z) = bitValue (pairFst z) % bitValue (pairSnd z) := by
  rw [remainderBits_bitValue z hb, Nat.mod_eq_sub_mul_div]
  simp [Nat.mul_comm]

theorem remainderPositiveFlag_true_iff (z : List Bool) :
    remainderPositiveFlag z = [true] ↔
      0 < bitValue (remainderBits z) := by
  simpa [remainderPositiveFlag, bitValue] using
    (ltCanonPair_true_iff (pair [] (remainderBits z)))

theorem ceilBits_eq_quotient_add (z : List Bool)
    (hb : 0 < bitValue (pairSnd z)) :
    ceilBits z =
      ((bitValue (pairFst z) / bitValue (pairSnd z)) +
        if bitValue (pairFst z) % bitValue (pairSnd z) = 0 then 0 else 1).bits := by
  let a : Nat := bitValue (pairFst z)
  let b : Nat := bitValue (pairSnd z)
  let q := a / b
  let r := a % b
  have hq : quotBitsPair z = q.bits := by
    simpa [a, b, q] using quotBitsPair_eq_bits z hb
  have hr : bitValue (remainderBits z) = r := by
    simpa [a, b, r] using remainderBits_mod z hb
  have hcases := ltCanonPair_cases (pair [] (remainderBits z))
  rcases hcases with hflag | hflag
  · have hpos : 0 < bitValue (remainderBits z) :=
      (remainderPositiveFlag_true_iff z).mp hflag
    have hrpos : 0 < r := by simpa [hr] using hpos
    have hqv : bitValue (quotBitsPair z) = q := by
      rw [hq]
      simp [bitValue_bits]
    rw [ceilBits, remainderPositiveFlag, hflag, hq,
      incrementedQuotient, addCanonPair_eq_bits]
    simp [a, b, q, r, hqv, Nat.ne_of_gt hrpos, bitValue]
  · have hnpos : ¬ 0 < bitValue (remainderBits z) := by
      intro hpos
      have htrue : remainderPositiveFlag z = [true] :=
        (remainderPositiveFlag_true_iff z).mpr hpos
      have hne : ([false] : List Bool) = [true] := hflag ▸ htrue
      cases hne
    have hrzero : r = 0 := by simpa [hr] using Nat.eq_zero_of_not_pos hnpos
    have hqv : bitValue (quotBitsPair z) = q := by
      rw [hq]
      simp [bitValue_bits]
    rw [ceilBits, remainderPositiveFlag, hflag, hq]
    simp [a, b, q, r, hqv, hrzero, bitValue]

theorem nat_quotient_add_carry_eq_ceilDiv (a b : Nat) (hb : 0 < b) :
    a / b + (if a % b = 0 then 0 else 1) = a ⌈/⌉ b := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have haddsub : a + b - 1 = a + (b - 1) := by omega
  rw [haddsub]
  have hpred_lt : b - 1 < b := by omega
  have hpred_mod : (b - 1) % b = b - 1 := Nat.mod_eq_of_lt hpred_lt
  have hpred_div : (b - 1) / b = 0 := Nat.div_eq_of_lt hpred_lt
  by_cases hzero : a % b = 0
  · have hsum_lt : a % b + (b - 1) % b < b := by
      rw [hzero, hpred_mod]
      omega
    rw [Nat.add_div_eq_of_add_mod_lt hsum_lt]
    simp [hzero, hpred_div]
  · have hpos : 0 < a % b := Nat.pos_of_ne_zero hzero
    have hsum_ge : b ≤ a % b + (b - 1) % b := by
      rw [hpred_mod]
      omega
    rw [Nat.add_div_eq_of_le_mod_add_mod hsum_ge hb]
    simp [hzero, hpred_div]

theorem ceilBits_eq_ceilDiv (z : List Bool)
    (hb : 0 < bitValue (pairSnd z)) :
    ceilBits z =
      (bitValue (pairFst z) ⌈/⌉ bitValue (pairSnd z)).bits := by
  rw [ceilBits_eq_quotient_add z hb]
  let a : Nat := bitValue (pairFst z)
  let b : Nat := bitValue (pairSnd z)
  change (a / b + if a % b = 0 then 0 else 1).bits = (a ⌈/⌉ b).bits
  rw [nat_quotient_add_carry_eq_ceilDiv a b (by simpa [b] using hb)]
/-! ## Exact fraction-tree serialization -/

def fractionTreeBitsTag (z : List Bool) : List Bool :=
  true :: (natTreeBitsTag (pairFst z) ++ natTreeBitsTag (pairSnd z))

theorem fractionTreeBitsTag_mem_FP : fractionTreeBitsTag ∈ FP := by
  exact Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [true])
      (mem_FP_comp Cobham.fstBlock_mem_FP natTreeBitsTag_mem_FP))
    (mem_FP_comp Cobham.sndBlock_mem_FP natTreeBitsTag_mem_FP)

theorem fractionTreeBitsTag_of_pair (n d : Nat) :
    fractionTreeBitsTag (pair n.bits d.bits) =
      CMMSACodec.Tree.encode (ExecutableRounding.fractionTree n d) := by
  simp [fractionTreeBitsTag, natTreeBitsTag_of_nat, ExecutableRounding.fractionTree,
    pairFst_pair, pairSnd_pair, CMMSACodec.Tree.encode]

end PvNP.RealizableHardness.ActualSelectedCmmsaRoundingFP
