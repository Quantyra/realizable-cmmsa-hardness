import PvNP.RealizableHardness.ActualSelectedCmmsaRoundingFP

/-!
Packed signed rational wires for the total selected-CMMSA arithmetic path.

The representation is `pair sign (pair numerator denominator)`, where `sign`
is `[false]` for nonnegative values and `[true]` for negative values.  The
natural fields are little-endian bitstrings.  The evaluator deliberately
uses Rat division directly, so a zero denominator has the same total value as
Rat division by zero; successful decoded inputs still provide positive
denominators through `signedTree`.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaSignedRatFP

open Complexity
open CMMSACodec hiding Tree
open CMMSAEncoding
open ActualDecodeInputFP
open ActualSelectedCmmsaRoundingFP
open ExecutablePipelineInput

set_option autoImplicit false
set_option maxHeartbeats 400000

abbrev Bits := CMMSACodec.Bits

def signedSign (z : Bits) : Bits := pairFst z

def signedMagnitude (z : Bits) : Bits := pairSnd z

def signedNumerator (z : Bits) : Bits := pairFst (signedMagnitude z)

def signedDenominator (z : Bits) : Bits := pairSnd (signedMagnitude z)

def signedRatValue (z : Bits) : Rat :=
  (if signedSign z = [true] then
      -((bitValue (signedNumerator z) : Rat))
    else
      (bitValue (signedNumerator z) : Rat)) /
    (bitValue (signedDenominator z) : Rat)

def signedRatWire (q : Rat) : Bits :=
  pair (if q < 0 then [true] else [false])
    (pair q.num.natAbs.bits q.den.bits)

def signedRatTreeWire (z : Bits) : Bits :=
  pair
    (if nodeLeftTag z = [true, false, false] then [true] else [false])
    (pair
      (dropOne (natBitsTag (nodeLeftTag (nodeRightTag z))))
      (dropOne (natBitsTag (nodeRightTag (nodeRightTag z)))))

theorem signedSign_signedRatWire (q : Rat) :
    signedSign (signedRatWire q) = if q < 0 then [true] else [false] := by
  simp [signedSign, signedRatWire]

theorem signedNumerator_signedRatWire (q : Rat) :
    signedNumerator (signedRatWire q) = q.num.natAbs.bits := by
  simp [signedNumerator, signedMagnitude, signedRatWire]

theorem signedDenominator_signedRatWire (q : Rat) :
    signedDenominator (signedRatWire q) = q.den.bits := by
  simp [signedDenominator, signedMagnitude, signedRatWire]

theorem signedRatWire_value (q : Rat) :
    signedRatValue (signedRatWire q) = q := by
  by_cases hq : q < 0
  · have hn : (q.num.natAbs : Rat) = -(q.num : Rat) := by
      have hnum : q.num < 0 := Rat.num_neg.mpr hq
      have hz : (Int.ofNat q.num.natAbs : Int) = -q.num := by
        exact Int.ofNat_natAbs_of_nonpos hnum.le
      have hz' := congrArg (fun z : Int => (z : Rat)) hz
      norm_num at hz' ⊢
      exact hz'
    simp [signedRatValue, signedRatWire, signedSign, signedNumerator,
      signedDenominator, signedMagnitude, hq, hn, Rat.num_div_den,
      bitValue_bits]
  · have hq0 : 0 ≤ q := le_of_not_gt hq
    have hn : (q.num.natAbs : Rat) = (q.num : Rat) := by
      have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
      have hz : (Int.ofNat q.num.natAbs : Int) = q.num :=
        Int.natAbs_of_nonneg hnum
      have hz' := congrArg (fun z : Int => (z : Rat)) hz
      norm_num at hz' ⊢
      exact hz'
    simp [signedRatValue, signedRatWire, signedSign, signedNumerator,
      signedDenominator, signedMagnitude, hq, hn, Rat.num_div_den,
      bitValue_bits]

theorem signedRatTreeWire_of_rat (q : Rat) :
    signedRatTreeWire (CMMSACodec.Tree.encode (signedTree q)) =
      signedRatWire q := by
  by_cases hq : q < 0
  · simp only [signedRatTreeWire, signedRatWire, signedTree, hq,
      nodeLeftTag_of_node, nodeRightTag_of_node, pairFst_pair, pairSnd_pair,
      ratTree]
    rw [natBitsTag_of_nat, natBitsTag_of_nat]
    simp [dropOne, CMMSACodec.Tree.encode, hq]
  · simp only [signedRatTreeWire, signedRatWire, signedTree, hq,
      nodeLeftTag_of_node, nodeRightTag_of_node, pairFst_pair, pairSnd_pair,
      ratTree]
    rw [natBitsTag_of_nat, natBitsTag_of_nat]
    simp [dropOne, CMMSACodec.Tree.encode, hq]

theorem signedRatTreeWire_of_readSignedTag
    (t : CMMSACodec.Tree) (q : Rat)
    (h : ExecutablePipelineInput.readSigned t = some q) :
    signedRatTreeWire
        (dropOne (readSignedTag (CMMSACodec.Tree.encode t))) =
      signedRatWire q := by
  rw [readSignedTag_of_tree t, h]
  change signedRatTreeWire (CMMSACodec.Tree.encode (signedTree q)) = _
  exact signedRatTreeWire_of_rat q

theorem signedSign_mem_FP : signedSign ∈ FP := by
  change pairFst ∈ FP
  exact Cobham.fstBlock_mem_FP

theorem signedMagnitude_mem_FP : signedMagnitude ∈ FP := by
  change pairSnd ∈ FP
  exact Cobham.sndBlock_mem_FP

theorem signedNumerator_mem_FP : signedNumerator ∈ FP := by
  change (fun z : Bits => pairFst (pairSnd z)) ∈ FP
  exact mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP

theorem signedDenominator_mem_FP : signedDenominator ∈ FP := by
  change (fun z : Bits => pairSnd (pairSnd z)) ∈ FP
  exact mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP

def signedRatPack (z : Bits) : Bits :=
  pair (pairFst z) (pair (pairFst (pairSnd z)) (pairSnd (pairSnd z)))

theorem signedRatPack_mem_FP : signedRatPack ∈ FP := by
  change (fun z : Bits =>
    pair (pairFst z) (pair (pairFst (pairSnd z)) (pairSnd (pairSnd z)))) ∈ FP
  have hs := Cobham.fstBlock_mem_FP
  have hm := Cobham.sndBlock_mem_FP
  have hmn := mem_FP_comp hm Cobham.fstBlock_mem_FP
  have hmd := mem_FP_comp hm Cobham.sndBlock_mem_FP
  have hp := Cobham.pairFn_mem_FP hmn hmd
  exact Cobham.pairFn_mem_FP hs hp

theorem signedRatPack_on_pair (s n d : Bits) :
    signedRatPack (pair s (pair n d)) = pair s (pair n d) := by
  simp [signedRatPack]

def signedZero : Bits := pair [false] (pair [] [true])

theorem signedZero_value : signedRatValue signedZero = 0 := by
  norm_num [signedZero, signedRatValue, signedSign, signedNumerator,
    signedDenominator, signedMagnitude, bitValue]

private theorem eqFlag_false_of_ne {a b : Bits} (h : a ≠ b) :
    Cobham.eqFlag a b = [false] := by
  have hf := Cobham.eqFlag_flag a b
  cases hf with
  | inl ht => exact (h ((Cobham.eqFlag_eq_true_iff a b).mp ht)).elim
  | inr hf => exact hf

private theorem mulCanonPair_bits (a b : Nat) :
    mulCanonPair (pair a.bits b.bits) = (a * b).bits := by
  rw [mulCanonPair_eq_bits]
  simp only [bitValue_bits, pairFst_pair, pairSnd_pair]

private theorem mulCanonPair_bits_zero_left (b : Nat) :
    mulCanonPair (pair (0 : Nat).bits b.bits) = [] := by
  rw [mulCanonPair_bits]
  simp

def signedSignXor (z : Bits) : Bits :=
  Cobham.selectHead (signedSign (pairFst z))
    (Cobham.selectHead (signedSign (pairSnd z)) [false] [true])
    (Cobham.selectHead (signedSign (pairSnd z)) [true] [false])

theorem signedSignXor_mem_FP : signedSignXor ∈ FP := by
  have hs : (fun z : Bits => signedSign (pairFst z)) ∈ FP := by
    change (signedSign ∘ pairFst) ∈ FP
    exact mem_FP_comp Cobham.fstBlock_mem_FP signedSign_mem_FP
  have hright := mem_FP_comp Cobham.sndBlock_mem_FP signedSign_mem_FP
  have hinner := Cobham.selectHeadFn_mem_FP hright
    (constFn_mem_FP [false]) (constFn_mem_FP [true])
  have houter := Cobham.selectHeadFn_mem_FP hs
    hinner (Cobham.selectHeadFn_mem_FP hright
      (constFn_mem_FP [true]) (constFn_mem_FP [false]))
  exact houter

theorem signedSignXor_true_iff (a b : Bits)
    (ha : signedSign a = [false] ∨ signedSign a = [true])
    (hb : signedSign b = [false] ∨ signedSign b = [true]) :
    signedSignXor (pair a b) = [true] ↔
      (signedSign a = [true]) ≠ (signedSign b = [true]) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp only [signedSignXor, pairFst_pair, pairSnd_pair]
  all_goals rw [ha, hb]
  all_goals simp [Cobham.selectHead]

def signedRatMul (z : Bits) : Bits :=
  let a := pairFst z
  let b := pairSnd z
  let n := mulCanonPair (pair (signedNumerator a) (signedNumerator b))
  let d := mulCanonPair (pair (signedDenominator a) (signedDenominator b))
  Cobham.selectHead (Cobham.eqFlag n []) signedZero
    (pair (signedSignXor z) (pair n d))

private theorem signedRatMul_pair_false
    (sa na da sb nb db : Bits)
    (h : Cobham.eqFlag (mulCanonPair (pair na nb)) [] = [false]) :
    signedRatMul (pair (pair sa (pair na da)) (pair sb (pair nb db))) =
      pair (signedSignXor (pair (pair sa (pair na da)) (pair sb (pair nb db))))
        (pair (mulCanonPair (pair na nb)) (mulCanonPair (pair da db))) := by
  unfold signedRatMul
  simp only [signedNumerator, signedDenominator, signedMagnitude,
    pairFst_pair, pairSnd_pair]
  rw [h]
  rfl

private theorem signedRatMul_pair_true
    (sa na da sb nb db : Bits)
    (h : Cobham.eqFlag (mulCanonPair (pair na nb)) [] = [true]) :
    signedRatMul (pair (pair sa (pair na da)) (pair sb (pair nb db))) =
      signedZero := by
  unfold signedRatMul
  simp only [signedNumerator, signedDenominator, signedMagnitude,
    pairFst_pair, pairSnd_pair]
  rw [h]
  rfl

set_option maxHeartbeats 800000 in
theorem signedRatMul_mem_FP : signedRatMul ∈ FP := by
  unfold signedRatMul
  have hfn : (fun z : Bits => signedNumerator (pairFst z)) ∈ FP := by
    change (signedNumerator ∘ pairFst) ∈ FP
    exact mem_FP_comp Cobham.fstBlock_mem_FP signedNumerator_mem_FP
  have hsn : (fun z : Bits => signedNumerator (pairSnd z)) ∈ FP := by
    change (signedNumerator ∘ pairSnd) ∈ FP
    exact mem_FP_comp Cobham.sndBlock_mem_FP signedNumerator_mem_FP
  have hfd : (fun z : Bits => signedDenominator (pairFst z)) ∈ FP := by
    change (signedDenominator ∘ pairFst) ∈ FP
    exact mem_FP_comp Cobham.fstBlock_mem_FP signedDenominator_mem_FP
  have hsd : (fun z : Bits => signedDenominator (pairSnd z)) ∈ FP := by
    change (signedDenominator ∘ pairSnd) ∈ FP
    exact mem_FP_comp Cobham.sndBlock_mem_FP signedDenominator_mem_FP
  have hn : (fun z : Bits =>
      mulCanonPair (pair (signedNumerator (pairFst z))
        (signedNumerator (pairSnd z)))) ∈ FP := by
    exact mulCanonPair_comp_mem_FP (Cobham.pairFn_mem_FP hfn hsn)
  have hd : (fun z : Bits =>
      mulCanonPair (pair (signedDenominator (pairFst z))
        (signedDenominator (pairSnd z)))) ∈ FP := by
    exact mulCanonPair_comp_mem_FP (Cobham.pairFn_mem_FP hfd hsd)
  have hpack : (fun z : Bits =>
      pair (signedSignXor z) (pair
        (mulCanonPair (pair (signedNumerator (pairFst z))
          (signedNumerator (pairSnd z))))
        (mulCanonPair (pair (signedDenominator (pairFst z))
          (signedDenominator (pairSnd z)))))) ∈ FP := by
    exact Cobham.pairFn_mem_FP signedSignXor_mem_FP
      (Cobham.pairFn_mem_FP hn hd)
  have heq := eqFlagFn_mem_FP hn (constFn_mem_FP [])
  exact Cobham.selectHeadFn_mem_FP heq
    (constFn_mem_FP signedZero) hpack

def signedRatDiv (z : Bits) : Bits :=
  let a := pairFst z
  let b := pairSnd z
  let n := mulCanonPair (pair (signedNumerator a) (signedDenominator b))
  let d := mulCanonPair (pair (signedDenominator a) (signedNumerator b))
  Cobham.selectHead (Cobham.eqFlag (signedNumerator b) []) signedZero
    (Cobham.selectHead (Cobham.eqFlag n []) signedZero
      (pair (signedSignXor z) (pair n d)))

private theorem signedRatDiv_pair_zero
    (sa na da sb nb db : Bits)
    (h : Cobham.eqFlag nb [] = [true]) :
    signedRatDiv (pair (pair sa (pair na da)) (pair sb (pair nb db))) =
      signedZero := by
  unfold signedRatDiv
  simp only [signedNumerator, signedDenominator, signedMagnitude,
    pairFst_pair, pairSnd_pair]
  rw [h]
  rfl

private theorem signedRatDiv_pair_false
    (sa na da sb nb db : Bits)
    (hn : Cobham.eqFlag (mulCanonPair (pair na db)) [] = [false])
    (hb : Cobham.eqFlag nb [] = [false]) :
    signedRatDiv (pair (pair sa (pair na da)) (pair sb (pair nb db))) =
      pair (signedSignXor (pair (pair sa (pair na da)) (pair sb (pair nb db))))
        (pair (mulCanonPair (pair na db)) (mulCanonPair (pair da nb))) := by
  unfold signedRatDiv
  simp only [signedNumerator, signedDenominator, signedMagnitude,
    pairFst_pair, pairSnd_pair]
  rw [hb, hn]
  rfl

private theorem signedRatDiv_pair_num_zero
    (sa na da sb nb db : Bits)
    (hn : Cobham.eqFlag (mulCanonPair (pair na db)) [] = [true])
    (hb : Cobham.eqFlag nb [] = [false]) :
    signedRatDiv (pair (pair sa (pair na da)) (pair sb (pair nb db))) =
      signedZero := by
  unfold signedRatDiv
  simp only [signedNumerator, signedDenominator, signedMagnitude,
    pairFst_pair, pairSnd_pair]
  rw [hb, hn]
  rfl

set_option maxHeartbeats 800000 in
theorem signedRatDiv_mem_FP : signedRatDiv ∈ FP := by
  unfold signedRatDiv
  have hfn : (fun z : Bits => signedNumerator (pairFst z)) ∈ FP := by
    change (signedNumerator ∘ pairFst) ∈ FP
    exact mem_FP_comp Cobham.fstBlock_mem_FP signedNumerator_mem_FP
  have hsn : (fun z : Bits => signedNumerator (pairSnd z)) ∈ FP := by
    change (signedNumerator ∘ pairSnd) ∈ FP
    exact mem_FP_comp Cobham.sndBlock_mem_FP signedNumerator_mem_FP
  have hfd : (fun z : Bits => signedDenominator (pairFst z)) ∈ FP := by
    change (signedDenominator ∘ pairFst) ∈ FP
    exact mem_FP_comp Cobham.fstBlock_mem_FP signedDenominator_mem_FP
  have hsd : (fun z : Bits => signedDenominator (pairSnd z)) ∈ FP := by
    change (signedDenominator ∘ pairSnd) ∈ FP
    exact mem_FP_comp Cobham.sndBlock_mem_FP signedDenominator_mem_FP
  have hna : (fun z : Bits =>
      mulCanonPair (pair (signedNumerator (pairFst z))
        (signedDenominator (pairSnd z)))) ∈ FP := by
    exact mulCanonPair_comp_mem_FP (Cobham.pairFn_mem_FP hfn hsd)
  have hda : (fun z : Bits =>
      mulCanonPair (pair (signedDenominator (pairFst z))
        (signedNumerator (pairSnd z)))) ∈ FP := by
    exact mulCanonPair_comp_mem_FP (Cobham.pairFn_mem_FP hfd hsn)
  have hpack : (fun z : Bits =>
      pair (signedSignXor z) (pair
        (mulCanonPair (pair (signedNumerator (pairFst z))
          (signedDenominator (pairSnd z))))
        (mulCanonPair (pair (signedDenominator (pairFst z))
          (signedNumerator (pairSnd z)))))) ∈ FP := by
    exact Cobham.pairFn_mem_FP signedSignXor_mem_FP
      (Cobham.pairFn_mem_FP hna hda)
  have hn := eqFlagFn_mem_FP hna (constFn_mem_FP [])
  have hz := eqFlagFn_mem_FP hsn (constFn_mem_FP [])
  have hinner := Cobham.selectHeadFn_mem_FP hn
    (constFn_mem_FP signedZero) hpack
  have hout := Cobham.selectHeadFn_mem_FP hz
    (constFn_mem_FP signedZero) hinner
  exact hout

/- Old expanded semantic proof retained as design notes while the packed
   semantic proof below is factored through canonical wire-shape lemmas.
set_option maxHeartbeats 800000 in
theorem signedRatMul_value_old (q r : Rat) :
    signedRatValue (signedRatMul (pair (signedRatWire q) (signedRatWire r))) =
      q * r := by
  by_cases hq0 : q = 0
  · have hnum : q.num.natAbs = 0 := by
      rw [hq0]
      simp
    have hmul : signedRatMul
        (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
      have hf : Cobham.eqFlag
          (mulCanonPair (pair q.num.natAbs.bits r.num.natAbs.bits)) [] = [true] := by
        rw [show q.num.natAbs = 0 by exact hnum, mulCanonPair_bits_zero_left]
        exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      change signedRatMul
        (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))) = signedZero
      exact signedRatMul_pair_true _ _ _ _ _ _ hf
    rw [hmul, signedZero_value]
    simp [hq0]
  by_cases hr0 : r = 0
  · have hnum : r.num.natAbs = 0 := by
      rw [hr0]
      simp
    have hmul : signedRatMul
        (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
      have hf : Cobham.eqFlag
          (mulCanonPair (pair q.num.natAbs.bits r.num.natAbs.bits)) [] = [true] := by
        rw [show r.num.natAbs = 0 by exact hnum]
        rw [show mulCanonPair (pair q.num.natAbs.bits (0 : Nat).bits) = [] by
          rw [mulCanonPair_eq_bits]
          simp [bitValue_bits, bitValue]]
        exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
      change signedRatMul
        (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))) = signedZero
      exact signedRatMul_pair_true _ _ _ _ _ _ hf
    rw [hmul, signedZero_value]
    simp [hr0]
  by_cases hq : q < 0 <;> by_cases hr : r < 0
  all_goals
    have hnpos : 0 < q.num.natAbs * r.num.natAbs := by
      have hqn : 0 < q.num.natAbs := by
        exact Nat.pos_of_ne_zero (by
          intro hz
          apply hq0
          apply Rat.num_eq_zero.mp
          exact Int.natAbs_eq_zero.mp hz)
      have hrn : 0 < r.num.natAbs := by
        exact Nat.pos_of_ne_zero (by
          intro hz
          apply hr0
          apply Rat.num_eq_zero.mp
          exact Int.natAbs_eq_zero.mp hz)
      exact Nat.mul_pos hqn hrn
    have heq : Cobham.eqFlag (q.num.natAbs * r.num.natAbs).bits [] = [false] := by
      apply eqFlag_false_of_ne
      intro hz
      have hv := congrArg bitValue hz
      have : q.num.natAbs * r.num.natAbs = 0 := by
        simpa [bitValue_bits, bitValue] using hv
      exact Nat.ne_of_gt hnpos this
    have hmul : signedRatMul
        (pair (signedRatWire q) (signedRatWire r)) =
        pair (signedSignXor (pair (signedRatWire q) (signedRatWire r)))
          (pair (q.num.natAbs * r.num.natAbs).bits
            (q.den * r.den).bits) := by
      have hf : Cobham.eqFlag
          (mulCanonPair (pair q.num.natAbs.bits r.num.natAbs.bits)) [] = [false] := by
        rw [mulCanonPair_bits]
        exact heq
      change signedRatMul
        (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))) =
        pair (signedSignXor (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))))
          (pair (q.num.natAbs * r.num.natAbs).bits
            (q.den * r.den).bits)
      exact signedRatMul_pair_false
        (if q < 0 then [true] else [false]) q.num.natAbs.bits q.den.bits
        (if r < 0 then [true] else [false]) r.num.natAbs.bits r.den.bits hf
    have hqf : q =
        (if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) /
          (q.den : Rat) := by
      simpa [signedRatValue, signedRatWire, signedSign, signedNumerator,
        signedDenominator, signedMagnitude, hq, bitValue_bits] using
        (signedRatWire_value q).symm
    have hrf : r =
        (if r < 0 then -((r.num.natAbs : Rat)) else (r.num.natAbs : Rat)) /
          (r.den : Rat) := by
      simpa [signedRatValue, signedRatWire, signedSign, signedNumerator,
        signedDenominator, signedMagnitude, hr, bitValue_bits] using
        (signedRatWire_value r).symm
    rw [hmul]
    simp only [signedRatValue, signedSign, signedNumerator,
      signedDenominator, signedMagnitude, pairFst_pair, pairSnd_pair,
      bitValue_bits]
    have hsign : signedSignXor
        (pair (signedRatWire q) (signedRatWire r)) =
        (if q < 0 then if r < 0 then [false] else [true]
         else if r < 0 then [true] else [false]) := by
      simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead]
    rw [hsign]
    simp only [if_pos hq, if_neg hr]
    have hqf' := hqf
    have hrf' := hrf
    simp only [if_pos hq] at hqf'
    simp only [if_neg hr] at hrf'
    rw [← hqf', ← hrf']
    field_simp
    ring
-/

private theorem signedRatWire_fraction (q : Rat) :
    (if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) /
        (q.den : Rat) = q := by
  simpa [signedRatValue, signedRatWire, signedSign, signedNumerator,
    signedDenominator, signedMagnitude, bitValue_bits] using
    signedRatWire_value q

private theorem signedRatMul_shape (q r : Rat)
    (hprod : q.num.natAbs * r.num.natAbs ≠ 0) :
    signedRatValue (signedRatMul (pair (signedRatWire q) (signedRatWire r))) =
      (if signedSignXor (pair (signedRatWire q) (signedRatWire r)) = [true] then
          -((q.num.natAbs * r.num.natAbs : Nat) : Rat)
        else ((q.num.natAbs * r.num.natAbs : Nat) : Rat)) /
        ((q.den * r.den : Nat) : Rat) := by
  have heq : Cobham.eqFlag (q.num.natAbs * r.num.natAbs).bits [] = [false] := by
    apply eqFlag_false_of_ne
    intro hz
    have hv := congrArg bitValue hz
    have hz0 : q.num.natAbs * r.num.natAbs = 0 := by
      simpa [bitValue_bits, bitValue] using hv
    exact hprod hz0
  have hf : Cobham.eqFlag
      (mulCanonPair (pair q.num.natAbs.bits r.num.natAbs.bits)) [] = [false] := by
    rw [mulCanonPair_bits]
    exact heq
  have hmul := signedRatMul_pair_false
    (if q < 0 then [true] else [false]) q.num.natAbs.bits q.den.bits
    (if r < 0 then [true] else [false]) r.num.natAbs.bits r.den.bits hf
  change signedRatMul (pair (signedRatWire q) (signedRatWire r)) = _ at hmul
  rw [hmul]
  simp only [signedRatValue, signedSign, signedNumerator,
    signedDenominator, signedMagnitude, pairFst_pair, pairSnd_pair,
    bitValue_bits, mulCanonPair_bitValue, signedRatWire]
  rfl

private theorem signedProductNumerator_sign (q r : Rat) :
    (if signedSignXor (pair (signedRatWire q) (signedRatWire r)) = [true] then
        -((q.num.natAbs * r.num.natAbs : Nat) : Rat)
      else ((q.num.natAbs * r.num.natAbs : Nat) : Rat)) =
      (if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) *
        (if r < 0 then -((r.num.natAbs : Rat)) else (r.num.natAbs : Rat)) := by
  by_cases hq : q < 0
  · by_cases hr : r < 0
    · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
    · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
  · by_cases hr : r < 0
    · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
    · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]

private theorem rat_mul_nat_fraction (a b : Rat) (da db : Nat)
    (hda : (da : Rat) ≠ 0) (hdb : (db : Rat) ≠ 0) :
    (a * b) / ((da * db : Nat) : Rat) =
      (a / (da : Rat)) * (b / (db : Rat)) := by
  field_simp [hda, hdb]
  push_cast
  ring

private theorem signedRatMul_zero_left (q r : Rat) (hq : q = 0) :
    signedRatMul (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
  have hn : q.num.natAbs = 0 := by rw [hq]; simp
  have hf : Cobham.eqFlag
      (mulCanonPair (pair q.num.natAbs.bits r.num.natAbs.bits)) [] = [true] := by
    rw [show q.num.natAbs = 0 by exact hn, mulCanonPair_bits_zero_left]
    exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  change signedRatMul
    (pair (pair (if q < 0 then [true] else [false])
      (pair q.num.natAbs.bits q.den.bits))
      (pair (if r < 0 then [true] else [false])
        (pair r.num.natAbs.bits r.den.bits))) = signedZero
  exact signedRatMul_pair_true _ _ _ _ _ _ hf

private theorem signedRatMul_zero_right (q r : Rat) (hr : r = 0) :
    signedRatMul (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
  have hn : r.num.natAbs = 0 := by rw [hr]; simp
  have hf : Cobham.eqFlag
      (mulCanonPair (pair q.num.natAbs.bits r.num.natAbs.bits)) [] = [true] := by
    rw [show r.num.natAbs = 0 by exact hn]
    rw [show mulCanonPair (pair q.num.natAbs.bits (0 : Nat).bits) = [] by
      rw [mulCanonPair_eq_bits]
      simp [bitValue_bits, bitValue]]
    exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  change signedRatMul
    (pair (pair (if q < 0 then [true] else [false])
      (pair q.num.natAbs.bits q.den.bits))
      (pair (if r < 0 then [true] else [false])
        (pair r.num.natAbs.bits r.den.bits))) = signedZero
  exact signedRatMul_pair_true _ _ _ _ _ _ hf

theorem signedRatMul_value (q r : Rat) :
    signedRatValue (signedRatMul (pair (signedRatWire q) (signedRatWire r))) =
      q * r := by
  by_cases hq0 : q = 0
  · rw [signedRatMul_zero_left q r hq0, signedZero_value]
    simp [hq0]
  by_cases hr0 : r = 0
  · rw [signedRatMul_zero_right q r hr0, signedZero_value]
    simp [hr0]
  have hprod : q.num.natAbs * r.num.natAbs ≠ 0 := by
    exact Nat.mul_ne_zero (by
      intro h; exact hq0 (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))) (by
      intro h; exact hr0 (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h)))
  rw [signedRatMul_shape q r hprod, signedProductNumerator_sign q r]
  rw [rat_mul_nat_fraction
    (if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat))
    (if r < 0 then -((r.num.natAbs : Rat)) else (r.num.natAbs : Rat))
    q.den r.den (Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt r.den_pos))]
  rw [signedRatWire_fraction q, signedRatWire_fraction r]

/- Old expanded division semantic proof.
set_option maxHeartbeats 800000 in
theorem signedRatDiv_value_old (q r : Rat) :
    signedRatValue (signedRatDiv (pair (signedRatWire q) (signedRatWire r))) =
      q / r := by
  by_cases hr0 : r = 0
  · have hnum : r.num.natAbs = 0 := by
      rw [hr0]
      simp
    have hf : Cobham.eqFlag r.num.natAbs.bits [] = [true] := by
      rw [show r.num.natAbs = 0 by exact hnum]
      exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
    have hdiv : signedRatDiv
        (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
      change signedRatDiv
        (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))) = signedZero
      exact signedRatDiv_pair_zero _ _ _ _ _ _ hf
    rw [hdiv, signedZero_value]
    simp [hr0]
  by_cases hq0 : q = 0
  · have hnum : q.num.natAbs = 0 := by
      rw [hq0]
      simp
    have hrnum : r.num.natAbs ≠ 0 := by
      intro hz
      apply hr0
      apply Rat.num_eq_zero.mp
      exact Int.natAbs_eq_zero.mp hz
    have hnb : Cobham.eqFlag r.num.natAbs.bits [] = [false] := by
      apply eqFlag_false_of_ne
      intro hz
      have hv := congrArg bitValue hz
      have : r.num.natAbs = 0 := by simpa [bitValue_bits, bitValue] using hv
      exact hrnum this
    have hf : Cobham.eqFlag
        (mulCanonPair (pair q.num.natAbs.bits r.den.bits)) [] = [true] := by
      rw [show q.num.natAbs = 0 by exact hnum,
        mulCanonPair_bits_zero_left]
      exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
    have hdiv : signedRatDiv
        (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
      change signedRatDiv
        (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))) = signedZero
      exact signedRatDiv_pair_num_zero _ _ _ _ _ _ hf hnb
    rw [hdiv, signedZero_value]
    simp [hq0]
  by_cases hq : q < 0 <;> by_cases hr : r < 0
  all_goals
    have hqn : 0 < q.num.natAbs := by
      exact Nat.pos_of_ne_zero (by
        intro hz
        apply hq0
        apply Rat.num_eq_zero.mp
        exact Int.natAbs_eq_zero.mp hz)
    have hrn : 0 < r.num.natAbs := by
      exact Nat.pos_of_ne_zero (by
        intro hz
        apply hr0
        apply Rat.num_eq_zero.mp
        exact Int.natAbs_eq_zero.mp hz)
    have hnb : Cobham.eqFlag r.num.natAbs.bits [] = [false] := by
      apply eqFlag_false_of_ne
      intro hz
      have hv := congrArg bitValue hz
      have : r.num.natAbs = 0 := by simpa [bitValue_bits, bitValue] using hv
      exact Nat.ne_of_gt hrn this
    have hnpos : 0 < q.num.natAbs * r.den :=
      Nat.mul_pos hqn r.den_pos
    have hn : Cobham.eqFlag
        (mulCanonPair (pair q.num.natAbs.bits r.den.bits)) [] = [false] := by
      apply eqFlag_false_of_ne
      intro hz
      have hv := congrArg bitValue hz
      have hz0 : q.num.natAbs * r.den = 0 := by
        simpa [mulCanonPair_eq_bits, bitValue_bits, bitValue] using hv
      exact Nat.ne_of_gt hnpos hz0
    have hdiv : signedRatDiv
        (pair (signedRatWire q) (signedRatWire r)) =
        pair (signedSignXor (pair (signedRatWire q) (signedRatWire r)))
          (pair (q.num.natAbs * r.den).bits
            (q.den * r.num.natAbs).bits) := by
      change signedRatDiv
        (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))) =
        pair (signedSignXor (pair (pair (if q < 0 then [true] else [false])
          (pair q.num.natAbs.bits q.den.bits))
          (pair (if r < 0 then [true] else [false])
            (pair r.num.natAbs.bits r.den.bits))))
          (pair (q.num.natAbs * r.den).bits
            (q.den * r.num.natAbs).bits)
      exact signedRatDiv_pair_false
        (if q < 0 then [true] else [false]) q.num.natAbs.bits q.den.bits
        (if r < 0 then [true] else [false]) r.num.natAbs.bits r.den.bits hn hnb
    have hqf : q =
        (if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) /
          (q.den : Rat) := by
      simpa [signedRatValue, signedRatWire, signedSign, signedNumerator,
        signedDenominator, signedMagnitude, hq, bitValue_bits] using
        (signedRatWire_value q).symm
    have hrf : r =
        (if r < 0 then -((r.num.natAbs : Rat)) else (r.num.natAbs : Rat)) /
          (r.den : Rat) := by
      simpa [signedRatValue, signedRatWire, signedSign, signedNumerator,
        signedDenominator, signedMagnitude, hr, bitValue_bits] using
        (signedRatWire_value r).symm
    rw [hdiv]
    simp only [signedRatValue, signedSign, signedNumerator,
      signedDenominator, signedMagnitude, pairFst_pair, pairSnd_pair,
      bitValue_bits]
    have hsign : signedSignXor
        (pair (signedRatWire q) (signedRatWire r)) =
        (if q < 0 then if r < 0 then [false] else [true]
         else if r < 0 then [true] else [false]) := by
      simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead]
    rw [hsign]
    simp only [if_pos hq, if_neg hr]
    have hqf' := hqf
    have hrf' := hrf
    simp only [if_pos hq] at hqf'
    simp only [if_neg hr] at hrf'
    rw [← hqf', ← hrf']
    field_simp
    ring

-/

private theorem signedRatDiv_shape (q r : Rat)
    (hnum : q.num.natAbs * r.den ≠ 0)
    (hden : q.den * r.num.natAbs ≠ 0) :
    signedRatValue (signedRatDiv (pair (signedRatWire q) (signedRatWire r))) =
      (if signedSignXor (pair (signedRatWire q) (signedRatWire r)) = [true] then
          -((q.num.natAbs * r.den : Nat) : Rat)
        else ((q.num.natAbs * r.den : Nat) : Rat)) /
        ((q.den * r.num.natAbs : Nat) : Rat) := by
  have hbn : Cobham.eqFlag r.num.natAbs.bits [] = [false] := by
    apply eqFlag_false_of_ne
    intro hz
    have hv := congrArg bitValue hz
    have hz0 : r.num.natAbs = 0 := by simpa [bitValue_bits, bitValue] using hv
    exact hden (by simp [hz0])
  have hnn : Cobham.eqFlag
      (mulCanonPair (pair q.num.natAbs.bits r.den.bits)) [] = [false] := by
    apply eqFlag_false_of_ne
    intro hz
    have hv := congrArg bitValue hz
    have hz0 : q.num.natAbs * r.den = 0 := by
      simpa [mulCanonPair_eq_bits, bitValue_bits, bitValue] using hv
    exact hnum hz0
  have hdiv := signedRatDiv_pair_false
    (if q < 0 then [true] else [false]) q.num.natAbs.bits q.den.bits
    (if r < 0 then [true] else [false]) r.num.natAbs.bits r.den.bits hnn hbn
  change signedRatDiv (pair (signedRatWire q) (signedRatWire r)) = _ at hdiv
  rw [hdiv]
  simp only [signedRatValue, signedSign, signedNumerator,
    signedDenominator, signedMagnitude, pairFst_pair, pairSnd_pair,
    bitValue_bits]
  simp only [mulCanonPair_bitValue, signedRatWire]
  simp only [pairFst_pair, pairSnd_pair, bitValue_bits]
  rfl

private theorem rat_div_nat_fraction (a b : Rat) (da db : Nat)
    (hb : b ≠ 0) (hda : (da : Rat) ≠ 0) (hdb : (db : Rat) ≠ 0) :
    (a * (db : Rat)) / ((da * b : Rat)) =
      (a / (da : Rat)) / (b / (db : Rat)) := by
  field_simp [hb, hda, hdb]

private theorem signedRatDiv_zero_right (q r : Rat) (hr : r = 0) :
    signedRatDiv (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
  have hn : r.num.natAbs = 0 := by rw [hr]; simp
  have hf : Cobham.eqFlag r.num.natAbs.bits [] = [true] := by
    rw [show r.num.natAbs = 0 by exact hn]
    exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  change signedRatDiv
    (pair (pair (if q < 0 then [true] else [false])
      (pair q.num.natAbs.bits q.den.bits))
      (pair (if r < 0 then [true] else [false])
        (pair r.num.natAbs.bits r.den.bits))) = signedZero
  exact signedRatDiv_pair_zero _ _ _ _ _ _ hf

private theorem signedRatDiv_zero_left (q r : Rat) (hq : q = 0) (hr : r ≠ 0) :
    signedRatDiv (pair (signedRatWire q) (signedRatWire r)) = signedZero := by
  have hn : q.num.natAbs = 0 := by rw [hq]; simp
  have hrn : r.num.natAbs ≠ 0 := by
    intro h
    exact hr (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))
  have hb : Cobham.eqFlag r.num.natAbs.bits [] = [false] := by
    apply eqFlag_false_of_ne
    intro hz
    have hv := congrArg bitValue hz
    have hz0 : r.num.natAbs = 0 := by simpa [bitValue_bits, bitValue] using hv
    exact hrn hz0
  have hf : Cobham.eqFlag
      (mulCanonPair (pair q.num.natAbs.bits r.den.bits)) [] = [true] := by
    rw [show q.num.natAbs = 0 by exact hn, mulCanonPair_bits_zero_left]
    exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  change signedRatDiv
    (pair (pair (if q < 0 then [true] else [false])
      (pair q.num.natAbs.bits q.den.bits))
      (pair (if r < 0 then [true] else [false])
        (pair r.num.natAbs.bits r.den.bits))) = signedZero
  exact signedRatDiv_pair_num_zero _ _ _ _ _ _ hf hb

private theorem rat_div_signed_fraction (q r : Rat)
    (hq : q.num.natAbs ≠ 0) (hr : r.num.natAbs ≠ 0) :
    ((if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) *
      (if r < 0 then -((r.den : Rat)) else (r.den : Rat))) /
        ((q.den : Rat) * (r.num.natAbs : Rat)) =
      ((if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) /
        (q.den : Rat)) /
      ((if r < 0 then -((r.num.natAbs : Rat)) else (r.num.natAbs : Rat)) /
        (r.den : Rat)) := by
  by_cases hq' : q < 0
  · by_cases hr' : r < 0
    · simp only [if_pos hq', if_pos hr']
      field_simp [hq, hr, Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos),
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt r.den_pos)]
    · simp only [if_pos hq', if_neg hr']
      field_simp [hq, hr, Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos),
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt r.den_pos)]
  · by_cases hr' : r < 0
    · simp only [if_neg hq', if_pos hr']
      field_simp [hq, hr, Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos),
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt r.den_pos)]
    · simp only [if_neg hq', if_neg hr']
      field_simp [hq, hr, Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos),
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt r.den_pos)]

theorem signedRatDiv_value (q r : Rat) :
    signedRatValue (signedRatDiv (pair (signedRatWire q) (signedRatWire r))) =
      q / r := by
  by_cases hr0 : r = 0
  · rw [signedRatDiv_zero_right q r hr0, signedZero_value]
    simp [hr0]
  by_cases hq0 : q = 0
  · rw [signedRatDiv_zero_left q r hq0 hr0, signedZero_value]
    simp [hq0]
  have hqn : q.num.natAbs ≠ 0 := by
    intro h; exact hq0 (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))
  have hrn : r.num.natAbs ≠ 0 := by
    intro h; exact hr0 (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))
  have hshape := signedRatDiv_shape q r
    (Nat.mul_ne_zero hqn (Nat.ne_of_gt r.den_pos))
    (Nat.mul_ne_zero (Nat.ne_of_gt q.den_pos) hrn)
  rw [hshape]
  have hsign :
      (if signedSignXor (pair (signedRatWire q) (signedRatWire r)) = [true] then
          -((q.num.natAbs * r.den : Nat) : Rat)
        else ((q.num.natAbs * r.den : Nat) : Rat)) =
      (if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) *
        (if r < 0 then -((r.den : Rat)) else (r.den : Rat)) := by
    by_cases hq : q < 0
    · by_cases hr : r < 0
      · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
      · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
    · by_cases hr : r < 0
      · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
      · simp [signedSignXor, signedSign, signedRatWire, Cobham.selectHead, hq, hr]
  rw [hsign]
  calc
    _ =
        ((if q < 0 then -((q.num.natAbs : Rat)) else (q.num.natAbs : Rat)) /
          (q.den : Rat)) /
        ((if r < 0 then -((r.num.natAbs : Rat)) else (r.num.natAbs : Rat)) /
          (r.den : Rat)) := by
      convert (rat_div_signed_fraction q r hqn hrn) using 1 <;>
        push_cast <;> ring
    _ = q / r := by rw [signedRatWire_fraction q, signedRatWire_fraction r]

end PvNP.RealizableHardness.ActualSelectedCmmsaSignedRatFP
