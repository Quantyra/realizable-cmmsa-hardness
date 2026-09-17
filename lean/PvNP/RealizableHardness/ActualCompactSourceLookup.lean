import PvNP.RealizableHardness.ActualSourceNormalization
import Complexitylib.Classes.PCP.Internal.Materialize

/-! Uncompiled draft. Exact full-bitstring binary label extraction and its
same-function FP proof. This does not yet implement first-occurrence search or
materialize the normalized unary table. -/
namespace PvNP.RealizableHardness.ActualCompactSourceLookup
open Complexity ActualSourceNormalization
set_option autoImplicit false
noncomputable section

def table (S : Source) : List Bool := DataEncode.bitstringEncode S.1

def tableFromWire (z : List Bool) : List Bool := fstEnc z

theorem tableFromWire_mem_FP : Membership.mem FP tableFromWire :=
  fstEnc_mem_FP id_mem_FP

theorem tableFromWire_correct (S : Source) : tableFromWire (wire S) = table S :=
  fstEnc_eq S.1 S.2

def rowCount (z : List Bool) : List Bool := posCount (tableFromWire z)

theorem rowCount_mem_FP : Membership.mem FP rowCount :=
  posCount_mem_FP tableFromWire_mem_FP

theorem rowCount_correct (S : Source) : rowCount (wire S) = List.replicate S.1.length true := by
  rw [rowCount, tableFromWire_correct]
  exact posCount_eq S.1

def slotClock (z : List Bool) : List Bool := mulC 3 (rowCount z)

theorem slotClock_mem_FP : Membership.mem FP slotClock := mulC_mem_FP rowCount_mem_FP 3

theorem slotClock_length (S : Source) : (slotClock (wire S)).length = 3*S.1.length := by
  simp [slotClock, rowCount_correct, Nat.mul_comm]

def lookupInput (T : List Bool) (q : Nat) : List Bool := pair T (List.replicate q true)

/-- Keeps the full Nat serialization. No unaryOf occurs in this function. -/
def ownerLookup (z : List Bool) : List Bool :=
  let entry := posAt (pairFst z) (divC 3 (pairSnd z)).length
  ifEqLen (modC 3 (pairSnd z)) [] (fstEnc entry)
    (ifEqLen (modC 3 (pairSnd z)) [true]
      (fstEnc (sndEnc entry)) (sndEnc (sndEnc entry)))

theorem ownerLookup_mem_FP : Membership.mem FP ownerLookup := by
  have hd := divC_mem_FP Cobham.sndBlock_mem_FP 3
  have hm := modC_mem_FP Cobham.sndBlock_mem_FP 3
  have he := posAt_mem_FP hd Cobham.fstBlock_mem_FP
  exact ifEqLen_mem_FP hm (constFn_mem_FP []) (fstEnc_mem_FP he)
    (ifEqLen_mem_FP hm (constFn_mem_FP [true])
      (fstEnc_mem_FP (sndEnc_mem_FP he)) (sndEnc_mem_FP (sndEnc_mem_FP he)))

def tripleLabel (t : BinaryTriple) (i : Fin 3) : Nat :=
  if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2

theorem ownerLookup_dispatch (T : List Bool) (r : Nat) (i : Fin 3) :
    ownerLookup (lookupInput T (3*r+i.val)) =
      if i.val = 0 then fstEnc (posAt T r)
      else if i.val = 1 then fstEnc (sndEnc (posAt T r))
      else sndEnc (sndEnc (posAt T r)) := by
  have hi := i.isLt
  have hd : (3*r+i.val)/3 = r := by omega
  have hm : (3*r+i.val)%3 = i.val := by omega
  simp only [ownerLookup, lookupInput, pairFst_pair, pairSnd_pair,
    divC_eq (c := 3) (by decide), modC_eq (c := 3) (by decide),
    List.length_replicate, hd, hm]
  fin_cases i <;> simp [ifEqLen_pos, ifEqLen_neg]

/-- The output is the serialized label itself, not its numeric value in unary
and not the length of its binary representation. -/
theorem ownerLookup_correct (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    ownerLookup (lookupInput (table S) (3*r.val+i.val)) =
      DataEncode.bitstringEncode (tripleLabel S.1[r.val] i) := by
  rw [ownerLookup_dispatch]
  have he : posAt (table S) r.val = DataEncode.bitstringEncode S.1[r.val] :=
    posAt_eq_of_lt r.isLt
  rw [he]
  cases ht : S.1[r.val] with
  | mk a bc =>
    cases bc with
    | mk b c => fin_cases i <;> simp [tripleLabel, fstEnc_eq, sndEnc_eq]

theorem lookupInput_length (T : List Bool) (q : Nat) :
    (lookupInput T q).length = 2*T.length+2+q := by simp [lookupInput]

theorem slotCounter_lt (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    3*r.val+i.val < 3*S.1.length := by
  have hr := r.isLt
  have hi := i.isLt
  omega

theorem validInput_length_le (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    (lookupInput (table S) (3*r.val+i.val)).length <=
      2*(table S).length+2+3*S.1.length := by
  rw [lookupInput_length]
  have h := slotCounter_lt S r i
  omega

/-- Equality must become an empty/nonempty mark before bounded search:
[false] itself would incorrectly count as a hit. -/
def equalityMark (a b : List Bool) : List Bool :=
  Cobham.selectHead (Cobham.eqFlag a b) [true] []

theorem equalityMark_mem_FP {a b : List Bool -> List Bool}
    (ha : Membership.mem FP a) (hb : Membership.mem FP b) :
    Membership.mem FP (fun z => equalityMark (a z) (b z)) :=
  Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP ha hb)
    (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem equalityMark_correct (a b : List Bool) :
    equalityMark a b = if a = b then [true] else [] := by
  rcases Cobham.eqFlag_flag a b with he | he
  case inl =>
    have hab := (Cobham.eqFlag_eq_true_iff a b).mp he
    unfold equalityMark
    rw [he, if_pos hab]
    rfl
  case inr =>
    have hab : Not (a = b) := by
      intro hab
      have ht := (Cobham.eqFlag_eq_true_iff a b).mpr hab
      rw [he] at ht
      cases ht
    unfold equalityMark
    rw [he, if_neg hab]
    rfl

/-- Exact original-label equality, even for equal-length binary codes. -/
theorem equalityMark_encoded (v w : Nat) :
    equalityMark (DataEncode.bitstringEncode v) (DataEncode.bitstringEncode w) =
      if v = w then [true] else [] := by
  rw [equalityMark_correct]
  simp only [DataEncode.bitstringEncode_injective.eq_iff]

end
end PvNP.RealizableHardness.ActualCompactSourceLookup
