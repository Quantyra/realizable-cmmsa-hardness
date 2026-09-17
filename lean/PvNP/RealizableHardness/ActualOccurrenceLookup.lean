import PvNP.RealizableHardness.ActualOccurrenceAllocation
import Complexitylib.Classes.PCP.Internal.Materialize

/-! Source-only lookup on the exact serialized ordered unary source triples.
The same total bitstring function has an FP proof script. No ordinal scan,
source hardness, or whole-constructor FP statement is asserted. -/
namespace PvNP.RealizableHardness.ActualOccurrenceLookup
open Complexity ActualOccurrenceAllocation
set_option autoImplicit false
noncomputable section

abbrev UnaryTriple := Prod (List Bool) (Prod (List Bool) (List Bool))

def sourceTriples {N m : Nat} (I : Instance N m) : List UnaryTriple :=
  List.ofFn (fun r => (List.replicate (I.vars r 0).val true,
    List.replicate (I.vars r 1).val true, List.replicate (I.vars r 2).val true))

def serializedSource {N m : Nat} (I : Instance N m) : List Bool :=
  DataEncode.bitstringEncode (sourceTriples I)

def lookupInput (table : List Bool) (q : Nat) : List Bool :=
  pair table (List.replicate q true)

/-- Total raw-bitstring rule; correctness below assumes an actual serialized table. -/
def ownerLookup (z : List Bool) : List Bool :=
  ifEqLen (modC 3 (pairSnd z)) []
    (recFst (pairFst z) (divC 3 (pairSnd z)).length)
    (ifEqLen (modC 3 (pairSnd z)) [true]
      (recSnd (pairFst z) (divC 3 (pairSnd z)).length)
      (recThd (pairFst z) (divC 3 (pairSnd z)).length))

theorem ownerLookup_mem_FP : Membership.mem FP ownerLookup := by
  have hq : Membership.mem FP (fun z : List Bool => pairSnd z) := Cobham.sndBlock_mem_FP
  have ht : Membership.mem FP (fun z : List Bool => pairFst z) := Cobham.fstBlock_mem_FP
  have hd := divC_mem_FP hq 3
  have hm := modC_mem_FP hq 3
  exact ifEqLen_mem_FP hm (constFn_mem_FP []) (recFst_mem_FP hd ht)
    (ifEqLen_mem_FP hm (constFn_mem_FP [true]) (recSnd_mem_FP hd ht)
      (recThd_mem_FP hd ht))

theorem sourceTriples_length {N m : Nat} (I : Instance N m) :
    (sourceTriples I).length = m := by simp [sourceTriples]

theorem sourceTriples_get {N m : Nat} (I : Instance N m) (r : Fin m) :
    (sourceTriples I)[r.val]'(by rw [sourceTriples_length]; exact r.isLt) =
      (List.replicate (I.vars r 0).val true,
        List.replicate (I.vars r 1).val true, List.replicate (I.vars r 2).val true) := by
  simp [sourceTriples]

theorem recFst_source {N m : Nat} (I : Instance N m) (r : Fin m) :
    recFst (serializedSource I) r.val = List.replicate (I.vars r 0).val true :=
  recFst_eq (by rw [sourceTriples_length]; exact r.isLt) (sourceTriples_get I r)

theorem recSnd_source {N m : Nat} (I : Instance N m) (r : Fin m) :
    recSnd (serializedSource I) r.val = List.replicate (I.vars r 1).val true :=
  recSnd_eq (by rw [sourceTriples_length]; exact r.isLt) (sourceTriples_get I r)

theorem recThd_source {N m : Nat} (I : Instance N m) (r : Fin m) :
    recThd (serializedSource I) r.val = List.replicate (I.vars r 2).val true :=
  recThd_eq (by rw [sourceTriples_length]; exact r.isLt) (sourceTriples_get I r)

theorem ownerLookup_dispatch (table : List Bool) (r : Nat) (i : Fin 3) :
    ownerLookup (lookupInput table (3*r+i.val)) =
      if i.val = 0 then recFst table r
      else if i.val = 1 then recSnd table r else recThd table r := by
  have hi := i.isLt
  have hd : (3*r+i.val)/3 = r := by omega
  have hm : (3*r+i.val)%3 = i.val := by omega
  simp only [ownerLookup, lookupInput, pairSnd_pair, pairFst_pair,
    divC_eq (c := 3) (by decide), modC_eq (c := 3) (by decide), List.length_replicate, hd, hm]
  fin_cases i <;> simp [ifEqLen_pos, ifEqLen_neg]

/-- This is the same ownerLookup as in ownerLookup_mem_FP, on the actual wire. -/
theorem ownerLookup_correct {N m : Nat} (I : Instance N m) (o : Slot m) :
    ownerLookup (lookupInput (serializedSource I) (3*o.1.val+o.2.val)) =
      List.replicate (I.owner o).val true := by
  cases o with
  | mk r i =>
    rw [ownerLookup_dispatch]
    fin_cases i <;> simp [Instance.owner, recFst_source, recSnd_source, recThd_source]

theorem ownerLookup_length {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ownerLookup (lookupInput (serializedSource I) (3*o.1.val+o.2.val))).length =
      (I.owner o).val := by rw [ownerLookup_correct, List.length_replicate]

theorem ownerLookup_length_lt {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ownerLookup (lookupInput (serializedSource I) (3*o.1.val+o.2.val))).length < N := by
  rw [ownerLookup_length]
  exact (I.owner o).isLt

theorem lookupInput_length (table : List Bool) (q : Nat) :
    (lookupInput table q).length = 2*table.length+2+q := by
  simp [lookupInput]

theorem slotCounter_lt {m : Nat} (o : Slot m) : 3*o.1.val+o.2.val < 3*m := by
  have hr := o.1.isLt
  have hi := o.2.isLt
  omega

theorem validInput_length_le {N m : Nat} (I : Instance N m) (o : Slot m) :
    (lookupInput (serializedSource I) (3*o.1.val+o.2.val)).length <=
      2*(serializedSource I).length+2+3*m := by
  rw [lookupInput_length]
  have h := slotCounter_lt o
  omega

theorem sourceTriples_empty {N : Nat} (I : Instance N 0) : sourceTriples I = [] := by
  simp [sourceTriples]

end
end PvNP.RealizableHardness.ActualOccurrenceLookup
