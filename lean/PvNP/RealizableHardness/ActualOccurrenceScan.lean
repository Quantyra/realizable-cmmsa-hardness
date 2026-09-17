import PvNP.RealizableHardness.ActualOccurrenceLookup
import PvNP.RealizableHardness.ActualOccurrencePrefix

/-! Uncompiled source: exact unary-wire ordinal scanner. No table-producer FP,
compact-label normalization, or whole-reduction runtime is asserted. -/
namespace PvNP.RealizableHardness.ActualOccurrenceScan
open Complexity ActualOccurrenceAllocation ActualOccurrenceLookup ActualOccurrencePrefix
open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-- w carries the original lookup wire as payload and the current unary loop index. -/
def sameOwnerMark (w : List Bool) : List Bool :=
  ifEqLen (ownerLookup (pair (pairFst (pairFst w)) (pairSnd w)))
    (ownerLookup (pairFst w)) [true] []

/-- Input remains precisely pair(table, unary query); count only earlier slots. -/
def ordinalScan (z : List Bool) : List Bool :=
  countOver sameOwnerMark (pair (pairSnd z) z)

theorem sameOwnerMark_mem_FP : Membership.mem FP sameOwnerMark := by
  unfold sameOwnerMark
  have hf : Membership.mem FP (fun w : List Bool => pairFst w) := Cobham.fstBlock_mem_FP
  have hs : Membership.mem FP (fun w : List Bool => pairSnd w) := Cobham.sndBlock_mem_FP
  have hff : Membership.mem FP (fun w : List Bool => pairFst (pairFst w)) :=
    by simpa only [Function.comp_def] using (mem_FP_comp hf hf)
  have hi : Membership.mem FP (fun w : List Bool => pair (pairFst (pairFst w)) (pairSnd w)) :=
    Cobham.pairFn_mem_FP hff hs
  have ha : Membership.mem FP (fun w : List Bool =>
      ownerLookup (pair (pairFst (pairFst w)) (pairSnd w))) :=
    by simpa only [Function.comp_def] using (mem_FP_comp hi ownerLookup_mem_FP)
  have hb : Membership.mem FP (fun w : List Bool => ownerLookup (pairFst w)) :=
    by simpa only [Function.comp_def] using (mem_FP_comp hf ownerLookup_mem_FP)
  exact ifEqLen_mem_FP ha hb (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem ordinalScan_mem_FP : Membership.mem FP ordinalScan := by
  unfold ordinalScan
  have harg := Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP id_mem_FP
  simpa only [Function.comp_def, id_eq] using
    (mem_FP_comp harg (countOver_mem_FP sameOwnerMark_mem_FP))

theorem ownerLookup_rank {N m : Nat} (I : Instance N m) (o : Slot m) :
    ownerLookup (lookupInput (serializedSource I) (rank o)) =
      List.replicate (I.owner o).val true := by
  simpa [rank, Nat.mul_comm] using ownerLookup_correct I o

theorem sameOwnerMark_correct {N m : Nat} (I : Instance N m) (o a : Slot m) :
    sameOwnerMark (pair (lookupInput (serializedSource I) (rank o))
      (List.replicate (rank a) true)) =
        if I.owner a = I.owner o then [true] else [] := by
  simp only [sameOwnerMark, pairFst_pair, pairSnd_pair, lookupInput]
  change ifEqLen (ownerLookup (lookupInput (serializedSource I) (rank a)))
    (ownerLookup (lookupInput (serializedSource I) (rank o))) [true] [] = _
  rw [ownerLookup_rank, ownerLookup_rank]
  by_cases h : I.owner a = I.owner o
  · rw [if_pos h]
    apply ifEqLen_pos
    simp [h]
  · rw [if_neg h]
    apply ifEqLen_neg
    simp only [List.length_replicate]
    intro he
    exact h (Fin.ext he)

theorem sameOwnerMark_length {N m : Nat} (I : Instance N m) (o a : Slot m) :
    (sameOwnerMark (pair (lookupInput (serializedSource I) (rank o))
      (List.replicate (rank a) true))).length =
        if I.owner a = I.owner o then 1 else 0 := by
  rw [sameOwnerMark_correct]
  split_ifs <;> rfl

private theorem countP_as_sum {A : Type*} (p : A → Bool) (l : List A) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]

/-- The loop sum is the exact mixed-radix prefix list's same-owner count. -/
theorem ordinalScan_length_eq_prefix {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ordinalScan (lookupInput (serializedSource I) (rank o))).length =
      («prefix» o).countP (fun a => decide (I.owner a = I.owner o)) := by
  unfold ordinalScan
  have hq : pairSnd (lookupInput (serializedSource I) (rank o)) =
      List.replicate (rank o) true := by simp [lookupInput]
  rw [hq, length_countOver, Finset.sum_range]
  rw [countP_as_sum]
  unfold «prefix»
  rw [List.map_map, ← Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro q _
  let a : Slot m := decode (Fin.mk q.val (Nat.lt_trans q.isLt (rank_lt o)))
  have ha : rank a = q.val := rank_decode _
  have h := sameOwnerMark_length I o a
  rw [ha] at h
  simpa only [Function.comp_def, decide_eq_true_eq] using h

theorem ordinalScan_length_eq_ordinal {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ordinalScan (lookupInput (serializedSource I) (rank o))).length =
      (I.ordinal (I.owner o) (Subtype.mk o rfl)).val := by
  rw [ordinalScan_length_eq_prefix]
  exact prefix_count_eq_ordinal I o

/-- Same raw function as ordinalScan_mem_FP, returning the canonical ordinal in unary. -/
theorem ordinalScan_correct {N m : Nat} (I : Instance N m) (o : Slot m) :
    ordinalScan (lookupInput (serializedSource I) (rank o)) =
      List.replicate (I.ordinal (I.owner o) (Subtype.mk o rfl)).val true := by
  calc
    _ = List.replicate (ordinalScan (lookupInput (serializedSource I) (rank o))).length true :=
      countOver_eq_replicate _ _
    _ = _ := by rw [ordinalScan_length_eq_ordinal]

theorem ordinalScan_length_lt_size {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ordinalScan (lookupInput (serializedSource I) (rank o))).length < I.size (I.owner o) := by
  rw [ordinalScan_length_eq_ordinal]
  exact (I.ordinal (I.owner o) (Subtype.mk o rfl)).isLt

theorem ordinalScan_length_le_slots {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ordinalScan (lookupInput (serializedSource I) (rank o))).length ≤ 3*m := by
  rw [ordinalScan_length_eq_ordinal, ← ActualOccurrenceOrdinals.scanOrdinal_eq_ordinal]
  exact ActualOccurrenceOrdinals.scanOrdinal_le_slots I.vars o

theorem scan_wire_length (table : List Bool) (q : Nat) :
    (lookupInput table q).length = 2*table.length+2+q := lookupInput_length table q

theorem scan_valid_wire_bound {N m : Nat} (I : Instance N m) (o : Slot m) :
    (lookupInput (serializedSource I) (rank o)).length ≤
      2*(serializedSource I).length+2+3*m := by
  simpa [rank, Nat.mul_comm] using validInput_length_le I o

/-- The internal countOver call adds one unary clock, with exact pairing overhead. -/
theorem countOver_wire_length (table : List Bool) (q : Nat) :
    (pair (pairSnd (lookupInput table q)) (lookupInput table q)).length =
      2*table.length+3*q+4 := by
  simp [lookupInput]
  omega

end
end PvNP.RealizableHardness.ActualOccurrenceScan
