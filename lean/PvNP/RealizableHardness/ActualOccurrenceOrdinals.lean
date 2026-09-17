import PvNP.RealizableHardness.ActualOccurrenceAllocation

/-! Source-only semantic prerequisite for the encoded occurrence scanner.
The recursive scan is executable; no encoded FP claim is made by this module. -/
namespace PvNP.RealizableHardness.ActualOccurrenceOrdinals
open ActualOccurrenceAllocation
set_option autoImplicit false

/-- Scan left to right, stopping before the first target slot. Count only matches. -/
def scanBefore {A : Type*} [DecidableEq A] (keep : A -> Bool) (target : A) : List A -> Nat
  | [] => 0
  | a :: tail => if a = target then 0 else
      (if keep a then 1 else 0) + scanBefore keep target tail

/-- This describes precisely which preceding slots are counted, including absent targets. -/
theorem scanBefore_eq_prefix_count {A : Type*} [DecidableEq A]
    (keep : A -> Bool) (target : A) (l : List A) :
    scanBefore keep target l = (l.takeWhile (fun a => a != target)).countP keep := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    by_cases h : a = target
    · subst a
      simp [scanBefore]
    · cases hk : keep a <;> simp [scanBefore, h, hk, ih, Nat.add_comm]

/-- Filtering preserves the target's prefix count whenever the target is retained. -/
theorem scanBefore_eq_filtered_idxOf {A : Type*} [DecidableEq A]
    (keep : A -> Bool) (target : A) (ht : keep target = true) (l : List A) :
    scanBefore keep target l = (l.filter keep).idxOf target := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    by_cases h : a = target
    · subst a
      simp [scanBefore, ht]
    · cases hk : keep a <;> simp [scanBefore, h, hk, ih, Nat.add_comm]

/-- Direct computation from the explicit ordered source triples and the queried slot.
No occurrence equivalence or complexity certificate is supplied as input. -/
def scanOrdinal {N m : Nat} (vars : Fin m -> Fin 3 -> Fin N) (o : Slot m) : Nat :=
  scanBefore (fun a : Slot m => decide (vars a.1 a.2 = vars o.1 o.2)) o (slotList m)

theorem scanOrdinal_eq_prefix_count {N m : Nat}
    (vars : Fin m -> Fin 3 -> Fin N) (o : Slot m) :
    scanOrdinal vars o = ((slotList m).takeWhile (fun a => a != o)).countP
      (fun a => decide (vars a.1 a.2 = vars o.1 o.2)) := by
  simpa only [scanOrdinal, bne_eq, Bool.beq_eq_decide_eq] using
    (scanBefore_eq_prefix_count
      (fun a : Slot m => decide (vars a.1 a.2 = vars o.1 o.2)) o (slotList m))

/-- The existing getEquiv-based canonical ordinal is exactly this executable scan. -/
theorem scanOrdinal_eq_ordinal {N m : Nat} (I : Instance N m) (o : Slot m) :
    scanOrdinal I.vars o = (I.ordinal (I.owner o) (Subtype.mk o rfl)).val := by
  rw [scanOrdinal, scanBefore_eq_filtered_idxOf _ _ (by simp)]
  rfl

/-- A valid slot's scan result fits the actual occurrence cloud, strictly. -/
theorem scanOrdinal_lt_size {N m : Nat} (I : Instance N m) (o : Slot m) :
    scanOrdinal I.vars o < I.size (I.owner o) := by
  rw [scanOrdinal_eq_ordinal]
  exact (I.ordinal (I.owner o) (Subtype.mk o rfl)).isLt

theorem scanBefore_le_length {A : Type*} [DecidableEq A]
    (keep : A -> Bool) (target : A) (l : List A) :
    scanBefore keep target l <= l.length := by
  induction l with
  | nil => simp [scanBefore]
  | cons a tail ih =>
    by_cases h : a = target
    · simp [scanBefore, h]
    · cases hk : keep a <;> simp only [scanBefore, ite_eq_right h, hk, List.length_cons] <;>
        simp_all <;> omega

/-- An output-size bound for the direct unary answer, not an FP runtime claim. -/
def unaryAnswer {N m : Nat} (vars : Fin m -> Fin 3 -> Fin N) (o : Slot m) : List Bool :=
  List.replicate (scanOrdinal vars o) true

theorem scanOrdinal_le_slots {N m : Nat} (vars : Fin m -> Fin 3 -> Fin N) (o : Slot m) :
    scanOrdinal vars o <= 3*m := by
  have h := scanBefore_le_length
    (fun a : Slot m => decide (vars a.1 a.2 = vars o.1 o.2)) o (slotList m)
  simpa [scanOrdinal, slotList, List.product, Nat.mul_comm] using h

theorem unaryAnswer_length_le {N m : Nat} (vars : Fin m -> Fin 3 -> Fin N) (o : Slot m) :
    (unaryAnswer vars o).length <= 3*m := by
  simpa [unaryAnswer] using scanOrdinal_le_slots vars o

end PvNP.RealizableHardness.ActualOccurrenceOrdinals
