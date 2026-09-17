import PvNP.RealizableHardness.ActualOccurrenceOrdinals

/-! Source-only exact mixed-radix «prefix» of the actual occurrence slot list.
No encoded FP or runtime assertion is made here. -/
namespace PvNP.RealizableHardness.ActualOccurrencePrefix
open ActualOccurrenceAllocation ActualOccurrenceOrdinals
set_option autoImplicit false

def rank {m : Nat} (o : Slot m) : Nat := o.1.val * 3 + o.2.val

theorem rank_lt {m : Nat} (o : Slot m) : rank o < m*3 := by
  have hr := o.1.isLt
  have hi := o.2.isLt
  unfold rank
  omega

def decode {m : Nat} (q : Fin (m*3)) : Slot m :=
  (Fin.mk (q.val / 3) (by have h := q.isLt; omega),
   Fin.mk (q.val % 3) (by omega))

theorem rank_decode {m : Nat} (q : Fin (m*3)) : rank (decode q) = q.val := by
  change q.val / 3 * 3 + q.val % 3 = q.val
  omega

theorem rank_injective {m : Nat} : Function.Injective (@rank m) := by
  intro a b h
  have ha := a.2.isLt
  have hb := b.2.isLt
  unfold rank at h
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem decode_rank {m : Nat} (o : Slot m) : decode (Fin.mk (rank o) (rank_lt o)) = o := by
  apply rank_injective
  exact rank_decode _

theorem decode_injective {m : Nat} : Function.Injective (@decode m) := by
  intro a b h
  apply Fin.ext
  simpa only [rank_decode] using congrArg rank h

private theorem finRange_map_value {A : Type} (n : Nat) (f : Nat -> A) :
    (List.finRange n).map (fun v => f v.val) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

private theorem finRange_flatMap_value {A : Type} (n : Nat) (f : Nat -> List A) :
    (List.finRange n).flatMap (fun v => f v.val) = (List.range n).flatMap f :=
  congrArg List.flatten (finRange_map_value n f)

private theorem range_mul_map {A : Type} (n k : Nat) (f : Nat -> A) :
    (List.range (n*k)).map f = (List.range n).flatMap fun v =>
      (List.range k).map fun j => f (v*k+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ,
      List.flatMap_append]
    simp [List.map_map]

theorem map_rank_slotList (m : Nat) : (slotList m).map rank = List.range (m*3) := by
  simp only [slotList, List.product, List.map_flatMap, List.map_map,
    Function.comp_def, rank]
  simp_rw [finRange_map_value]
  rw [finRange_flatMap_value m (fun v => (List.range 3).map (fun j => v*3+j))]
  simpa using (range_mul_map m 3 id).symm

/-- Full actual enumeration, with label fastest and source row slowest. -/
theorem slotList_eq_decode (m : Nat) :
    slotList m = (List.finRange (m*3)).map decode := by
  apply (List.map_injective_iff.mpr rank_injective)
  rw [map_rank_slotList, List.map_map]
  simp only [Function.comp_def, rank_decode]
  simp

private theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    [BEq A] [LawfulBEq A] [BEq B] [LawfulBEq B]
    (f : A -> B) (hf : Function.Injective f) (a : A) (l : List A) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons b tail ih =>
    by_cases h : b = a
    · subst b
      simp
    · simp [h, hf.eq_iff, ih]

theorem slotList_idxOf {m : Nat} (o : Slot m) : (slotList m).idxOf o = rank o := by
  rw [slotList_eq_decode]
  conv_lhs => arg 1; rw [<- decode_rank o]
  rw [idxOf_map_injective decode decode_injective]
  simp

private theorem takeWhile_ne_eq_take_idxOf {A : Type*} [DecidableEq A] [BEq A] [LawfulBEq A]
    (a : A) (l : List A) :
    l.takeWhile (fun b => b != a) = l.take (l.idxOf a) := by
  induction l with
  | nil => rfl
  | cons b tail ih =>
    by_cases h : b = a
    · subst b
      simp
    · simp [h, ih]

/-- The concrete query clock agrees with the actual stop-before-slot «prefix». -/
theorem slotList_prefix_take {m : Nat} (o : Slot m) :
    (slotList m).takeWhile (fun a => a != o) = (slotList m).take (rank o) := by
  have h := takeWhile_ne_eq_take_idxOf o (slotList m)
  rw [slotList_idxOf] at h
  simpa only [bne_eq, Bool.beq_eq_decide_eq] using h

/-- Increasing q, with its actual quotient/remainder slots. -/
def «prefix» {m : Nat} (o : Slot m) : List (Slot m) :=
  (List.finRange (rank o)).map (fun q =>
    decode (Fin.mk q.val (Nat.lt_trans q.isLt (rank_lt o))))

/-- Exact list equality, not membership, cardinality, permutation or endpoint deduplication. -/
theorem prefix_eq_actual {m : Nat} (o : Slot m) :
    «prefix» o = (slotList m).takeWhile (fun a => a != o) := by
  rw [slotList_prefix_take, slotList_eq_decode]
  unfold «prefix»
  rw [<- List.map_take]
  apply List.ext_getElem
  · simp [Nat.min_eq_left (Nat.le_of_lt (rank_lt o))]
  · intro i hi hj
    simp

theorem prefix_length {m : Nat} (o : Slot m) : («prefix» o).length = rank o := by
  simp [«prefix»]

theorem prefix_nodup {m : Nat} (o : Slot m) : («prefix» o).Nodup := by
  rw [prefix_eq_actual, slotList_prefix_take]
  exact (slotList_nodup m).take

/-- Same-owner count for the exact numeric «prefix» equals the accepted canonical scan. -/
theorem prefix_count_eq_scanOrdinal {N m : Nat}
    (vars : Fin m -> Fin 3 -> Fin N) (o : Slot m) :
    («prefix» o).countP (fun a => decide (vars a.1 a.2 = vars o.1 o.2)) =
      scanOrdinal vars o := by
  rw [prefix_eq_actual]
  exact (scanOrdinal_eq_prefix_count vars o).symm

theorem prefix_count_eq_ordinal {N m : Nat} (I : Instance N m) (o : Slot m) :
    («prefix» o).countP (fun a => decide (I.vars a.1 a.2 = I.vars o.1 o.2)) =
      (I.ordinal (I.owner o) (Subtype.mk o rfl)).val := by
  rw [prefix_count_eq_scanOrdinal, scanOrdinal_eq_ordinal]

end PvNP.RealizableHardness.ActualOccurrencePrefix
