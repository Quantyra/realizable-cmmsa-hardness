import PvNP.RealizableHardness.ActualCompactSourceLookup

/-! Source-only draft: bounded search for the first occurrence of an original
binary label. This does not materialize the whole normalized source. -/
namespace PvNP.RealizableHardness.ActualSourceFirstOccurrence
open Complexity ActualSourceNormalization ActualCompactSourceLookup
set_option autoImplicit false
noncomputable section

/-- The table supplies the clock; marks changes bits, not its length. -/
def tableClock (T : List Bool) : List Bool := marks (mulC 3 (posCount T))

theorem tableClock_mem_FP : Membership.mem FP tableClock :=
  marks_mem_FP (mulC_mem_FP (posCount_mem_FP id_mem_FP) 3)

theorem tableClock_correct (S : Source) :
    tableClock (table S) = List.replicate (3*S.1.length) true := by
  simp [tableClock, table, posCount_eq, marks_eq, mulC, Nat.mul_comm]

/-- Input is pair (pair table queryLabelBits) candidateUnary. -/
def hit (w : List Bool) : List Bool :=
  equalityMark (ownerLookup (pair (pairFst (pairFst w)) (pairSnd w)))
    (pairSnd (pairFst w))

theorem hit_mem_FP : Membership.mem FP hit := by
  have hT : Membership.mem FP (fun w : List Bool => pairFst (pairFst w)) := by
    simpa only [Function.comp_def] using
      mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hlabel : Membership.mem FP (fun w : List Bool => pairSnd (pairFst w)) := by
    simpa only [Function.comp_def] using
      mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have harg := Cobham.pairFn_mem_FP hT Cobham.sndBlock_mem_FP
  have howner : Membership.mem FP (fun w : List Bool =>
      ownerLookup (pair (pairFst (pairFst w)) (pairSnd w))) := by
    simpa only [Function.comp_def] using mem_FP_comp harg ownerLookup_mem_FP
  exact equalityMark_mem_FP howner hlabel

/-- Same raw function used in the FP and correctness statements. -/
def firstFn (z : List Bool) : List Bool :=
  findFirst hit (pair (tableClock (pairFst z))
    (pair (pairFst z) (ownerLookup z)))

theorem firstFn_mem_FP : Membership.mem FP firstFn := by
  unfold firstFn
  have hc : Membership.mem FP (fun z : List Bool => tableClock (pairFst z)) := by
    simpa only [Function.comp_def] using
      mem_FP_comp Cobham.fstBlock_mem_FP tableClock_mem_FP
  have hp := Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP ownerLookup_mem_FP
  have ha := Cobham.pairFn_mem_FP hc hp
  simpa only [Function.comp_def] using
    mem_FP_comp ha (findFirst_mem_FP hit_mem_FP)

/-- Rows and columns belong to the normalization source, with repetitions. -/
def decodeRow (S : Source) (q : Fin (3*S.1.length)) : Fin S.1.length :=
  ⟨q.val / 3, by have h := q.isLt; omega⟩

def decodeCol (S : Source) (q : Fin (3*S.1.length)) : Fin 3 :=
  ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩

theorem rank_decode (S : Source) (q : Fin (3*S.1.length)) :
    3*(decodeRow S q).val + (decodeCol S q).val = q.val := by
  simp only [decodeRow, decodeCol]
  omega

theorem flatten_get_row (ts : List BinaryTriple) (r : Nat) (hr : r < ts.length)
    (i : Fin 3) :
    (ts.flatMap tripleLabels)[3*r+i.val]? = some (tripleLabel ts[r] i) := by
  induction ts generalizing r with
  | nil => simp at hr
  | cons t ts ih =>
    cases r with
    | zero => fin_cases i <;> simp [tripleLabels, tripleLabel]
    | succ r =>
      have hr' : r < ts.length := by simpa using hr
      have he : 3*(r+1)+i.val = (3*r+i.val)+3 := by omega
      change (t.1 :: t.2.1 :: t.2.2 :: ts.flatMap tripleLabels)[3*(r+1)+i.val]? =
        some (tripleLabel ts[r] i)
      rw [he]
      simpa only [List.getElem?_cons_succ] using ih r hr'

theorem ownerLookup_flatten (S : Source) (q : Fin (3*S.1.length)) :
    ownerLookup (lookupInput (table S) q.val) =
      DataEncode.bitstringEncode ((flatten S)[q.val]'(by
        rw [flatten_length]; exact q.isLt)) := by
  have hf := flatten_get_row S.1 (decodeRow S q).val (decodeRow S q).isLt
    (decodeCol S q)
  rw [rank_decode] at hf
  have hq : q.val < (flatten S).length := by rw [flatten_length]; exact q.isLt
  have hget : (flatten S)[q.val] =
      tripleLabel S.1[(decodeRow S q).val] (decodeCol S q) := by
    change (flatten S)[q.val]? = some _ at hf
    rw [List.getElem?_eq_getElem hq] at hf
    exact Option.some.inj hf
  rw [hget, ← rank_decode S q]
  exact ownerLookup_correct S (decodeRow S q) (decodeCol S q)

theorem hit_at (S : Source) (v : Nat) (q : Fin (3*S.1.length)) :
    hit (pair (pair (table S) (DataEncode.bitstringEncode v))
      (List.replicate q.val true)) =
      if (flatten S)[q.val]'(by rw [flatten_length]; exact q.isLt) = v
        then [true] else [] := by
  simp only [hit, pairFst_pair, pairSnd_pair]
  change equalityMark (ownerLookup (lookupInput (table S) q.val)) _ = _
  rw [ownerLookup_flatten, equalityMark_encoded]

/-- Minimality follows from idxOf itself; no first-correctness premise. -/
theorem no_earlier_label (S : Source) (v : Nat) (k : Nat)
    (hk : k < first S v) :
    (flatten S)[k]'(lt_of_lt_of_le hk List.idxOf_le_length) ≠ v := by
  have h := List.not_of_lt_findIdx (xs := flatten S) (p := fun a => a == v) hk
  simpa only [beq_eq_false_iff_ne] using h

theorem hit_first (S : Source) (v : Nat) (hv : v ∈ flatten S) :
    hit (pair (pair (table S) (DataEncode.bitstringEncode v))
      (List.replicate (first S v) true)) = [true] := by
  rw [hit_at S v ⟨first S v, first_lt hv⟩]
  have hg := get_first hv
  have hc : first S v < (flatten S).length := by
    rw [flatten_length]
    exact first_lt hv
  have he : (flatten S)[first S v] = v := by
    rw [List.getElem?_eq_getElem hc] at hg
    exact Option.some.inj hg
  simp only [he, if_true]

theorem hit_before_first (S : Source) (v : Nat) (hv : v ∈ flatten S)
    (k : Nat) (hk : k < first S v) :
    hit (pair (pair (table S) (DataEncode.bitstringEncode v))
      (List.replicate k true)) = [] := by
  rw [hit_at S v ⟨k, lt_trans hk (first_lt hv)⟩]
  exact if_neg (no_earlier_label S v k hk)

theorem search_correct (S : Source) (v : Nat) (hv : v ∈ flatten S) :
    findFirst hit (pair (tableClock (table S))
      (pair (table S) (DataEncode.bitstringEncode v))) =
        List.replicate (first S v) true := by
  rw [tableClock_correct]
  have hl : (findFirst hit (pair (List.replicate (3*S.1.length) true)
      (pair (table S) (DataEncode.bitstringEncode v)))).length = first S v := by
    apply length_findFirst_eq (first_lt hv)
    · rw [hit_first S v hv]; decide
    · intro k hk
      rw [hit_before_first S v hv k hk]; rfl
  conv_lhs => rw [findFirst_eq_replicate]
  rw [hl]

theorem firstFn_correct (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    firstFn (lookupInput (table S) (3*r.val+i.val)) =
      List.replicate (first S (tripleLabel S.1[r.val] i)) true := by
  have hv : tripleLabel S.1[r.val] i ∈ flatten S := by
    apply label_mem_flatten (List.getElem_mem r.isLt)
    fin_cases i <;> simp [tripleLabel, tripleLabels]
  unfold firstFn
  rw [ownerLookup_correct]
  simp only [lookupInput, pairFst_pair]
  exact search_correct S _ hv

theorem output_length_lt (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    (firstFn (lookupInput (table S) (3*r.val+i.val))).length < 3*S.1.length := by
  rw [firstFn_correct, List.length_replicate]
  apply first_lt
  apply label_mem_flatten (List.getElem_mem r.isLt)
  fin_cases i <;> simp [tripleLabel, tripleLabels]

theorem input_length_bound (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    (lookupInput (table S) (3*r.val+i.val)).length ≤
      2*(table S).length+2+3*S.1.length := validInput_length_le S r i

theorem search_wire_length (S : Source) (v : Nat) :
    (pair (tableClock (table S)) (pair (table S)
      (DataEncode.bitstringEncode v))).length =
      6*S.1.length+2*(table S).length+4+(DataEncode.bitstringEncode v).length := by
  simp [tableClock_correct]
  omega

end
end PvNP.RealizableHardness.ActualSourceFirstOccurrence
