import PvNP.RealizableHardness.ActualSourceFirstOccurrence

/-! Source-only draft, conditional on the uncompiled FirstOccurrence dependency.
Actual compact-source to unary normalized-table producer. No finite Allocation
bridge or upstream hardness result is asserted. -/
namespace PvNP.RealizableHardness.ActualSourceNormalizedTable
open Complexity ActualSourceNormalization ActualCompactSourceLookup
open ActualSourceFirstOccurrence
set_option autoImplicit false
noncomputable section

abbrev UnaryTriple := Prod (List Bool) (Prod (List Bool) (List Bool))

def unaryTriple (t : BinaryTriple) : UnaryTriple :=
  (List.replicate t.1 true, List.replicate t.2.1 true, List.replicate t.2.2 true)

def unaryRows (S : Source) : List UnaryTriple := (normalize S).1.map unaryTriple

def unarySource (S : Source) : Prod (List UnaryTriple) (List Bool) :=
  (unaryRows S, S.2)

theorem unaryRows_length (S : Source) : (unaryRows S).length = S.1.length := by
  simp [unaryRows, ActualSourceNormalization.normalize]

/-- Machine pair of table and exact all-true mixed-radix occurrence counter. -/
def slotArg (i : Nat) (z : List Bool) : List Bool :=
  pair (pairFst z) (marks (mulC 3 (pairSnd z) ++ List.replicate i true))

theorem slotArg_mem_FP (i : Nat) : Membership.mem FP (slotArg i) := by
  exact Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (marks_mem_FP (Cobham.appendFn_mem_FP
      (mulC_mem_FP Cobham.sndBlock_mem_FP 3)
      (constFn_mem_FP (List.replicate i true))))

theorem slotArg_correct (T : List Bool) (r i : Nat) :
    slotArg i (pair T (List.replicate r true)) = lookupInput T (3*r+i) := by
  simp [slotArg, lookupInput, marks_eq, Nat.mul_comm]

def renamedField (i : Nat) (z : List Bool) : List Bool := firstFn (slotArg i z)

theorem renamedField_mem_FP (i : Nat) : Membership.mem FP (renamedField i) := by
  unfold renamedField
  simpa only [Function.comp_def] using
    mem_FP_comp (slotArg_mem_FP i) firstFn_mem_FP

theorem renamedField_correct (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    renamedField i.val (pair (table S) (List.replicate r.val true)) =
      List.replicate (first S (tripleLabel S.1[r.val] i)) true := by
  rw [renamedField, slotArg_correct]
  exact firstFn_correct S r i

def rowRule (z : List Bool) : List Bool :=
  encTriple (renamedField 0 z) (renamedField 1 z) (renamedField 2 z)

theorem rowRule_mem_FP : Membership.mem FP rowRule :=
  encTriple_mem_FP (renamedField_mem_FP 0) (renamedField_mem_FP 1)
    (renamedField_mem_FP 2)

theorem rowRule_correct (S : Source) (r : Fin S.1.length) :
    rowRule (pair (table S) (List.replicate r.val true)) =
      DataEncode.bitstringEncode (unaryTriple (renameTriple S S.1[r.val])) := by
  unfold rowRule
  have h0 : renamedField 0 (pair (table S) (List.replicate r.val true)) =
      List.replicate (first S S.1[r.val].1) true :=
    renamedField_correct S r (Fin.mk 0 (by decide))
  have h1 : renamedField 1 (pair (table S) (List.replicate r.val true)) =
      List.replicate (first S S.1[r.val].2.1) true :=
    renamedField_correct S r (Fin.mk 1 (by decide))
  have h2 : renamedField 2 (pair (table S) (List.replicate r.val true)) =
      List.replicate (first S S.1[r.val].2.2) true :=
    renamedField_correct S r (Fin.mk 2 (by decide))
  rw [h0, h1, h2]
  exact encTriple_eq _ _ _

/-- The actual library list loop, clocked by the supplied table's row count. -/
def tableFn (T : List Bool) : List Bool := listEncFn rowRule (pair (posCount T) T)

theorem tableFn_mem_FP : Membership.mem FP tableFn := by
  unfold tableFn
  have ha := Cobham.pairFn_mem_FP (posCount_mem_FP id_mem_FP) id_mem_FP
  simpa only [Function.comp_def, id_eq] using
    mem_FP_comp ha (materialize_mem_FP rowRule_mem_FP)

theorem tableFn_correct (S : Source) :
    tableFn (table S) = DataEncode.bitstringEncode (unaryRows S) := by
  unfold tableFn
  have hc : posCount (table S) = List.replicate (unaryRows S).length true := by
    rw [unaryRows_length]
    exact posCount_eq S.1
  rw [hc]
  apply materialize_eq (unaryRows S) (table S)
  intro i hi
  have hr : i < S.1.length := by simpa only [unaryRows_length] using hi
  simpa [unaryRows, ActualSourceNormalization.normalize] using rowRule_correct S (Fin.mk i hr)

/-- DATA pairing, intentionally different from the machine argument pair. -/
def dataPair (a b : List Bool) : List Bool := false :: (a ++ b) ++ [true]

theorem dataPair_mem_FP {a b : List Bool -> List Bool}
    (ha : Membership.mem FP a) (hb : Membership.mem FP b) :
    Membership.mem FP (fun z => dataPair (a z) (b z)) := by
  have hc := mem_FP_comp (Cobham.appendFn_mem_FP ha hb) (Cobham.cons_mem_FP false)
  exact mem_FP_of_eq (Cobham.appendFn_mem_FP hc (constFn_mem_FP [true]))
    (fun _ => rfl)

def sourceFn (z : List Bool) : List Bool :=
  dataPair (tableFn (tableFromWire z)) (sndEnc z)

theorem sourceFn_mem_FP : Membership.mem FP sourceFn := by
  have ht : Membership.mem FP (fun z => tableFn (tableFromWire z)) := by
    simpa only [Function.comp_def] using mem_FP_comp tableFromWire_mem_FP tableFn_mem_FP
  exact dataPair_mem_FP ht (sndEnc_mem_FP id_mem_FP)

/-- Complete output identity, including the original encoded RHS and row order. -/
theorem sourceFn_correct (S : Source) :
    sourceFn (wire S) = DataEncode.bitstringEncode (unarySource S) := by
  rw [sourceFn, tableFromWire_correct, tableFn_correct]
  have hr : sndEnc (wire S) = DataEncode.bitstringEncode S.2 := sndEnc_eq S.1 S.2
  rw [hr]
  exact (bitstringEncode_prod_eq (unaryRows S) S.2).symm

theorem sourceFn_rhs (S : Source) :
    sndEnc (sourceFn (wire S)) = DataEncode.bitstringEncode S.2 := by
  rw [sourceFn_correct]
  exact sndEnc_eq (unaryRows S) S.2

theorem sourceFn_table (S : Source) :
    fstEnc (sourceFn (wire S)) = DataEncode.bitstringEncode (unaryRows S) := by
  rw [sourceFn_correct]
  exact fstEnc_eq (unaryRows S) S.2

theorem sourceFn_length (S : Source) :
    (sourceFn (wire S)).length = (tableFn (table S)).length +
      (DataEncode.bitstringEncode S.2).length + 2 := by
  rw [sourceFn, tableFromWire_correct]
  have hr : sndEnc (wire S) = DataEncode.bitstringEncode S.2 := sndEnc_eq S.1 S.2
  rw [hr]
  simp [dataPair] <;> omega

/-- This is the library's genuine polynomial output bound for the same raw
producer, not an assumed runtime field or an inference from a size estimate. -/
theorem sourceFn_output_polynomial :
    Exists (fun p : Polynomial Nat => forall z : List Bool,
      (sourceFn z).length <= p.eval z.length) :=
  Cobham.output_length_poly_of_mem_FP sourceFn_mem_FP

private theorem sum_map_bound {A : Type} (l : List A) (f : A -> Nat) (K : Nat)
    (h : forall a, a ∈ l -> f a <= K) : (l.map f).sum <= l.length*K := by
  revert h
  induction l with
  | nil => intro h; simp
  | cons a l ih =>
    intro h
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem unaryTriple_length (t : BinaryTriple) :
    (DataEncode.bitstringEncode (unaryTriple t)).length =
      4*t.1+4*t.2.1+4*t.2.2+10 := by
  rw [unaryTriple, <- encTriple_eq]
  exact length_encTriple _ _ _

theorem tableFn_length_bound (S : Source) :
    (tableFn (table S)).length <= 2+S.1.length*(36*S.1.length+10) := by
  rw [tableFn_correct, length_bitstringEncode_list]
  have hb : forall t, t ∈ S.1 ->
      (DataEncode.bitstringEncode (unaryTriple (renameTriple S t))).length <=
        36*S.1.length+10 := by
    intro t ht
    have h := normalized_label_bound ht
    rw [unaryTriple_length]
    omega
  have hs := sum_map_bound S.1
    (fun t => (DataEncode.bitstringEncode (unaryTriple (renameTriple S t))).length)
    (36*S.1.length+10) hb
  simpa only [unaryRows, ActualSourceNormalization.normalize, List.map_map, Function.comp_def] using Nat.add_le_add_left hs 2

theorem sourceFn_length_bound (S : Source) :
    (sourceFn (wire S)).length <= 4+S.1.length*(36*S.1.length+10)+
      (DataEncode.bitstringEncode S.2).length := by
  rw [sourceFn_length]
  have h := tableFn_length_bound S
  omega

theorem unarySource_empty : unarySource ([], []) = ([], []) := rfl

theorem unarySource_rhs (S : Source) : (unarySource S).2 = S.2 := rfl

end
end PvNP.RealizableHardness.ActualSourceNormalizedTable
