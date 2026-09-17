import PvNP.RealizableHardness.ExecutablePortRotation

/-! SOURCE ONLY, uncompiled. Materializes the actual fixed port-cycle table,
including both endpoints of every dart, in the existing list encoding.
The imported rotation pair is author verified, pending independent review. -/
namespace PvNP.RealizableHardness.ExecutablePortTable
open Complexity
open ExecutablePortRotation
set_option autoImplicit false
noncomputable section

def rowCount (n : Nat) : Nat := n * FixedPortCycleFamily.degree * 3

/-- The first coordinate varies slowest; the three-valued dart label fastest. -/
def numericRow (n v j i : Nat) : List Bool :=
  pair (output v j i) (rotationFn (input n v j i))

def rowAt (n q : Nat) : List Bool :=
  numericRow n (q / 3 / FixedPortCycleFamily.degree)
    ((q / 3) % FixedPortCycleFamily.degree) (q % 3)

def rows (n : Nat) : List (List Bool) := (List.range (rowCount n)).map (rowAt n)

def dartWire {n : Nat}
    (p : PortCycleReplacement.Port n FixedPortCycleFamily.predecessor × Fin 3) : List Bool :=
  output p.1.1.val p.1.2.val p.2.val

def rowWire {n : Nat}
    (p : (PortCycleReplacement.Port n FixedPortCycleFamily.predecessor × Fin 3) ×
      (PortCycleReplacement.Port n FixedPortCycleFamily.predecessor × Fin 3)) : List Bool :=
  pair (dartWire p.1) (dartWire p.2)

def serializedTable (n : Nat) : List Bool :=
  DataEncode.bitstringEncode ((FixedPortCycleFamily.table n).map rowWire)

/-- Total row rule on pair(size word, counter word); all arithmetic uses lengths. -/
def rowRule (z : List Bool) : List Bool :=
  let n := marks (pairFst z)
  let q := pairSnd z
  let v := divC FixedPortCycleFamily.degree (divC 3 q)
  let j := modC FixedPortCycleFamily.degree (divC 3 q)
  let i := modC 3 q
  let p := pair (pair v j) i
  encodeListFn (pair [] (pair p (rotationFn (pair n p))))

/-- One actual function, on every bitstring. It interprets the input length as n.
The loop clock is constructed, not supplied by the caller. -/
def tableFn (z : List Bool) : List Bool :=
  listEncFn rowRule (pair (mulC (FixedPortCycleFamily.degree * 3) (marks z)) (marks z))

private def stageN (z : List Bool) : List Bool := marks (pairFst z)
private def stageV (z : List Bool) : List Bool :=
  divC FixedPortCycleFamily.degree (divC 3 (pairSnd z))
private def stageJ (z : List Bool) : List Bool :=
  modC FixedPortCycleFamily.degree (divC 3 (pairSnd z))
private def stageI (z : List Bool) : List Bool := modC 3 (pairSnd z)
private def stageP (z : List Bool) : List Bool := pair (pair (stageV z) (stageJ z)) (stageI z)
private def stageInput (z : List Bool) : List Bool := pair (stageN z) (stageP z)
private def stageR : List Bool → List Bool := rotationFn ∘ stageInput
private def stageW (z : List Bool) : List Bool := pair (stageP z) (stageR z)
private def stageE (z : List Bool) : List Bool := encodeListFn (pair [] (stageW z))

private theorem stageN_mem_FP : stageN ∈ FP := marks_mem_FP Cobham.fstBlock_mem_FP
private theorem stageV_mem_FP : stageV ∈ FP :=
  divC_mem_FP (divC_mem_FP Cobham.sndBlock_mem_FP 3) FixedPortCycleFamily.degree
private theorem stageJ_mem_FP : stageJ ∈ FP :=
  modC_mem_FP (divC_mem_FP Cobham.sndBlock_mem_FP 3) FixedPortCycleFamily.degree
private theorem stageI_mem_FP : stageI ∈ FP := modC_mem_FP Cobham.sndBlock_mem_FP 3
private theorem stageP_mem_FP : stageP ∈ FP :=
  Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP stageV_mem_FP stageJ_mem_FP) stageI_mem_FP
private theorem stageInput_mem_FP : stageInput ∈ FP :=
  Cobham.pairFn_mem_FP stageN_mem_FP stageP_mem_FP
private theorem stageComposition_mem_FP : (rotationFn ∘ stageInput) ∈ FP :=
  @mem_FP_comp stageInput rotationFn stageInput_mem_FP rotationFn_mem_FP

private theorem stageR_mem_FP : stageR ∈ FP :=
  stageComposition_mem_FP
private theorem stageW_mem_FP : stageW ∈ FP := Cobham.pairFn_mem_FP stageP_mem_FP stageR_mem_FP
private theorem stageE_mem_FP : stageE ∈ FP :=
  mem_FP_comp (Cobham.pairFn_mem_FP (constFn_mem_FP []) stageW_mem_FP) encodeListFn_mem_FP

private theorem rowRule_eq_stage (z : List Bool) : rowRule z = stageE z := by
  simp only [rowRule, stageE, stageW, stageR, Function.comp_def,
    stageInput, stageN, stageP, stageV, stageJ, stageI]

theorem rowRule_mem_FP : rowRule ∈ FP :=
  mem_FP_of_eq stageE_mem_FP (fun z => (rowRule_eq_stage z).symm)

theorem tableFn_mem_FP : tableFn ∈ FP := by
  have hn := marks_mem_FP id_mem_FP
  have hc := mulC_mem_FP hn (FixedPortCycleFamily.degree * 3)
  exact mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hc hn)
    (materialize_mem_FP rowRule_mem_FP)) (fun _ => rfl)

theorem rowRule_on_input (n q : Nat) :
    rowRule (pair (unary n) (unary q)) = DataEncode.bitstringEncode (rowAt n q) := by
  simp [rowRule, encodeListFn_eq, marks_eq, divC_eq FixedPortCycleFamily.degree_pos,
    divC_eq (by norm_num : 0 < (3 : Nat)),
    modC_eq FixedPortCycleFamily.degree_pos, modC_eq (by norm_num : 0 < (3 : Nat)),
    unary, rowAt, numericRow, output, input]

@[simp] theorem rows_length (n : Nat) : (rows n).length = rowCount n := by
  simp [rows]

theorem tableFn_rows (z : List Bool) :
    tableFn z = DataEncode.bitstringEncode (rows z.length) := by
  unfold tableFn
  apply listEncFn_eq_bitstringEncode (rows z.length)
  · simp [marks_eq, rowCount, Nat.mul_assoc]
  · intro i hi
    simp only [pairSnd_pair, marks_eq]
    change rowRule (pair (unary z.length) (unary i)) = _
    simp only [rows, List.getElem_map, List.getElem_range]
    exact rowRule_on_input z.length i

/-! The next identities fix canonical order, not merely a permutation. -/
private theorem range_mul_map {α : Type} (n k : Nat) (f : Nat → α) :
    (List.range (n*k)).map f = (List.range n).flatMap fun v =>
      (List.range k).map fun j => f (v*k+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ,
      List.flatMap_append]
    simp [List.map_map]

private theorem range_mul_flatMap {α : Type} (n k : Nat) (f : Nat → List α) :
    (List.range (n*k)).flatMap f = (List.range n).flatMap fun v =>
      (List.range k).flatMap fun j => f (v*k+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ,
      List.flatMap_append]
    simp [List.flatMap_map]

private theorem flatMap_congr {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  exact congrArg List.flatten (List.map_congr_left h)

private theorem finRange_map_value {α : Type} (n : Nat) (f : Nat → α) :
    (List.finRange n).map (fun v => f v.val) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

private theorem finRange_flatMap_value {α : Type} (n : Nat) (f : Nat → List α) :
    (List.finRange n).flatMap (fun v => f v.val) = (List.range n).flatMap f :=
  congrArg List.flatten (finRange_map_value n f)

theorem rowAt_mixedRadix (n v j i : Nat) (hj : j < FixedPortCycleFamily.degree)
    (hi : i < 3) :
    rowAt n ((v * FixedPortCycleFamily.degree + j) * 3 + i) = numericRow n v j i := by
  have hq : ((v * FixedPortCycleFamily.degree + j) * 3 + i) / 3 =
      v * FixedPortCycleFamily.degree + j := by
    rw [Nat.mul_comm _ 3, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hi, Nat.add_zero]
  have hv : (v * FixedPortCycleFamily.degree + j) / FixedPortCycleFamily.degree = v := by
    rw [Nat.mul_comm v, Nat.mul_add_div FixedPortCycleFamily.degree_pos,
      Nat.div_eq_of_lt hj, Nat.add_zero]
  simp only [rowAt, hq, hv, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj,
    Nat.mod_eq_of_lt hi]

theorem rows_canonical_order (n : Nat) :
    rows n = (List.range n).flatMap fun v =>
      (List.range FixedPortCycleFamily.degree).flatMap fun j =>
        (List.range 3).map fun i => numericRow n v j i := by
  rw [rows, rowCount, range_mul_map, range_mul_flatMap]
  apply flatMap_congr
  intro v hv
  apply flatMap_congr
  intro j hj
  apply List.map_congr_left
  intro i hi
  exact rowAt_mixedRadix n v j i (List.mem_range.mp hj) (List.mem_range.mp hi)

theorem numericRow_agrees (n : Nat) (v : Fin n)
    (j : Fin (FixedPortCycleFamily.predecessor + 1)) (i : Fin 3) :
    numericRow n v.val j.val i.val =
      rowWire (((v,j),i), PortCycleReplacement.rotation
        (FixedPortCycleFamily.baseRotation n) ((v,j),i)) := by
  unfold numericRow
  rw [rotationFn_agrees]
  rfl

theorem rows_eq_actual_table (n : Nat) :
    rows n = (FixedPortCycleFamily.table n).map rowWire := by
  have hfinite : (FixedPortCycleFamily.table n).map rowWire =
      (List.finRange n).flatMap fun v =>
        (List.finRange (FixedPortCycleFamily.predecessor + 1)).flatMap fun j =>
          (List.finRange 3).map fun i => numericRow n v.val j.val i.val := by
    simp only [FixedPortCycleFamily.table, PortCycleReplacement.table,
      List.map_flatMap, List.map_map, Function.comp_def]
    apply flatMap_congr
    intro v hv
    apply flatMap_congr
    intro j hj
    apply List.map_congr_left
    intro i hi
    exact (numericRow_agrees n v j i).symm
  rw [hfinite, rows_canonical_order]
  simp only [finRange_map_value]
  have hj (v : Nat) := finRange_flatMap_value (FixedPortCycleFamily.predecessor + 1)
    (fun j => (List.range 3).map (numericRow n v j))
  simp only [← FixedPortCycleFamily.degree_eq] at hj
  simp_rw [hj]
  exact (finRange_flatMap_value n (fun v =>
    (List.range FixedPortCycleFamily.degree).flatMap fun j =>
      (List.range 3).map (numericRow n v j))).symm

/-- Exact serialized equality, including list order, duplicates and both endpoints. -/
theorem tableFn_eq (z : List Bool) : tableFn z = serializedTable z.length := by
  rw [tableFn_rows, rows_eq_actual_table, serializedTable]

theorem tableFn_unary (n : Nat) : tableFn (unary n) = serializedTable n := by
  simpa using tableFn_eq (unary n)

theorem tableFn_zero : tableFn [] = DataEncode.bitstringEncode ([] : List (List Bool)) := by
  simp [tableFn_rows, rows, rowCount]

/-! Wire accounting includes every pair delimiter and every outer list/bit encoding. -/
theorem output_length (v j i : Nat) : (output v j i).length = 4*v+2*j+i+6 := by
  simp [output, pair_length, unary]
  omega

theorem rowWire_length_le {n : Nat}
    (p : (PortCycleReplacement.Port n FixedPortCycleFamily.predecessor × Fin 3) ×
      (PortCycleReplacement.Port n FixedPortCycleFamily.predecessor × Fin 3)) :
    (rowWire p).length ≤ 12*n + 6*FixedPortCycleFamily.degree + 26 := by
  have hv := p.1.1.1.isLt
  have hw := p.2.1.1.isLt
  have hj : p.1.1.2.val < FixedPortCycleFamily.degree := by
    simpa only [FixedPortCycleFamily.degree_eq] using p.1.1.2.isLt
  have hk : p.2.1.2.val < FixedPortCycleFamily.degree := by
    simpa only [FixedPortCycleFamily.degree_eq] using p.2.1.2.isLt
  have hi := p.1.2.isLt
  have hl := p.2.2.isLt
  simp only [rowWire, dartWire, pair_length, output_length]
  omega

theorem rowAt_length_le (n q : Nat) (hq : q < rowCount n) :
    (rowAt n q).length ≤ 12*n + 6*FixedPortCycleFamily.degree + 26 := by
  have hm : q / 3 < n * FixedPortCycleFamily.degree :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hq
  have hv : q / 3 / FixedPortCycleFamily.degree < n :=
    (Nat.div_lt_iff_lt_mul FixedPortCycleFamily.degree_pos).mpr hm
  let v : Fin n := ⟨q / 3 / FixedPortCycleFamily.degree, hv⟩
  let j : Fin (FixedPortCycleFamily.predecessor + 1) :=
    ⟨(q / 3) % FixedPortCycleFamily.degree, by
      simpa only [FixedPortCycleFamily.degree_eq] using
        Nat.mod_lt (q / 3) FixedPortCycleFamily.degree_pos⟩
  let i : Fin 3 := ⟨q % 3, Nat.mod_lt _ (by norm_num)⟩
  change (numericRow n v.val j.val i.val).length ≤ _
  rw [numericRow_agrees]
  exact rowWire_length_le _

theorem bitList_encode_length_le (s : List Bool) :
    (DataEncode.bitstringEncode s).length ≤ 4*s.length+2 := by
  have h := length_flatMap_boolBits s
  rw [bitstringEncode_list]
  simp only [List.length_append,
    List.length_cons, List.length_nil]
  omega

def wireBound : Polynomial Nat :=
  Polynomial.C 2 + (Polynomial.X * Polynomial.C (FixedPortCycleFamily.degree * 3)) *
    (Polynomial.C 4 * (Polynomial.C 12 * Polynomial.X +
      Polynomial.C (6*FixedPortCycleFamily.degree+26)) + Polynomial.C 2)

theorem wireBound_eval (n : Nat) : wireBound.eval n =
    2 + rowCount n * (4*(12*n+6*FixedPortCycleFamily.degree+26)+2) := by
  simp [wireBound, rowCount]
  ring

theorem tableFn_wire_bound (z : List Bool) : (tableFn z).length ≤ wireBound.eval z.length := by
  have hentries : ∀ q < rowCount z.length,
      (rowRule (pair (unary z.length) (unary q))).length ≤
        4*(12*z.length+6*FixedPortCycleFamily.degree+26)+2 := by
    intro q hq
    rw [rowRule_on_input]
    exact (bitList_encode_length_le _).trans (by
      have := rowAt_length_le z.length q hq
      omega)
  have hcat := length_entryCat_le rowRule (unary z.length)
    (4*(12*z.length+6*FixedPortCycleFamily.degree+26)+2) (rowCount z.length) hentries
  have he : DataEncode.bitstringEncode (rows z.length) =
      false :: entryCat rowRule (unary z.length) (rowCount z.length) ++ [true] := by
    simpa only [rows_length] using bitstringEncode_of_entries (E := rowRule)
      (x := unary z.length) (rows z.length) (by
        intro i hi
        simp only [rows, List.getElem_map, List.getElem_range]
        exact rowRule_on_input z.length i)
  rw [tableFn_rows, he, wireBound_eval]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end
end PvNP.RealizableHardness.ExecutablePortTable
