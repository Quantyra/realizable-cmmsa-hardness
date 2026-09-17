import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Complexitylib.Encoding.DataEncode

/-! Uncompiled source draft: first-occurrence renaming of compact binary source
labels. No Allocation distinctness assumption, encoded FP or hardness assertion.
Rows and RHS retain their original order and multiplicity. -/
namespace PvNP.RealizableHardness.ActualSourceNormalization
set_option autoImplicit false

abbrev BinaryTriple := Prod Nat (Prod Nat Nat)
abbrev Source := Prod (List BinaryTriple) (List Bool)

def Valid (S : Source) : Prop := S.1.length = S.2.length

def wire (S : Source) : List Bool := Complexity.DataEncode.bitstringEncode S

def tripleLabels (t : BinaryTriple) : List Nat := [t.1, t.2.1, t.2.2]
def flatten (S : Source) : List Nat := S.1.flatMap tripleLabels

def first (S : Source) (v : Nat) : Nat := (flatten S).idxOf v

def renameTriple (S : Source) (t : BinaryTriple) : BinaryTriple :=
  (first S t.1, first S t.2.1, first S t.2.2)

def normalize (S : Source) : Source := (S.1.map (renameTriple S), S.2)

theorem flatten_length (S : Source) : (flatten S).length = 3*S.1.length := by
  unfold flatten
  induction S.1 with
  | nil => simp
  | cons t ts ih => simp [List.flatMap_cons, tripleLabels, ih]; omega

theorem label_mem_flatten {S : Source} {t : BinaryTriple} (ht : t ∈ S.1)
    {v : Nat} (hv : v ∈ tripleLabels t) : v ∈ flatten S :=
  List.mem_flatMap.mpr ⟨t, ht, hv⟩

theorem first_lt {S : Source} {v : Nat} (hv : v ∈ flatten S) :
    first S v < 3*S.1.length := by
  rw [<- flatten_length]
  exact List.idxOf_lt_length_of_mem hv

theorem get_first {S : Source} {v : Nat} (hv : v ∈ flatten S) :
    (flatten S)[first S v]? = some v := List.getElem?_idxOf hv

theorem first_eq_iff_on_used {S : Source} {v w : Nat}
    (hv : v ∈ flatten S) (hw : w ∈ flatten S) :
    first S v = first S w <-> v = w := by
  constructor
  · intro he
    have hg := get_first hv
    rw [he, get_first hw] at hg
    exact Option.some.inj hg.symm
  · intro he; subst w; rfl

theorem normalized_rows_length (S : Source) : (normalize S).1.length = S.1.length := by
  simp [normalize]

theorem normalized_rhs (S : Source) : (normalize S).2 = S.2 := rfl

theorem normalized_valid {S : Source} (h : Valid S) : Valid (normalize S) := by
  simpa [Valid, normalize] using h

theorem normalized_label_bound {S : Source} {t : BinaryTriple} (ht : t ∈ S.1) :
    (renameTriple S t).1 < 3*S.1.length ∧
    (renameTriple S t).2.1 < 3*S.1.length ∧
    (renameTriple S t).2.2 < 3*S.1.length := by
  exact ⟨first_lt (label_mem_flatten ht (by simp [tripleLabels])),
    first_lt (label_mem_flatten ht (by simp [tripleLabels])),
    first_lt (label_mem_flatten ht (by simp [tripleLabels]))⟩

/-- Values of unused output names never affect an equation. -/
def liftAssignment (S : Source) (a : Nat -> ZMod 2) (k : Nat) : ZMod 2 :=
  a ((flatten S)[k]?.getD 0)

/-- Unused original labels are explicitly assigned zero. -/
def decodeAssignment (S : Source) (b : Nat -> ZMod 2) (v : Nat) : ZMod 2 :=
  if v ∈ flatten S then b (first S v) else 0

theorem lift_used {S : Source} (a : Nat -> ZMod 2) {v : Nat} (hv : v ∈ flatten S) :
    liftAssignment S a (first S v) = a v := by
  simp [liftAssignment, get_first hv]

theorem decode_used {S : Source} (b : Nat -> ZMod 2) {v : Nat} (hv : v ∈ flatten S) :
    decodeAssignment S b v = b (first S v) := by simp [decodeAssignment, hv]

theorem decode_unused {S : Source} (b : Nat -> ZMod 2) {v : Nat} (hv : v ∉ flatten S) :
    decodeAssignment S b v = 0 := by simp [decodeAssignment, hv]

def rowValue (a : Nat -> ZMod 2) (t : BinaryTriple) : ZMod 2 :=
  a t.1 + a t.2.1 + a t.2.2

theorem rowValue_lift {S : Source} (a : Nat -> ZMod 2) {t : BinaryTriple}
    (ht : t ∈ S.1) : rowValue (liftAssignment S a) (renameTriple S t) = rowValue a t := by
  have h0 := label_mem_flatten ht (v := t.1) (by simp [tripleLabels])
  have h1 := label_mem_flatten ht (v := t.2.1) (by simp [tripleLabels])
  have h2 := label_mem_flatten ht (v := t.2.2) (by simp [tripleLabels])
  simp only [rowValue, renameTriple, lift_used a h0, lift_used a h1, lift_used a h2]

theorem rowValue_decode {S : Source} (b : Nat -> ZMod 2) {t : BinaryTriple}
    (ht : t ∈ S.1) : rowValue (decodeAssignment S b) t = rowValue b (renameTriple S t) := by
  have h0 := label_mem_flatten ht (v := t.1) (by simp [tripleLabels])
  have h1 := label_mem_flatten ht (v := t.2.1) (by simp [tripleLabels])
  have h2 := label_mem_flatten ht (v := t.2.2) (by simp [tripleLabels])
  simp only [rowValue, renameTriple, decode_used b h0, decode_used b h1, decode_used b h2]

def rhsValue (b : Bool) : ZMod 2 := if b then 1 else 0

/-- On Valid sources there is exactly one flag per original equation. On
invalid sources this explicit total rule follows List.zip truncation. -/
def violationFlags (S : Source) (a : Nat -> ZMod 2) : List Bool :=
  ((S.1.map (rowValue a)).zip S.2).map (fun p => decide (p.1 ≠ rhsValue p.2))

def violations (S : Source) (a : Nat -> ZMod 2) : Nat :=
  (violationFlags S a).countP id

theorem violationFlags_lift (S : Source) (a : Nat -> ZMod 2) :
    violationFlags (normalize S) (liftAssignment S a) = violationFlags S a := by
  have he : (S.1.map (renameTriple S)).map (rowValue (liftAssignment S a)) =
      S.1.map (rowValue a) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    exact rowValue_lift a ht
  simp only [violationFlags, normalize, he]

theorem violationFlags_decode (S : Source) (b : Nat -> ZMod 2) :
    violationFlags S (decodeAssignment S b) = violationFlags (normalize S) b := by
  have he : S.1.map (rowValue (decodeAssignment S b)) =
      (S.1.map (renameTriple S)).map (rowValue b) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    exact rowValue_decode b ht
  simp only [violationFlags, normalize, he]

theorem violations_lift (S : Source) (a : Nat -> ZMod 2) :
    violations (normalize S) (liftAssignment S a) = violations S a := by
  simp only [violations, violationFlags_lift]

theorem violations_decode (S : Source) (b : Nat -> ZMod 2) :
    violations S (decodeAssignment S b) = violations (normalize S) b := by
  simp only [violations, violationFlags_decode]

theorem normalize_empty : normalize ([], []) = ([], []) := rfl

theorem repeated_labels_preserved (S : Source) (v w : Nat) :
    renameTriple S (v,v,w) = (first S v,first S v,first S w) := rfl

end PvNP.RealizableHardness.ActualSourceNormalization
