import PvNP.RealizableHardness.Formula

/-! Source draft: not compiled. Concrete binary syntax and validated CMMSA semantics.
No polynomial-time or full reduction theorem is asserted. -/
namespace PvNP.RealizableHardness.CMMSACodec

abbrev Bits := List Bool

inductive Tree where
  | leaf
  | node : Tree → Tree → Tree
  deriving DecidableEq

namespace Tree

def encode : Tree → Bits
  | .leaf => [false]
  | .node p q => true :: (encode p ++ encode q)

def depth : Tree → Nat
  | .leaf => 1
  | .node p q => max (depth p) (depth q) + 1

/-- Fuel bounds nesting depth, not any decoded numeric magnitude. -/
def parse : Nat → Bits → Option (Tree × Bits)
  | 0, _ => none
  | _+1, [] => none
  | _+1, false :: bs => some (.leaf, bs)
  | fuel+1, true :: bs => do
      let (p, rest) ← parse fuel bs
      let (q, tail) ← parse fuel rest
      pure (.node p q, tail)

theorem parse_encode (t : Tree) (tail : Bits) (fuel : Nat)
    (hf : depth t ≤ fuel) : parse fuel (encode t ++ tail) = some (t, tail) := by
  induction t generalizing fuel tail with
  | leaf =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel => rfl
  | node p q ihp ihq =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel =>
          have hp : depth p ≤ fuel := by simp only [depth] at hf; omega
          have hq : depth q ≤ fuel := by simp only [depth] at hf; omega
          simp only [encode, List.cons_append, List.append_assoc, parse]
          rw [ihp (encode q ++ tail) fuel hp]
          change (do
            let v ← parse fuel (encode q ++ tail)
            pure (Tree.node p v.1, v.2)) = some (Tree.node p q, tail)
          rw [ihq tail fuel hq]
          rfl

theorem depth_le_length (t : Tree) : depth t ≤ (encode t).length := by
  induction t with
  | leaf => simp [depth, encode]
  | node p q hp hq => simp only [depth, encode, List.length_cons, List.length_append]; omega

end Tree

/-- Little-endian digits; magnitude is never encoded by that many nodes. -/
def bitValue : Bits → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitValue bs

/-- A list cell per binary digit, with a constant-size digit tag. -/
def digitTree : Bits → Tree
  | [] => .leaf
  | false :: bs => .node .leaf (digitTree bs)
  | true :: bs => .node (.node .leaf .leaf) (digitTree bs)

def readDigits : Tree → Option Bits
  | .leaf => some []
  | .node .leaf bs => (false :: ·) <$> readDigits bs
  | .node (.node .leaf .leaf) bs => (true :: ·) <$> readDigits bs
  | _ => none

@[simp] theorem read_digitTree (bs : Bits) : readDigits (digitTree bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [digitTree, readDigits, ih]

def readNat (t : Tree) : Option Nat := bitValue <$> readDigits t

/-- Wire size grows with the number of digits, not their represented value. -/
theorem digitTree_length (bs : Bits) :
    (Tree.encode (digitTree bs)).length ≤ 4*bs.length+1 := by
  induction bs with
  | nil => simp [digitTree, Tree.encode]
  | cons b bs ih =>
      cases b <;>
        simp only [digitTree, Tree.encode, List.length_cons, List.length_append,
          List.length_nil] at * <;> omega

@[simp] theorem readNat_digitTree (bs : Bits) : readNat (digitTree bs) = some (bitValue bs) := by
  simp [readNat]

/-- Numerator and denominator are binary naturals; zero denominator is rejected.
Signs are unnecessary for positive CMMSA weights and budgets. -/
def readRat : Tree → Option Rat
  | .node n d => do
      let num ← readNat n
      let den ← readNat d
      if den = 0 then none else some ((num : Rat) / den)
  | _ => none

def listTree : List Tree → Tree
  | [] => .leaf
  | t :: ts => .node t (listTree ts)

def readList {α : Type} (read : Tree → Option α) : Tree → Option (List α)
  | .leaf => some []
  | .node t ts => do
      let a ← read t
      let rest ← readList read ts
      pure (a :: rest)

/-- Existing positive AND/OR syntax, with variable bounds checked while parsing.
The three tags are leaf, node leaf leaf, node leaf (node leaf leaf). -/
def readFormula (n : Nat) : Tree → Option (Formula (Fin n))
  | .node .leaf v => do
      let k ← readNat v
      if h : k < n then some (.var ⟨k, h⟩) else none
  | .node (.node .leaf .leaf) (.node p q) => do
      let fp ← readFormula n p
      let fq ← readFormula n q
      pure (.and fp fq)
  | .node (.node .leaf (.node .leaf .leaf)) (.node p q) => do
      let fp ← readFormula n p
      let fq ← readFormula n q
      pure (.or fp fq)
  | _ => none

/-- Explicit coordinates and ordered occurrences, rather than arbitrary functions. -/
structure Data where
  weights : List Rat
  formulas : List (Formula (Fin weights.length))
  budget : Rat

def readData : Tree → Option Data
  | .node ws (.node fs budget) => do
      let weights ← readList readRat ws
      let formulas ← readList (readFormula weights.length) fs
      let budget ← readRat budget
      pure ⟨weights, formulas, budget⟩
  | _ => none

/-- L is a problem parameter. Gap/threshold parameters are not instance fields. -/
def Valid (L : Nat) (d : Data) : Prop :=
  (∀ w ∈ d.weights, 0 < w) ∧ d.weights.sum = 1 ∧
  d.formulas ≠ [] ∧ (∀ f ∈ d.formulas, Formula.leaves f ≤ L) ∧
  0 < d.budget ∧ d.budget ≤ 1

instance (L : Nat) (d : Data) : Decidable (Valid L d) := by
  unfold Valid
  infer_instance

def accepted (L : Nat) (t : Tree) : Bool :=
  match readData t with
  | none => false
  | some d => decide (Valid L d)

/-- A concrete, validated syntax instance. Retaining syntax permits noncanonical
binary rationals without identifying distinct byte representations. -/
abbrev Instance (L : Nat) := {t : Tree // accepted L t = true}

def Instance.data {L : Nat} (i : Instance L) : Data :=
  match h : readData i.val with
  | some d => d
  | none => False.elim (by have hi := i.property; simp [accepted, h] at hi)

theorem Instance.valid {L : Nat} (i : Instance L) : Valid L i.data := by
  unfold Instance.data
  split
  next d h =>
    have hi := i.property
    simpa [accepted, h] using hi
  next h =>
    have hi := i.property
    simp [accepted, h] at hi

def encode {L : Nat} (i : Instance L) : Bits := i.val.encode

/-- Total: malformed trees, trailing bits, invalid fields, bad indices, empty
formula lists, nonpositive or unnormalized weights, and invalid budgets fail. -/
def decode (L : Nat) (bs : Bits) : Option (Instance L) := do
  let (t, rest) ← Tree.parse (bs.length + 1) bs
  if rest = [] then
    if h : accepted L t = true then some ⟨t, h⟩ else none
  else none

@[simp] theorem decode_encode {L : Nat} (i : Instance L) :
    decode L (encode i) = some i := by
  have hp := Tree.parse_encode i.val [] ((encode i).length + 1)
    (Nat.le_trans (Tree.depth_le_length i.val) (Nat.le_succ _))
  simp only [List.append_nil] at hp
  change Tree.parse ((encode i).length + 1) (encode i) = some (i.val, []) at hp
  unfold decode
  rw [hp]
  simp [i.property]

theorem encode_injective {L : Nat} : Function.Injective (@encode L) := by
  intro i j h
  have hd := congrArg (decode L) h
  simpa using hd

@[simp] theorem decode_empty (L : Nat) : decode L [] = none := rfl

theorem decode_invalid (L : Nat) (bs : Bits) (t : Tree)
    (hp : Tree.parse (bs.length+1) bs = some (t, []))
    (hi : accepted L t = false) : decode L bs = none := by
  simp [decode, hp, hi]

/-- Semantic coordinates and formula indices retain list positions, including duplicates. -/
def Data.coordinateWeights (d : Data) : Fin d.weights.length → Rat := d.weights.get
def Data.indexedFormulas (d : Data) : Fin d.formulas.length → Formula (Fin d.weights.length) :=
  d.formulas.get

noncomputable def Data.cost (d : Data) (x : Fin d.weights.length → Bool) : Rat :=
  weight d.coordinateWeights x

noncomputable def Data.satisfaction (d : Data) (x : Fin d.weights.length → Bool) : Rat :=
  average (fun j => Formula.eval x (d.indexedFormulas j))

def Yes (eps : Rat) {L : Nat} (i : Instance L) : Prop :=
  ∃ x : Fin i.data.weights.length → Bool,
    i.data.cost x ≤ i.data.budget ∧ 1-eps ≤ i.data.satisfaction x

def No (sig gam : Rat) {L : Nat} (i : Instance L) : Prop :=
  ∀ x : Fin i.data.weights.length → Bool,
    i.data.cost x ≤ sig*i.data.budget → i.data.satisfaction x < gam

/-- Interpretation after decoding is exactly the same explicit data. -/
@[simp] theorem decoded_data {L : Nat} (i : Instance L) :
    (decode L (encode i)).map Instance.data = some i.data := by simp

theorem decoded_yes {L : Nat} (i : Instance L) (eps : Rat) :
    (∃ j, decode L (encode i) = some j ∧ Yes eps j) ↔ Yes eps i := by simp

theorem decoded_no {L : Nat} (i : Instance L) (sig gam : Rat) :
    (∃ j, decode L (encode i) = some j ∧ No sig gam j) ↔ No sig gam i := by simp

end PvNP.RealizableHardness.CMMSACodec
