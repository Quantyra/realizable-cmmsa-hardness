import PvNP.RealizableHardness.CMMSACodec
import PvNP.RealizableHardness.SamplingFormulaPromises
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Equiv.Fin.Basic

/-! Uncompiled semantic-to-binary constructor. No FP/runtime claim. -/
namespace PvNP.RealizableHardness.CMMSAEncoding
open CMMSACodec
open scoped BigOperators

theorem bitValue_bits (n : Nat) : bitValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitValue]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases b <;> simp [bitValue, ih, Nat.bit] <;> omega

def natTree (n : Nat) : Tree := digitTree n.bits

@[simp] theorem read_natTree (n : Nat) : readNat (natTree n) = some n := by
  simp [natTree, bitValue_bits]

theorem natTree_length (n : Nat) : (Tree.encode (natTree n)).length ≤ 4*n.size+1 := by
  simpa [natTree, Nat.size_eq_bits_len] using digitTree_length n.bits

/-- Valid data uses positive rationals. Absolute numerator is exact on that domain. -/
def ratTree (q : Rat) : Tree := .node (natTree q.num.natAbs) (natTree q.den)

@[simp] theorem read_ratTree (q : Rat) (hq : 0 ≤ q) : readRat (ratTree q) = some q := by
  have hn : (q.num.natAbs : Rat) = (q.num : Rat) := by
    have hz : (q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
    simpa only [Int.cast_natCast] using congrArg (fun z : Int => (z : Rat)) hz
  simp [ratTree, readRat, q.den_ne_zero, hn, Rat.num_div_den]

theorem ratTree_length (q : Rat) :
    (Tree.encode (ratTree q)).length ≤ 4*q.num.natAbs.size+4*q.den.size+3 := by
  have hn := natTree_length q.num.natAbs
  have hd := natTree_length q.den
  simp only [ratTree, Tree.encode, List.length_cons, List.length_append]
  omega

def formulaTree {N : Nat} : Formula (Fin N) → Tree
  | .var v => .node .leaf (natTree v.val)
  | .and p q => .node (.node .leaf .leaf) (.node (formulaTree p) (formulaTree q))
  | .or p q => .node (.node .leaf (.node .leaf .leaf))
      (.node (formulaTree p) (formulaTree q))

@[simp] theorem read_formulaTree {N : Nat} (f : Formula (Fin N)) :
    readFormula N (formulaTree f) = some f := by
  induction f with
  | var v => simp [formulaTree, readFormula, v.isLt]
  | and p q hp hq => simp [formulaTree, readFormula, hp, hq]
  | or p q hp hq => simp [formulaTree, readFormula, hp, hq]

theorem readList_map {α : Type} (enc : α → Tree) (read : Tree → Option α)
    (xs : List α) (h : ∀ x ∈ xs, read (enc x) = some x) :
    readList read (listTree (xs.map enc)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, read (enc y) = some y := fun y hy => h y (by simp [hy])
      simp [listTree, readList, hx, ih ht]

def dataTree (d : Data) : Tree :=
  .node (listTree (d.weights.map ratTree))
    (.node (listTree (d.formulas.map formulaTree)) (ratTree d.budget))

/-- Every valid explicit semantic record is represented, not merely prevalidated syntax. -/
theorem read_dataTree {L : Nat} (d : Data) (hd : Valid L d) :
    readData (dataTree d) = some d := by
  have hw := readList_map ratTree readRat d.weights
    (fun w hw => read_ratTree w (le_of_lt (hd.1 w hw)))
  have hf := readList_map formulaTree (readFormula d.weights.length) d.formulas
    (fun f _ => read_formulaTree f)
  have hb := read_ratTree d.budget hd.2.2.2.2.1.le
  cases d
  simp_all [dataTree, readData]

def ofData {L : Nat} (d : Data) (hd : Valid L d) : Instance L :=
  ⟨dataTree d, by simp [accepted, read_dataTree d hd, hd]⟩

@[simp] theorem ofData_data {L : Nat} (d : Data) (hd : Valid L d) :
    (ofData d hd).data = d := by
  dsimp only [ofData, Instance.data]
  split
  next d' h =>
    have hh := read_dataTree d hd
    rw [h] at hh
    exact Option.some.inj hh
  next h =>
    have hh := read_dataTree d hd
    simp [h] at hh

def encodeData {L : Nat} (d : Data) (hd : Valid L d) : Bits := encode (ofData d hd)

@[simp] theorem decode_encodeData {L : Nat} (d : Data) (hd : Valid L d) :
    (decode L (encodeData d hd)).map Instance.data = some d := by
  simp [encodeData]

/-- A concrete finite family becomes an ordered explicit list, with no deduplication. -/
def indexedData {N M : Nat} (w : Fin N → Rat) (F : Fin M → Formula (Fin N))
    (s : Rat) : Data :=
  { weights := List.ofFn w
    formulas := List.ofFn (fun i => Formula.rename
      (Fin.cast (by simp : N = (List.ofFn w).length)) (F i))
    budget := s }

@[simp] theorem indexedData_count {N M : Nat} (w : Fin N → Rat)
    (F : Fin M → Formula (Fin N)) (s : Rat) :
    (indexedData w F s).formulas.length = M := by simp [indexedData]

theorem indexedData_valid {N M L : Nat} (w : Fin N → Rat)
    (F : Fin M → Formula (Fin N)) (s : Rat)
    (hw : ∀ v, 0 < w v) (hsum : ∑ v, w v = 1) (hM : 0 < M)
    (hF : ∀ i, Formula.leaves (F i) ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) :
    Valid L (indexedData w F s) := by
  refine ⟨?_, ?_, ?_, ?_, hs, hs1⟩
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact hw i
  · simpa [indexedData, List.sum_ofFn] using hsum
  · intro he
    have hl := congrArg List.length he
    simp [indexedData] at hl
    omega
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    change Formula.leaves (Formula.rename
      (Fin.cast (by simp : N = (List.ofFn w).length)) (F i)) ≤ L
    rw [Formula.leaves_rename]
    exact hF i

def encodeIndexed {N M L : Nat} (w : Fin N → Rat)
    (F : Fin M → Formula (Fin N)) (s : Rat)
    (hw : ∀ v, 0 < w v) (hsum : ∑ v, w v = 1) (hM : 0 < M)
    (hF : ∀ i, Formula.leaves (F i) ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) : Bits :=
  encodeData (indexedData w F s) (indexedData_valid w F s hw hsum hM hF hs hs1)

theorem decode_encodeIndexed {N M L : Nat} (w : Fin N → Rat)
    (F : Fin M → Formula (Fin N)) (s : Rat)
    (hw : ∀ v, 0 < w v) (hsum : ∑ v, w v = 1) (hM : 0 < M)
    (hF : ∀ i, Formula.leaves (F i) ≤ L) (hs : 0 < s) (hs1 : s ≤ 1) :
    (decode L (encodeIndexed w F s hw hsum hM hF hs hs1)).map Instance.data =
      some (indexedData w F s) := by simp [encodeIndexed]

/-- Pointwise formula semantics through the explicit coordinate cast. -/
theorem indexedData_eval {N M : Nat} (w : Fin N → Rat)
    (F : Fin M → Formula (Fin N)) (s : Rat)
    (x : Fin (List.ofFn w).length → Bool) (i : Fin M) :
    Formula.eval x ((List.ofFn (fun j => Formula.rename
      (Fin.cast (by simp : N = (List.ofFn w).length)) (F j))).get
        ⟨i.val, by simpa using i.isLt⟩) =
    Formula.eval (fun v => x (Fin.cast (by simp) v)) (F i) := by
  simp

/-- Concrete repair output with the standard sum-coordinate equivalence. -/
def repairedFamily {N M : Nat} (F : Fin M → Formula (Fin N)) :
    Fin M → Formula (Fin (N+M)) :=
  fun i => Formula.rename finSumFinEquiv (Formula.repair F i)

@[simp] theorem repairedFamily_eval {N M : Nat} (F : Fin M → Formula (Fin N))
    (x : Fin (N+M) → Bool) (i : Fin M) :
    Formula.eval x (repairedFamily F i) =
      (Formula.eval (fun v => x (finSumFinEquiv (.inl v))) (F i) ||
        x (finSumFinEquiv (.inr i))) := by
  simp only [repairedFamily, Formula.eval_rename, Formula.repair, Formula.eval]

@[simp] theorem repairedFamily_leaves {N M : Nat} (F : Fin M → Formula (Fin N))
    (i : Fin M) : Formula.leaves (repairedFamily F i) = Formula.leaves (F i)+1 := by
  simp [repairedFamily]

/-- Exact actual seed-selected occurrences feed the same repair and coordinate map. -/
def seededFamily {N : Nat} (p : Nat → Rat) (S b M : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (F : Nat → Formula (Fin N))
    (seeds : JointSamplingLaw.SeedArray M b) : Fin M → Formula (Fin (N+M)) :=
  repairedFamily (SamplingFormulaPromises.fromSeeds p S b M hn F seeds)

theorem seededFamily_eval {N : Nat} (p : Nat → Rat) (S b M : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (F : Nat → Formula (Fin N))
    (seeds : JointSamplingLaw.SeedArray M b) (x : Fin (N+M) → Bool) (i : Fin M) :
    Formula.eval x (seededFamily p S b M hn F seeds i) =
      (Formula.eval (fun v => x (finSumFinEquiv (.inl v)))
        (F (JointSamplingLaw.sampleArray p S b M hn seeds i).val) ||
      x (finSumFinEquiv (.inr i))) := by
  simp only [seededFamily, repairedFamily_eval, SamplingFormulaPromises.fromSeeds,
    SamplingFormulaPromises.sampled]

end PvNP.RealizableHardness.CMMSAEncoding
