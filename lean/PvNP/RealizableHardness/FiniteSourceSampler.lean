import PvNP.RealizableHardness.SamplingFormulaPromises

/-! Uncompiled finite-table execution bridge. No binary-tape FP claim. -/
namespace PvNP.RealizableHardness.FiniteSourceSampler
open scoped BigOperators
open FiniteSampling InverseCDFSampler JointSamplingLaw

abbrev Row (N : Nat) := Rat × Formula (Fin N)

/-- Explicit ordered atoms: equal formulas and zero-probability rows remain indexed. -/
def ValidRows {N : Nat} (rows : List (Row N)) : Prop :=
  0 < rows.length ∧ (∀ i : Fin rows.length, 0 ≤ (rows.get i).1) ∧
    (∑ i : Fin rows.length, (rows.get i).1) = 1

instance {N : Nat} (rows : List (Row N)) : Decidable (ValidRows rows) := by
  unfold ValidRows
  infer_instance

structure Table (N : Nat) where
  rows : List (Row N)
  valid : ValidRows rows

def readTable {N : Nat} (rows : List (Row N)) : Option (Table N) :=
  if h : ValidRows rows then some ⟨rows,h⟩ else none

@[simp] theorem readTable_valid {N : Nat} (t : Table N) : readTable t.rows = some t := by
  cases t
  simp [readTable, *]

theorem readTable_invalid {N : Nat} (rows : List (Row N)) (h : ¬ValidRows rows) :
    readTable rows = none := by simp [readTable,h]

def probability {N : Nat} (t : Table N) (j : Nat) : Rat :=
  if h : j < t.rows.length then (t.rows.get ⟨j,h⟩).1 else 0

/-- Outside support the first stored formula is a total fallback of probability zero. -/
def formula {N : Nat} (t : Table N) (j : Nat) : Formula (Fin N) :=
  if h : j < t.rows.length then (t.rows.get ⟨j,h⟩).2
  else (t.rows.get ⟨0,t.valid.1⟩).2

@[simp] theorem probability_at {N : Nat} (t : Table N) (i : Fin t.rows.length) :
    probability t i.val = (t.rows.get i).1 := by simp [probability,i.isLt]

@[simp] theorem formula_at {N : Nat} (t : Table N) (i : Fin t.rows.length) :
    formula t i.val = (t.rows.get i).2 := by simp [formula,i.isLt]

theorem probability_outside {N : Nat} (t : Table N) (j : Nat) (hj : t.rows.length ≤ j) :
    probability t j = 0 := by simp [probability,show ¬j<t.rows.length by omega]

theorem probability_nonneg {N : Nat} (t : Table N) : ∀ j, 0 ≤ probability t j := by
  intro j
  unfold probability
  split
  next h => exact t.valid.2.1 ⟨j,h⟩
  next h => exact le_rfl

/-- The finite table itself discharges the normalization needed by the existing sampler. -/
theorem cumulative_endpoint {N : Nat} (t : Table N) :
    cumulative (probability t) t.rows.length = 1 := by
  unfold cumulative
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [probability_at] using t.valid.2.2

theorem cumulative_prefix {N : Nat} (t : Table N) (j : Nat) (hj : j ≤ t.rows.length) :
    cumulative (probability t) j =
      ∑ i : Fin j, (t.rows.get ⟨i.val,lt_of_lt_of_le i.isLt hj⟩).1 := by
  unfold cumulative
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [probability,lt_of_lt_of_le i.isLt hj]

/-- Reuse the existing computable first-crossing selector; no independent CDF theory. -/
def select {N : Nat} (t : Table N) (D : Nat) (seed : Fin D) : Fin t.rows.length :=
  sampler (probability t) D t.rows.length (cumulative_endpoint t) seed

theorem select_interval {N : Nat} (t : Table N) (D : Nat) (seed : Fin D)
    (i : Fin t.rows.length) :
    select t D seed = i ↔ cut (probability t) D i.val ≤ seed.val ∧
      seed.val < cut (probability t) D (i.val+1) :=
  sampler_eq_iff _ _ _ _ (probability_nonneg t) _ _

theorem select_not_zero_mass {N : Nat} (t : Table N) (D : Nat) (seed : Fin D)
    (i : Fin t.rows.length) (hi : (t.rows.get i).1 = 0) : select t D seed ≠ i := by
  intro he
  have hs := (select_interval t D seed i).mp he
  have hc : cut (probability t) D (i.val+1) = cut (probability t) D i.val := by
    have hz : probability t i.val = 0 := (probability_at t i).trans hi
    simp only [cut, cumulative_succ, hz, add_zero]
  rw [hc] at hs
  omega

def selectBits {N : Nat} (t : Table N) (b : Nat) (bits : Fin b → Fin 2) : Fin t.rows.length :=
  select t (2^b) (finFunctionFinEquiv bits)

theorem selectBits_eq {N : Nat} (t : Table N) (b : Nat) (bits : Fin b → Fin 2) :
    selectBits t b bits = bitSampler (probability t) t.rows.length b (cumulative_endpoint t) bits := rfl

def selectArray {N : Nat} (t : Table N) (b M : Nat) (seeds : SeedArray M b) :
    Fin M → Fin t.rows.length := fun i => selectBits t b (seeds i)

theorem selectArray_eq {N : Nat} (t : Table N) (b M : Nat) (seeds : SeedArray M b) :
    selectArray t b M seeds = sampleArray (probability t) t.rows.length b M
      (cumulative_endpoint t) seeds := rfl

/-- Actual finite ordered selected list, including repeated selected indices. -/
def selected {N : Nat} (t : Table N) (b M : Nat) (seeds : SeedArray M b) :
    List (Formula (Fin N)) := List.ofFn (fun i => (t.rows.get (selectArray t b M seeds i)).2)

theorem selected_eq_fromSeeds {N : Nat} (t : Table N) (b M : Nat) (seeds : SeedArray M b) :
    selected t b M seeds = List.ofFn
      (SamplingFormulaPromises.fromSeeds (probability t) t.rows.length b M
        (cumulative_endpoint t) (formula t) seeds) := by
  unfold selected
  congr 1
  funext i
  simp only [SamplingFormulaPromises.fromSeeds, SamplingFormulaPromises.sampled, formula_at,
    selectArray_eq]

@[simp] theorem selected_length {N : Nat} (t : Table N) (b M : Nat) (seeds : SeedArray M b) :
    (selected t b M seeds).length = M := by simp [selected]

/-- Raw seed lists must have exactly b digits. Digits already have the finite binary type. -/
def selectRaw {N : Nat} (t : Table N) (b : Nat) (bits : List (Fin 2)) : Option (Fin t.rows.length) :=
  if h : bits.length = b then
    some (selectBits t b (fun i => bits.get ⟨i.val,by omega⟩))
  else none

theorem selectRaw_invalid {N : Nat} (t : Table N) (b : Nat) (bits : List (Fin 2))
    (h : bits.length ≠ b) : selectRaw t b bits = none := by simp [selectRaw,h]

theorem selectRaw_ofFn {N : Nat} (t : Table N) (b : Nat) (bits : Fin b → Fin 2) :
    selectRaw t b (List.ofFn bits) = some (selectBits t b bits) := by
  simp [selectRaw]

end PvNP.RealizableHardness.FiniteSourceSampler
