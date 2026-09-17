import PvNP.RealizableHardness.FiniteSourceSampler
import PvNP.RealizableHardness.ExecutableRounding

/-! Uncompiled complete per-seed output constructor. No FP/runtime claim. -/
namespace PvNP.RealizableHardness.ExecutablePipeline
open CMMSACodec CMMSAEncoding
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Actual indexed table lookup, preserving trial positions. -/
def draws {N : Nat} (t : FiniteSourceSampler.Table N) (b M : Nat)
    (seeds : JointSamplingLaw.SeedArray M b) : Fin M -> Formula (Fin N) :=
  fun i => (t.rows.get (FiniteSourceSampler.selectArray t b M seeds i)).2

theorem draws_eq {N : Nat} (t : FiniteSourceSampler.Table N) (b M : Nat)
    (seeds : JointSamplingLaw.SeedArray M b) :
    draws t b M seeds = SamplingFormulaPromises.fromSeeds
      (FiniteSourceSampler.probability t) t.rows.length b M
      (FiniteSourceSampler.cumulative_endpoint t) (FiniteSourceSampler.formula t) seeds := by
  funext i
  simp only [draws, SamplingFormulaPromises.fromSeeds, SamplingFormulaPromises.sampled,
    FiniteSourceSampler.formula_at, FiniteSourceSampler.selectArray_eq]

/-- Each occurrence receives its own exception coordinate, even for repeated draws. -/
def repaired {N : Nat} (t : FiniteSourceSampler.Table N) (b M : Nat)
    (seeds : JointSamplingLaw.SeedArray M b) : Fin M -> Formula (Fin (N+M)) :=
  repairedFamily (draws t b M seeds)

theorem repaired_eval {N : Nat} (t : FiniteSourceSampler.Table N) (b M : Nat)
    (seeds : JointSamplingLaw.SeedArray M b) (x : Fin (N+M) -> Bool) (i : Fin M) :
    Formula.eval x (repaired t b M seeds i) =
      (Formula.eval (fun v => x (finSumFinEquiv (.inl v))) (draws t b M seeds i) ||
        x (finSumFinEquiv (.inr i))) := repairedFamily_eval _ _ _

theorem repaired_leaves {N : Nat} (t : FiniteSourceSampler.Table N) (b M : Nat)
    (seeds : JointSamplingLaw.SeedArray M b) (i : Fin M) :
    Formula.leaves (repaired t b M seeds i) = Formula.leaves (draws t b M seeds i)+1 :=
  repairedFamily_leaves _ _

/-- Complete explicit output record computed from finite inputs, without a validity oracle. -/
def data (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b) : Data :=
  { weights := ExecutableRounding.outputWeights ws M q
    formulas := List.ofFn (fun i => Formula.rename
      (Fin.cast (ExecutableRounding.outputWeights_length ws M q).symm) (repaired t b M seeds i))
    budget := ExecutableRounding.outputBudget ws M q }

@[simp] theorem data_count (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b) :
    (data ws t b M q seeds).formulas.length = M := by simp [data]

/-- Emit the full tree, retaining the computed unreduced arithmetic fractions. -/
def tree (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b) : Tree :=
  .node (ExecutableRounding.weightTree ws M q)
    (.node (listTree ((data ws t b M q seeds).formulas.map formulaTree))
      (ExecutableRounding.budgetTree ws M q))

def bits (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b) : Bits :=
  Tree.encode (tree ws t b M q seeds)

theorem read_tree (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b)
    (hd : 0 < ExecutableRounding.commonDenominator ws M q) :
    readData (tree ws t b M q seeds) = some (data ws t b M q seeds) := by
  have hf := readList_map formulaTree
    (readFormula (ExecutableRounding.outputWeights ws M q).length)
    (data ws t b M q seeds).formulas (fun f _ => read_formulaTree f)
  simp only [tree, readData, ExecutableRounding.read_weightTree ws M q hd]
  change (do
    let fs ← readList (readFormula (ExecutableRounding.outputWeights ws M q).length)
      (listTree ((data ws t b M q seeds).formulas.map formulaTree))
    let budget ← readRat (ExecutableRounding.budgetTree ws M q)
    pure (Data.mk (ExecutableRounding.outputWeights ws M q) fs budget)) = _
  rw [hf]
  simp only [Option.bind_some, ExecutableRounding.read_budgetTree ws M q hd]
  rfl

theorem record_congr {N M : Nat} (xs ys : List Rat) (hx : N = xs.length) (hy : N = ys.length)
    (F G : Fin M → Formula (Fin N)) (s t : Rat)
    (hxy : xs = ys) (hFG : F = G) (hst : s = t) :
    (Data.mk xs (List.ofFn (fun i => Formula.rename (Fin.cast hx) (F i))) s) =
      Data.mk ys (List.ofFn (fun i => Formula.rename (Fin.cast hy) (G i))) t := by
  cases hxy
  cases hFG
  cases hst
  rfl

/-- Full record equality, including dependent formula coordinates and ordered occurrences. -/
theorem data_eq (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) :
    data ws t b M (ExecutableRounding.inputOf p) seeds =
      CMMSAPipelineEncoding.outputData p (SamplingFormulaPromises.fromSeeds
        (FiniteSourceSampler.probability t) t.rows.length b M
        (FiniteSourceSampler.cumulative_endpoint t) (FiniteSourceSampler.formula t) seeds) := by
  unfold data CMMSAPipelineEncoding.outputData indexedData
  apply record_congr
  · exact ExecutableRounding.outputWeights_eq M p
  · simp only [repaired, draws_eq]
  · exact ExecutableRounding.outputBudget_eq M p

/-- A leaf bound on stored rows supplies the bound on every selected occurrence. -/
theorem draws_leaf_bound {N L : Nat} (t : FiniteSourceSampler.Table N) (b M : Nat)
    (seeds : JointSamplingLaw.SeedArray M b)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2 + 1 <= L) :
    forall i, Formula.leaves (draws t b M seeds i)+1 <= L := by
  intro i
  exact hF (FiniteSourceSampler.selectArray t b M seeds i)

theorem data_valid {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) :
    Valid L (data ws t b M (ExecutableRounding.inputOf p) seeds) := by
  rw [data_eq]
  apply CMMSAPipelineEncoding.outputData_valid p _ hM
  rw [← draws_eq]
  exact draws_leaf_bound t b M seeds hF

/-- Structural binary payload bound including every variable index and connective. -/
theorem formula_wire_bound {N : Nat} (f : Formula (Fin N)) :
    (Tree.encode (formulaTree f)).length + 7 <= Formula.leaves f * (4*N.size+10) := by
  induction f with
  | var v =>
      have hn := natTree_length v.val
      have hs := Nat.size_le_size (Nat.le_of_lt v.isLt)
      simp only [formulaTree, Tree.encode, List.length_cons, List.length_append, List.length_nil, Formula.leaves]
      omega
  | and f g hf hg =>
      simp only [formulaTree, Tree.encode, List.length_cons, List.length_append, List.length_nil, Formula.leaves] at *
      nlinarith
  | or f g hf hg =>
      simp only [formulaTree, Tree.encode, List.length_cons, List.length_append, List.length_nil, Formula.leaves] at *
      nlinarith

theorem full_wire_bound {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) :
    let B := ExecutableRounding.inputMagnitudeBound ws M (ExecutableRounding.inputOf p)
    (bits ws t b M (ExecutableRounding.inputOf p) seeds).length <=
      (ws.length+M)*(8*B.size+4)+1 +
      (M*(L*(4*(ws.length+M).size+10)+1)+1) + (8*B.size+3) + 2 := by
  have ha := ExecutableRounding.input_arithmetic_wire_bound M hM p
  have hv := data_valid ws t b M p seeds hM hF
  have hf := ExecutableRounding.listTree_length_bound
    ((data ws t b M (ExecutableRounding.inputOf p) seeds).formulas.map formulaTree)
    (L*(4*(ws.length+M).size+10)) (by
      intro tr ht
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ht
      have h := formula_wire_bound f
      have hl := hv.2.2.2.1 f hf
      have hm := Nat.mul_le_mul_right (4*(ws.length+M).size+10) hl
      simp only [data, ExecutableRounding.outputWeights_length] at h
      omega)
  simp only [List.length_map, data_count] at hf
  dsimp only at ha ⊢
  simp only [bits, tree, Tree.encode, List.length_cons, List.length_append]
  omega

/-- Validation failure is explicit even for raw scalar choices and zero trials.
This validates the computed output; it is not an input-table byte parser. -/
def checkedBits (L : Nat) (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b) : Option Bits :=
  if accepted L (tree ws t b M q seeds) then some (bits ws t b M q seeds) else none

theorem checkedBits_reject (L : Nat) (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (q : ExecutableRounding.InputParameters) (seeds : JointSamplingLaw.SeedArray M b)
    (h : accepted L (tree ws t b M q seeds) = false) :
    checkedBits L ws t b M q seeds = none := by simp [checkedBits,h]

def instanceOf {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) : Instance L :=
  ⟨tree ws t b M (ExecutableRounding.inputOf p) seeds, by
    simp [accepted, read_tree ws t b M (ExecutableRounding.inputOf p) seeds
      (ExecutableRounding.positive_integer_data M hM p).1,
      data_valid ws t b M p seeds hM hF]⟩

theorem instanceOf_data {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) :
    (instanceOf ws t b M p seeds hM hF).data = data ws t b M (ExecutableRounding.inputOf p) seeds := by
  have hr := read_tree ws t b M (ExecutableRounding.inputOf p) seeds
    (ExecutableRounding.positive_integer_data M hM p).1
  dsimp only [Instance.data, instanceOf]
  split
  next d h =>
    rw [h] at hr
    exact Option.some.inj hr
  next h => simp [h] at hr

theorem decode_bits {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) :
    (decode L (bits ws t b M (ExecutableRounding.inputOf p) seeds)).map Instance.data =
      some (CMMSAPipelineEncoding.outputData p (SamplingFormulaPromises.fromSeeds
        (FiniteSourceSampler.probability t) t.rows.length b M
        (FiniteSourceSampler.cumulative_endpoint t) (FiniteSourceSampler.formula t) seeds)) := by
  change (decode L (encode (instanceOf ws t b M p seeds hM hF))).map Instance.data = _
  rw [decoded_data, instanceOf_data, data_eq]

/-- Equality of decoded data with the seeded semantic instance, not canonical byte equality. -/
theorem decode_seeded_data {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length,
      Formula.leaves (FiniteSourceSampler.formula t j.val)+1 <= L) :
    (decode L (bits ws t b M (ExecutableRounding.inputOf p) seeds)).map Instance.data =
      some (CMMSAPipelineEncoding.seededInstance p (FiniteSourceSampler.probability t)
        t.rows.length b (FiniteSourceSampler.cumulative_endpoint t)
        (FiniteSourceSampler.formula t) seeds hM hF).data := by
  have hf : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L := by
    simpa only [FiniteSourceSampler.formula_at] using hF
  simpa only [CMMSAPipelineEncoding.seededInstance, CMMSAPipelineEncoding.outputInstance_data]
    using decode_bits ws t b M p seeds hM hf

theorem checkedBits_valid {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length) (b M : Nat)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : forall j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 <= L) :
    checkedBits L ws t b M (ExecutableRounding.inputOf p) seeds =
      some (bits ws t b M (ExecutableRounding.inputOf p) seeds) := by
  have h : accepted L (tree ws t b M (ExecutableRounding.inputOf p) seeds) = true :=
    (instanceOf ws t b M p seeds hM hF).property
  simp [checkedBits, h]

end PvNP.RealizableHardness.ExecutablePipeline
