import PvNP.RealizableHardness.CMMSAPipelineEncoding
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size

/-! UNCOMPILED source draft. Concrete finite-list repair and rounding arithmetic.
The semantic equality and wire-size scripts below await compiler verification.
No FP or Turing-machine runtime claim is made. -/
namespace PvNP.RealizableHardness.ExecutableRounding
open scoped BigOperators
open WeightRounding CMMSACodec CMMSAEncoding

/-- Explicit scalar input, with no promise or output certificate stored. -/
structure InputParameters where
  s : Rat
  eps : Rat
  gam : Rat
  sig : Nat
  deriving DecidableEq

def repairLambda (q : InputParameters) : Rat := (q.sig : Rat) * q.s / q.gam

def repairBudget (q : InputParameters) : Rat :=
  (q.s + repairLambda q * q.eps) / (1 + repairLambda q)

/-- The first block contains the original weights in list order. The second
block contains one exception coordinate for each of the M indexed formulas. -/
def repairedAt (ws : List Rat) (M : Nat) (q : InputParameters)
    (z : Fin ws.length ⊕ Fin M) : Rat :=
  Sum.elim ws.get (fun _ => repairLambda q / (M : Rat)) z / (1 + repairLambda q)

def flatRepairedAt (ws : List Rat) (M : Nat) (q : InputParameters)
    (v : Fin (ws.length + M)) : Rat := repairedAt ws M q (finSumFinEquiv.symm v)

/-- Reuse the existing executable ceiling and dyadic-logarithm arithmetic. -/
def roundingScale (ws : List Rat) (M : Nat) (q : InputParameters) : Nat :=
  dyadicScale (ws.length + M) (repairBudget q)

def numerators (ws : List Rat) (M : Nat) (q : InputParameters) : List Nat :=
  List.ofFn (fun v => coordinate (flatRepairedAt ws M q) (roundingScale ws M q) v)

def commonDenominator (ws : List Rat) (M : Nat) (q : InputParameters) : Nat :=
  (numerators ws M q).sum

/-- Clipping is performed on the computed integer numerator, before division. -/
def clippedNumerator (ws : List Rat) (M : Nat) (q : InputParameters) : Nat :=
  min (commonDenominator ws M q)
    (⌈(roundingScale ws M q : Rat) * repairBudget q⌉₊ + (ws.length + M))

def outputWeights (ws : List Rat) (M : Nat) (q : InputParameters) : List Rat :=
  (numerators ws M q).map (fun (n : Nat) => (n : Rat) / commonDenominator ws M q)

def outputBudget (ws : List Rat) (M : Nat) (q : InputParameters) : Rat :=
  (clippedNumerator ws M q : Rat) / commonDenominator ws M q

@[simp] theorem numerators_length (ws : List Rat) (M : Nat) (q : InputParameters) :
    (numerators ws M q).length = ws.length + M := by simp [numerators]

@[simp] theorem outputWeights_length (ws : List Rat) (M : Nat) (q : InputParameters) :
    (outputWeights ws M q).length = ws.length + M := by simp [outputWeights]

/-- This constructor forgets validity proofs, rather than accepting a target
output function or a certificate identifying the desired result. -/
def inputOf {ws : List Rat} (p : FiniteRepairRoundingPipeline.Parameters ws.get) : InputParameters :=
  ⟨p.s, p.eps, p.gam, p.sig⟩

variable {ws : List Rat}

@[simp] theorem lambda_eq (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    repairLambda (inputOf p) = FiniteRepairRoundingPipeline.lam p := rfl

@[simp] theorem budget_eq (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    repairBudget (inputOf p) = FiniteRepairRoundingPipeline.budget p := rfl

theorem repairedAt_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (z : Fin ws.length ⊕ Fin M) :
    repairedAt ws M (inputOf p) z = FiniteRepairRoundingPipeline.weights p z := by
  simp [repairedAt, FiniteRepairRoundingPipeline.weights, repairedWeights]

@[simp] theorem scale_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    roundingScale ws M (inputOf p) = FiniteRepairRoundingPipeline.scale (I := Fin M) p := by
  simp [roundingScale, FiniteRepairRoundingPipeline.scale]

/-- Full coordinatewise arithmetic equality, not a collection of sample checks. -/
theorem numerators_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    numerators ws M (inputOf p) = List.ofFn (fun v : Fin (ws.length + M) =>
      coordinate (FiniteRepairRoundingPipeline.weights p)
        (FiniteRepairRoundingPipeline.scale (I := Fin M) p) (finSumFinEquiv.symm v)) := by
  unfold numerators
  apply congrArg List.ofFn
  funext v
  simp only [coordinate, flatRepairedAt, repairedAt_eq, scale_eq]

theorem denominator_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    commonDenominator ws M (inputOf p) = FiniteRepairRoundingPipeline.outputDenominator (I := Fin M) p := by
  rw [commonDenominator, numerators_eq, List.sum_ofFn]
  exact finSumFinEquiv.symm.sum_comp
    (coordinate (FiniteRepairRoundingPipeline.weights p) (FiniteRepairRoundingPipeline.scale (I := Fin M) p))

theorem clippedNumerator_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    clippedNumerator ws M (inputOf p) =
      budgetNumerator (FiniteRepairRoundingPipeline.weights (I := Fin M) p)
        (FiniteRepairRoundingPipeline.scale (I := Fin M) p) (FiniteRepairRoundingPipeline.budget p) := by
  simp [clippedNumerator, denominator_eq, scale_eq, budgetNumerator,
    FiniteRepairRoundingPipeline.outputDenominator]

/-- Exact order transport into the existing flattened semantic output. -/
theorem outputWeights_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    outputWeights ws M (inputOf p) = List.ofFn (CMMSAPipelineEncoding.flatWeights (M := M) p) := by
  rw [outputWeights, numerators_eq, List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  rw [denominator_eq]
  rfl

theorem outputBudget_eq (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    outputBudget ws M (inputOf p) = FiniteRepairRoundingPipeline.outputBudget (I := Fin M) p := by
  rw [outputBudget, clippedNumerator_eq, denominator_eq]
  rfl

/-- The arithmetic fields agree with the full pipeline data, for every formula
family. Computing the formulas and their source sampler is a separate operation. -/
theorem outputData_fields (M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (F : Fin M → Formula (Fin ws.length)) :
    outputWeights ws M (inputOf p) = (CMMSAPipelineEncoding.outputData p F).weights ∧
    outputBudget ws M (inputOf p) = (CMMSAPipelineEncoding.outputData p F).budget := by
  exact ⟨outputWeights_eq M p, outputBudget_eq M p⟩

/-- Original and exception coordinates retain their explicit positions. -/
theorem original_repairedAt (ws : List Rat) (M : Nat) (q : InputParameters) (v : Fin ws.length) :
    flatRepairedAt ws M q (finSumFinEquiv (Sum.inl v)) = ws.get v / (1 + repairLambda q) := by
  simp [flatRepairedAt, repairedAt]

theorem exception_repairedAt (ws : List Rat) (M : Nat) (q : InputParameters) (i : Fin M) :
    flatRepairedAt ws M q (finSumFinEquiv (Sum.inr i)) =
      (repairLambda q / (M : Rat)) / (1 + repairLambda q) := by
  simp [flatRepairedAt, repairedAt]

/-- Raw common-denominator magnitude bound inherited through proved equality. -/
theorem denominator_bound (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) (P Q : Nat)
    (hP : 1 / p.s ≤ (P : Rat)) (hQ : (p.sig : Rat) / p.gam ≤ (Q : Rat)) :
    commonDenominator ws M (inputOf p) ≤
      16 * (ws.length + M + 1) * (P + Q) + (ws.length + M) := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  rw [denominator_eq]
  simpa using FiniteRepairRoundingPipeline.denominator_bound (I := Fin M) p P Q hP hQ

theorem positive_integer_data (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    0 < commonDenominator ws M (inputOf p) ∧
    (∀ n ∈ numerators ws M (inputOf p), 0 < n ∧ n ≤ commonDenominator ws M (inputOf p)) ∧
    (0 < clippedNumerator ws M (inputOf p) ∧
      clippedNumerator ws M (inputOf p) ≤ commonDenominator ws M (inputOf p)) := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have h := FiniteRepairRoundingPipeline.output_common_denominator (I := Fin M) p
  rw [denominator_eq, clippedNumerator_eq, numerators_eq]
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1⟩
  intro n hn
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hn
  exact ⟨(h.2.1 (finSumFinEquiv.symm v)).1, (h.2.1 (finSumFinEquiv.symm v)).2.1⟩

/-- Serialize the computed common-denominator representation directly. The
codec accepts positive unreduced fractions, so no canonicalization bound is hidden. -/
def fractionTree (n d : Nat) : Tree := .node (natTree n) (natTree d)

@[simp] theorem read_fractionTree (n d : Nat) (hd : 0 < d) :
    readRat (fractionTree n d) = some ((n : Rat) / d) := by
  simp [fractionTree, readRat, Nat.ne_of_gt hd]

theorem fractionTree_length (n d B : Nat) (hn : n ≤ B) (hd : d ≤ B) :
    (Tree.encode (fractionTree n d)).length ≤ 8*B.size+3 := by
  have h1 := natTree_length n
  have h2 := natTree_length d
  have hn' := Nat.size_le_size hn
  have hd' := Nat.size_le_size hd
  simp only [fractionTree, Tree.encode, List.length_cons, List.length_append]
  omega

def weightTree (ws : List Rat) (M : Nat) (q : InputParameters) : Tree :=
  listTree ((numerators ws M q).map (fun n => fractionTree n (commonDenominator ws M q)))

def budgetTree (ws : List Rat) (M : Nat) (q : InputParameters) : Tree :=
  fractionTree (clippedNumerator ws M q) (commonDenominator ws M q)

theorem read_weightTree (ws : List Rat) (M : Nat) (q : InputParameters)
    (hd : 0 < commonDenominator ws M q) :
    readList readRat (weightTree ws M q) = some (outputWeights ws M q) := by
  unfold weightTree outputWeights
  induction numerators ws M q with
  | nil => rfl
  | cons n ns ih => simp [listTree, readList, read_fractionTree n _ hd, ih]

@[simp] theorem read_budgetTree (ws : List Rat) (M : Nat) (q : InputParameters)
    (hd : 0 < commonDenominator ws M q) :
    readRat (budgetTree ws M q) = some (outputBudget ws M q) := by
  exact read_fractionTree _ _ hd

lemma listTree_length_bound (ts : List Tree) (B : Nat)
    (h : ∀ t ∈ ts, (Tree.encode t).length ≤ B) :
    (Tree.encode (listTree ts)).length ≤ ts.length * (B+1) + 1 := by
  induction ts with
  | nil => simp [listTree, Tree.encode]
  | cons t ts ih =>
      have ht := h t (by simp)
      have hh := ih (fun u hu => h u (by simp [hu]))
      simp only [listTree, Tree.encode, List.length_cons, List.length_append]
      nlinarith

/-- Actual wire bound for the rounded-weight list and the clipped budget.
This is an output-size theorem; it does not measure the computation time. -/
theorem arithmetic_wire_bound (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) (P Q : Nat)
    (hP : 1 / p.s ≤ (P : Rat)) (hQ : (p.sig : Rat) / p.gam ≤ (Q : Rat)) :
    let B := 16 * (ws.length + M + 1) * (P + Q) + (ws.length + M)
    (Tree.encode (weightTree ws M (inputOf p))).length ≤
      (ws.length + M) * (8*B.size+4) + 1 ∧
    (Tree.encode (budgetTree ws M (inputOf p))).length ≤ 8*B.size+3 := by
  dsimp only
  let B := 16 * (ws.length + M + 1) * (P + Q) + (ws.length + M)
  have hd : commonDenominator ws M (inputOf p) ≤ B := denominator_bound M hM p P Q hP hQ
  have hi := positive_integer_data M hM p
  constructor
  · have h := listTree_length_bound
      ((numerators ws M (inputOf p)).map (fun n => fractionTree n (commonDenominator ws M (inputOf p))))
      (8*B.size+3) (by
        intro t ht
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ht
        exact fractionTree_length _ _ B ((hi.2.1 n hn).2.trans hd) hd)
    simpa [weightTree] using h
  · exact fractionTree_length _ _ B (hi.2.2.2.trans hd) hd

/-- Positive rational inputs give a reciprocal bound directly from their
stored denominator, without a supplied asymptotic or output-size certificate. -/
lemma inverse_le_denominator (q : Rat) (hq : 0 < q) : 1 / q ≤ (q.den : Rat) := by
  have hn : (1 : Int) ≤ q.num := by have := Rat.num_pos.mpr hq; omega
  have hnq : (1 : Rat) ≤ (q.num : Rat) := by exact_mod_cast hn
  have hd : (q.den : Rat) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have he : q * (q.den : Rat) = (q.num : Rat) := by
    calc
      _ = ((q.num : Rat) / (q.den : Rat)) * (q.den : Rat) :=
        congrArg (fun x : Rat => x * (q.den : Rat)) (Rat.num_div_den q).symm
      _ = _ := div_mul_cancel₀ _ hd
  apply (div_le_iff₀ hq).mpr
  nlinarith

/-- Numeric bound calculated only from the explicit scalar input and list sizes. -/
def inputMagnitudeBound (ws : List Rat) (M : Nat) (q : InputParameters) : Nat :=
  16 * (ws.length + M + 1) * (q.s.den + q.sig * q.gam.den) + (ws.length + M)

theorem input_denominator_bound (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    commonDenominator ws M (inputOf p) ≤ inputMagnitudeBound ws M (inputOf p) := by
  apply denominator_bound M hM p p.s.den (p.sig * p.gam.den)
    (inverse_le_denominator p.s p.s_pos)
  have h := mul_le_mul_of_nonneg_left (inverse_le_denominator p.gam p.gam_pos)
    (Nat.cast_nonneg p.sig : (0 : Rat) ≤ p.sig)
  simpa only [mul_one_div, Nat.cast_mul] using h

/-- Binary wire length for the actual arithmetic output from explicit input
magnitudes. No reciprocal-budget bound is an extra hypothesis here. -/
theorem input_arithmetic_wire_bound (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    let B := inputMagnitudeBound ws M (inputOf p)
    (Tree.encode (weightTree ws M (inputOf p))).length ≤
      (ws.length + M) * (8*B.size+4) + 1 ∧
    (Tree.encode (budgetTree ws M (inputOf p))).length ≤ 8*B.size+3 := by
  apply arithmetic_wire_bound M hM p p.s.den (p.sig * p.gam.den)
    (inverse_le_denominator p.s p.s_pos)
  have h := mul_le_mul_of_nonneg_left (inverse_le_denominator p.gam p.gam_pos)
    (Nat.cast_nonneg p.sig : (0 : Rat) ≤ p.sig)
  simpa only [mul_one_div, Nat.cast_mul] using h

/-- The emitted arithmetic fragments decode to the exact semantic fields. -/
theorem read_semantic_fields (M : Nat) (hM : 0 < M)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get) :
    readList readRat (weightTree ws M (inputOf p)) =
      some (List.ofFn (CMMSAPipelineEncoding.flatWeights (M := M) p)) ∧
    readRat (budgetTree ws M (inputOf p)) =
      some (FiniteRepairRoundingPipeline.outputBudget (I := Fin M) p) := by
  have hd := (positive_integer_data M hM p).1
  rw [read_weightTree _ _ _ hd, read_budgetTree _ _ _ hd, outputWeights_eq, outputBudget_eq]
  exact ⟨rfl, rfl⟩

end PvNP.RealizableHardness.ExecutableRounding
