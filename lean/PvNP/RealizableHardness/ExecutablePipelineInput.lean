import PvNP.RealizableHardness.ExecutablePipeline
import Complexitylib.Encoding.Pairing
import Mathlib.Tactic.FinCases

/-! Uncompiled binary input and paired-coin parser for ExecutablePipeline.
No FP or polynomial coin-ruler theorem is asserted. -/
namespace PvNP.RealizableHardness.ExecutablePipelineInput
open CMMSACodec CMMSAEncoding
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Deterministic finite input; no output identity or arithmetic-validity oracle. -/
structure Input where
  weights : List Rat
  source : FiniteSourceSampler.Table weights.length
  parameters : ExecutableRounding.InputParameters
  precision : Nat
  trials : Nat

/-- Sign tag plus the existing unsigned fraction codec, including negative raw scalars. -/
def signedTree (q : Rat) : Tree :=
  .node (if q < 0 then .node .leaf .leaf else .leaf) (ratTree q)

def readSigned : Tree → Option Rat
  | .node .leaf t => readRat t
  | .node (.node .leaf .leaf) t => (fun q => -q) <$> readRat t
  | _ => none

theorem read_ratTree_abs (q : Rat) : readRat (ratTree q) = some |q| := by
  have hn : (q.num.natAbs : Rat) = |(q.num : Rat)| := by simp
  have hd : (0 : Rat) < q.den := by exact_mod_cast q.den_pos
  have he : |(q.num : Rat)| / (q.den : Rat) = |q| := by
    calc
      _ = |(q.num : Rat)| / |(q.den : Rat)| := by rw [abs_of_pos hd]
      _ = |(q.num : Rat) / (q.den : Rat)| := (abs_div _ _).symm
      _ = |q| := congrArg abs (Rat.num_div_den q)
  simp [ratTree, readRat, q.den_ne_zero, hn, he]

@[simp] theorem read_signedTree (q : Rat) : readSigned (signedTree q) = some q := by
  by_cases h : q < 0
  · simp [signedTree, h, readSigned, read_ratTree_abs, abs_of_neg h]
  · simp [signedTree, h, readSigned, read_ratTree_abs, abs_of_nonneg (le_of_not_gt h)]

def rowTree {N : Nat} (row : FiniteSourceSampler.Row N) : Tree :=
  .node (signedTree row.1) (formulaTree row.2)

def readRow (N : Nat) : Tree → Option (FiniteSourceSampler.Row N)
  | .node p f => do
      let probability ← readSigned p
      let formula ← readFormula N f
      pure (probability, formula)
  | _ => none

@[simp] theorem read_rowTree {N : Nat} (row : FiniteSourceSampler.Row N) :
    readRow N (rowTree row) = some row := by
  rcases row with ⟨p,f⟩
  simp [rowTree, readRow]

def parameterTree (q : ExecutableRounding.InputParameters) : Tree :=
  .node (signedTree q.s) (.node (signedTree q.eps)
    (.node (signedTree q.gam) (natTree q.sig)))

def readParameters : Tree → Option ExecutableRounding.InputParameters
  | .node s (.node e (.node g k)) => do
      let s ← readSigned s
      let e ← readSigned e
      let g ← readSigned g
      let k ← readNat k
      pure ⟨s,e,g,k⟩
  | _ => none

@[simp] theorem read_parameterTree (q : ExecutableRounding.InputParameters) :
    readParameters (parameterTree q) = some q := by
  cases q
  simp [parameterTree, readParameters]

/-- Fixed framing: weights, source rows, parameters, precision, trial count. -/
def inputTree (x : Input) : Tree :=
  .node (listTree (x.weights.map signedTree))
    (.node (listTree (x.source.rows.map rowTree))
      (.node (parameterTree x.parameters) (.node (natTree x.precision) (natTree x.trials))))

def readInput : Tree → Option Input
  | .node ws (.node rows (.node q (.node b m))) => do
      let weights ← readList readSigned ws
      let rows ← readList (readRow weights.length) rows
      let source ← FiniteSourceSampler.readTable rows
      let parameters ← readParameters q
      let precision ← readNat b
      let trials ← readNat m
      pure ⟨weights,source,parameters,precision,trials⟩
  | _ => none

@[simp] theorem read_inputTree (x : Input) : readInput (inputTree x) = some x := by
  cases x with
  | mk weights source parameters precision trials =>
      have hw := readList_map signedTree readSigned weights (fun q _ => read_signedTree q)
      have hr := readList_map rowTree (readRow weights.length) source.rows
        (fun row _ => read_rowTree row)
      simp only [inputTree, readInput, hw]
      change (do
        let rows ← readList (readRow weights.length) (listTree (source.rows.map rowTree))
        let source ← FiniteSourceSampler.readTable rows
        let parameters ← readParameters (parameterTree parameters)
        let precision ← readNat (natTree precision)
        let trials ← readNat (natTree trials)
        pure (Input.mk weights source parameters precision trials)) = _
      rw [hr]
      simp [FiniteSourceSampler.readTable_valid]

def encodeInput (x : Input) : Bits := Tree.encode (inputTree x)

/-- Reject malformed tree syntax, trailing input bits, fields and source validation failures. -/
def decodeInput (bs : Bits) : Option Input := do
  let (tree, rest) ← Tree.parse (bs.length+1) bs
  if rest = [] then readInput tree else none

@[simp] theorem decode_encodeInput (x : Input) : decodeInput (encodeInput x) = some x := by
  have hp := Tree.parse_encode (inputTree x) [] ((encodeInput x).length+1)
    (Nat.le_trans (Tree.depth_le_length _) (Nat.le_succ _))
  simp only [List.append_nil] at hp
  simp [decodeInput, encodeInput] at hp ⊢
  rw [hp]
  simp

theorem decodeInput_bad_fields (bs : Bits) (t : Tree)
    (hp : Tree.parse (bs.length+1) bs = some (t,[])) (hr : readInput t = none) :
    decodeInput bs = none := by simp [decodeInput,hp,hr]

theorem decodeInput_trailing (bs rest : Bits) (t : Tree)
    (hp : Tree.parse (bs.length+1) bs = some (t,rest)) (hr : rest ≠ []) :
    decodeInput bs = none := by simp [decodeInput,hp,hr]

@[simp] theorem decodeInput_empty : decodeInput [] = none := rfl

def boolDigit (b : Bool) : Fin 2 := if b then 1 else 0

def digitBool (d : Fin 2) : Bool := d == 1

@[simp] theorem digit_roundtrip (d : Fin 2) : boolDigit (digitBool d) = d := by
  fin_cases d <;> rfl

/-- Row-major flat coin tape. The existing machine interface pairs it with deterministic input. -/
def coinBits {M b : Nat} (seeds : JointSamplingLaw.SeedArray M b) : Bits :=
  List.ofFn (fun j : Fin (M*b) =>
    digitBool (seeds (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))

@[simp] theorem coinBits_length {M b : Nat} (seeds : JointSamplingLaw.SeedArray M b) :
    (coinBits seeds).length = M*b := by simp [coinBits]

def seedsOf (M b : Nat) (coins : Bits) (h : coins.length = M*b) :
    JointSamplingLaw.SeedArray M b := fun i j =>
  boolDigit (coins.get ⟨(finProdFinEquiv (i,j)).val, by
    rw [h]
    exact (finProdFinEquiv (i,j)).isLt⟩)

theorem seedsOf_coinBits {M b : Nat} (seeds : JointSamplingLaw.SeedArray M b) :
    seedsOf M b (coinBits seeds) (coinBits_length seeds) = seeds := by
  funext i j
  simp only [seedsOf, coinBits, List.get_ofFn]
  change boolDigit (digitBool (seeds
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)) = seeds i j
  rw [Equiv.symm_apply_apply, digit_roundtrip]

/-- No input proof is supplied by callers; source and seed validation are executed. -/
def runOption (L : Nat) (instanceBits coins : Bits) : Option Bits := do
  let x ← decodeInput instanceBits
  if h : coins.length = x.trials*x.precision then
    ExecutablePipeline.checkedBits L x.weights x.source x.precision x.trials x.parameters
      (seedsOf x.trials x.precision coins h)
  else none

theorem runOption_roundtrip (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    runOption L (encodeInput x) (coinBits seeds) =
      ExecutablePipeline.checkedBits L x.weights x.source x.precision x.trials x.parameters seeds := by
  simp [runOption, seedsOf_coinBits]

theorem runOption_wrong_coins (L : Nat) (x : Input) (coins : Bits)
    (h : coins.length ≠ x.trials*x.precision) :
    runOption L (encodeInput x) coins = none := by simp [runOption,h]

theorem runOption_bad_input (L : Nat) (instanceBits coins : Bits)
    (h : decodeInput instanceBits = none) : runOption L instanceBits coins = none := by
  simp [runOption,h]

/-- Same pair/unpair convention as RandomizedReduction.SeededMap.apply.
All parse or output-validation failures produce the explicit empty output tape. -/
def run (L : Nat) (z : Bits) : Bits :=
  (runOption L (Complexity.pairFst z) (Complexity.pairSnd z)).getD []

theorem run_pair (L : Nat) (x : Input)
    (seeds : JointSamplingLaw.SeedArray x.trials x.precision) :
    run L (Complexity.pair (encodeInput x) (coinBits seeds)) =
      (ExecutablePipeline.checkedBits L x.weights x.source x.precision x.trials
        x.parameters seeds).getD [] := by
  simp [run,runOption_roundtrip]

/-- For valid arithmetic and leaf-bounded source rows, the parser reaches exactly
the accepted full per-seed binary constructor, rather than only an equal record. -/
theorem run_valid {L : Nat} (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (b M : Nat) (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray M b) (hM : 0 < M)
    (hF : ∀ j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 ≤ L) :
    run L (Complexity.pair (encodeInput ⟨ws,t,ExecutableRounding.inputOf p,b,M⟩)
      (coinBits seeds)) = ExecutablePipeline.bits ws t b M (ExecutableRounding.inputOf p) seeds := by
  rw [run_pair]
  simp only [ExecutablePipeline.checkedBits_valid ws t b M p seeds hM hF, Option.getD_some]

theorem readInput_empty_rows (ws : List Rat) (q b m : Tree) :
    readInput (.node (listTree (ws.map signedTree)) (.node .leaf (.node q (.node b m)))) = none := by
  have hw := readList_map signedTree readSigned ws (fun q _ => read_signedTree q)
  simp [readInput,hw,readList,FiniteSourceSampler.readTable,FiniteSourceSampler.ValidRows]

theorem readSigned_zero_denominator (negative : Bool) (n : Nat) :
    readSigned (.node (if negative then .node .leaf .leaf else .leaf)
      (.node (natTree n) (natTree 0))) = none := by
  cases negative <;> simp [readSigned,readRat]

theorem readRow_bad_variable (N k : Nat) (q : Rat) (hk : N ≤ k) :
    readRow N (.node (signedTree q) (.node .leaf (natTree k))) = none := by
  simp [readRow,readFormula,show ¬k<N by omega]

@[simp] theorem coinBits_zero_trials (b : Nat) (seeds : JointSamplingLaw.SeedArray 0 b) :
    coinBits seeds = [] := by simp [coinBits]

@[simp] theorem coinBits_zero_precision (M : Nat) (seeds : JointSamplingLaw.SeedArray M 0) :
    coinBits seeds = [] := by simp [coinBits]

end PvNP.RealizableHardness.ExecutablePipelineInput
