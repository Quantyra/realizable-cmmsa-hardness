import PvNP.RealizableHardness.ActualOccurrenceUnaryCodec
import Complexitylib.Classes.PCP.Internal.AlgFamily
import Mathlib.Tactic

/-! A concrete fixed-arity state machine for unary scanning, source-slot
scanning, and row-by-row output emission. The latter currently consumes the
captured semantic occurrence producer; this file deliberately does not claim
that the semantic producer has yet been compiled into Cobham primitives. -/
namespace PvNP.RealizableHardness.ActualOccurrenceBoundedRuntime

open ActualOccurrenceUnaryCodec
open ActualNumberedOccurrenceProducer
open BooleanParityInput
open Complexity

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The fixed polynomial parameter used by the captured family algorithm. -/
def rotationPolynomial : Polynomial Nat := 2 * Polynomial.X

/-- The fit-level bound is supplied by the chosen finite base itself. Since
`eval (2X) n = 2*n`, this discharges the `famRotFn_eq` precondition without a
runtime caller hypothesis. -/
theorem rotation_fitLevel_le (n : Nat) :
    Complexity.algBase.fitLevel Complexity.one_lt_algBase_deg n <=
      rotationPolynomial.eval n := by
  simpa [rotationPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] using
      (Complexity.algBase.fitLevel_le Complexity.one_lt_algBase_deg n)

/-- The literal fixed-family string program called by the bounded producer.
The input tuple is unary `(n,v,i)` under the library pair encoding. -/
def familyRotationProgram : List Bool -> List Bool :=
  Complexity.algBase.famRotFn rotationPolynomial

theorem familyRotationProgram_mem_FP : familyRotationProgram \u2208 FP := by
  exact Complexity.FinBase.famRotFn_mem_FP Complexity.algBase rotationPolynomial

/-- The encoded call returns the numeral encoding of the pinned family's
rotation value for every positive cloud size. -/
theorem familyRotationProgram_eq (n v i : Nat) (hn : 0 < n) :
    familyRotationProgram
        (pair (List.replicate n true)
          (pair (List.replicate v true) (List.replicate i true))) =
      pair
        (List.replicate
          (Complexity.algBase.famRotVal Complexity.one_lt_algBase_deg n (v, i)).1 true)
        (List.replicate
          (Complexity.algBase.famRotVal Complexity.one_lt_algBase_deg n (v, i)).2 true) := by
  exact Complexity.FinBase.famRotFn_eq Complexity.algBase rotationPolynomial
    Complexity.one_lt_algBase_deg n v i hn (rotation_fitLevel_le n)

inductive Phase where
  | parse
  | slotScan
  | emit
  | done
  | invalid
  deriving DecidableEq, Repr

def phaseCode : Phase -> Nat
  | .parse => 0
  | .slotScan => 1
  | .emit => 2
  | .done => 3
  | .invalid => 4

/-- The parser and producer scheduler have a fixed seven-field state.
`slotTrace` stores triples (row ordinal, coordinate ordinal, source owner).
Rows are appended in their original occurrence order, including duplicates. -/
structure State where
  phase : Phase
  unread : List Bool
  unaryCount : Nat
  decodedWords : List Nat
  slotCursor : Nat
  slotTrace : List (Nat \u00d7 Nat \u00d7 Nat)
  outputBits : List Bool
  deriving Repr

/-- A length-prefixed frame for an arbitrary bit string. -/
def frameBits (bits : List Bool) : List Bool :=
  encodeWord bits.length ++ bits

/-- A length-prefixed frame for an arbitrary natural-number vector. -/
def frameNats (ns : List Nat) : List Bool :=
  encodeWords (ns.length :: ns)

def flattenTriples (xs : List (Nat \u00d7 Nat \u00d7 Nat)) : List Nat :=
  xs.flatMap fun (r, c, v) => [r, c, v]

/-- The seven fields are framed independently, so a fixed projection boundary
does not depend on any field contents. -/
def encodeState (s : State) : List Bool :=
  encodeWord (phaseCode s.phase) ++
    frameBits s.unread ++
    encodeWord s.unaryCount ++
    frameNats s.decodedWords ++
    encodeWord s.slotCursor ++
    frameNats (flattenTriples s.slotTrace) ++
    frameBits s.outputBits

def initial (bits : List Bool) : State :=
  { phase := .parse, unread := bits, unaryCount := 0, decodedWords := [],
    slotCursor := 0, slotTrace := [], outputBits := [] }

def invalidState (s : State) : State :=
  { s with phase := .invalid, unread := [], unaryCount := 0,
    outputBits := sharedInputBits fallbackInput }

def parsedInput (s : State) : Option Input := decodeInputWords s.decodedWords

/-- Consume exactly one bit in the unary decoder. A false bit closes one
number; a true bit increments the current unary counter. -/
def parseStep (s : State) : State :=
  match s.unread with
  | true :: rest => { s with unread := rest, unaryCount := s.unaryCount + 1 }
  | false :: rest =>
      { s with unread := rest, unaryCount := 0,
        decodedWords := s.decodedWords ++ [s.unaryCount] }
  | [] =>
      if s.unaryCount != 0 then invalidState s
      else
        match parsedInput s with
        | some _ => { s with phase := .slotScan }
        | none => invalidState s

def ownerAt {n : Nat} (e : Equation (Fin n)) (coordinate : Nat) : Fin n :=
  if coordinate % 3 = 0 then e.first
  else if coordinate % 3 = 1 then e.second
  else e.third

/-- One transition scans one actual source slot. The owner field is taken from
the parsed input row at the cursor's row and coordinate ordinals. -/
def slotScanStep (s : State) : State :=
  match parsedInput s with
  | none => invalidState s
  | some input =>
      if s.slotCursor < input.equations.length * 3 then
        let rowIndex : Fin input.equations.length :=
          \u27e8s.slotCursor / 3, by omega\u27e9
        let coordinate := s.slotCursor % 3
        let row := input.equations.get rowIndex
        { s with slotCursor := s.slotCursor + 1,
          slotTrace := s.slotTrace ++
            [(rowIndex.val, coordinate, (ownerAt row coordinate).val)] }
      else
        let out := output input
        { s with phase := .emit, slotCursor := 0,
          outputBits := encodeWords [out.variables, out.equations.length] }

/-- One transition emits one complete unary-encoded output equation from the
captured row-preserving semantic producer. -/
def emitStep (s : State) : State :=
  match parsedInput s with
  | none => invalidState s
  | some input =>
      let out := output input
      if s.slotCursor < out.equations.length then
        let row := out.equations.get \u27e8s.slotCursor, by omega\u27e9
        { s with slotCursor := s.slotCursor + 1,
          outputBits := s.outputBits ++
            encodeWords (equationWords row) }
      else { s with phase := .done }

/-- The global scheduler has explicit absorbing terminal states. -/
def step (s : State) : State :=
  match s.phase with
  | .parse => parseStep s
  | .slotScan => slotScanStep s
  | .emit => emitStep s
  | .done => s
  | .invalid => s

def runSteps : Nat -> State -> State
  | 0, s => s
  | k + 1, s => runSteps k (step s)

theorem step_done_absorbing (s : State) (h : s.phase = .done) : step s = s := by
  simp [step, h]

theorem step_invalid_absorbing (s : State) (h : s.phase = .invalid) : step s = s := by
  simp [step, h]

theorem parseStep_consumes_true (s : State) (rest : List Bool)
    (h : s.unread = true :: rest) :
    (parseStep s).unread = rest \u2227
      (parseStep s).unaryCount = s.unaryCount + 1 := by
  simp [parseStep, h]

theorem parseStep_closes_word (s : State) (rest : List Bool)
    (h : s.unread = false :: rest) :
    (parseStep s).unread = rest \u2227
      (parseStep s).unaryCount = 0 \u2227
      (parseStep s).decodedWords = s.decodedWords ++ [s.unaryCount] := by
  simp [parseStep, h]

theorem slotScanStep_increments (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor < input.equations.length * 3) :
    (slotScanStep s).slotCursor = s.slotCursor + 1 := by
  simp [slotScanStep, hparsed, hcursor]

theorem slotScanStep_appends_occurrence (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor < input.equations.length * 3) :
    (slotScanStep s).slotTrace = s.slotTrace ++
      [(s.slotCursor / 3, s.slotCursor % 3,
        (ownerAt (input.equations.get \u27e8s.slotCursor / 3, by omega\u27e9)
          (s.slotCursor % 3)).val] := by
  simp [slotScanStep, hparsed, hcursor]

theorem emitStep_appends_equation (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor < (output input).equations.length) :
    (emitStep s).outputBits = s.outputBits ++
      encodeWords (equationWords ((output input).equations.get
        \u27e8s.slotCursor, by omega\u27e9)) := by
  simp [emitStep, hparsed, hcursor]

theorem terminal_states_absorb (s : State)
    (h : s.phase = .done \u2228 s.phase = .invalid) : step s = s := by
  rcases h with h | h
  · exact step_done_absorbing s h
  · exact step_invalid_absorbing s h

end
end PvNP.RealizableHardness.ActualOccurrenceBoundedRuntime

