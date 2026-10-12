import PvNP.RealizableHardness.ActualOccurrenceUnaryCodec
import Complexitylib.Classes.PCP.Internal.AlgFamily
import Mathlib.Tactic

/-! A concrete fixed-arity state machine for unary scanning, ordered source-slot
scanning, owner-prefix occurrence enumeration, and port-tag enumeration. It
does not call the semantic output producer. -/
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

theorem familyRotationProgram_mem_FP : familyRotationProgram ∈ FP := by
  exact Complexity.FinBase.famRotFn_mem_FP Complexity.algBase rotationPolynomial

/-- The same fixed family subroutine can be inserted into the Cobham
composition used by a future bounded iterator. This certifies the subroutine
only, not the transition loop or the complete producer. -/
theorem familyRotationProgram_mem_CobhamFP :
    Complexity.Cobham familyRotationProgram := by
  exact Complexity.FP_subset_CobhamFP familyRotationProgram_mem_FP

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

def familyRotationValue (n v i : Nat) : Nat × Nat :=
  let encoded := familyRotationProgram
    (pair (List.replicate n true)
      (pair (List.replicate v true) (List.replicate i true)))
  ((pairFst encoded).length, (pairSnd encoded).length)

theorem familyRotationValue_eq (n v i : Nat) (hn : 0 < n) :
    familyRotationValue n v i =
      Complexity.algBase.famRotVal Complexity.one_lt_algBase_deg n (v, i) := by
  unfold familyRotationValue
  rw [familyRotationProgram_eq n v i hn]
  simp

def cloudDegree : Nat := FixedPortCycleFamily.predecessor + 1

def portRank (v j : Nat) : Nat := j + cloudDegree * v

def reverseDart (n v j d : Nat) : Nat × Nat × Nat :=
  if d = 0 then
    let q := familyRotationValue n v j
    (q.1, q.2, 0)
  else if d = 1 then
    (v, (j + 1) % cloudDegree, 2)
  else
    (v, (j + cloudDegree - 1) % cloudDegree, 1)

def selectedDart (n cursor : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  let q := cursor / 3
  let v := q / cloudDegree
  let j := q % cloudDegree
  let d := cursor % 3
  let (w, k, e) := reverseDart n v j d
  if portRank v j < portRank w k then [(v, j, d, w, k, e)] else []

inductive Phase where
  | parse
  | slotScan
  | ownerScan
  | portTags
  | cloudDarts
  | internalTags
  | tagsComplete
  | invalid
  deriving DecidableEq, Repr

def phaseCode : Phase -> Nat
  | .parse => 0
  | .slotScan => 1
  | .ownerScan => 2
  | .portTags => 3
  | .cloudDarts => 4
  | .internalTags => 5
  | .tagsComplete => 6
  | .invalid => 7

/-- The parser and producer scheduler have a fixed eighteen-field state.
`slotTrace` stores triples (row ordinal, coordinate ordinal, source owner);
each `ownerSlotLists` entry stores source slot ordinals in their actual order;
`variableTags` stores four-word finite tags. -/
structure State where
  phase : Phase
  unread : List Bool
  unaryCount : Nat
  decodedWords : List Nat
  slotCursor : Nat
  slotTrace : List (Nat × Nat × Nat)
  ownerCursor : Nat
  ownerScanCursor : Nat
  ownerSizes : List Nat
  ownerSlotAcc : List Nat
  ownerSlotLists : List (List Nat)
  portOccurrenceCursor : Nat
  portLabelCursor : Nat
  variableTags : List (Nat × Nat × Nat × Nat)
  cloudRepAcc : List (Nat × Nat × Nat × Nat × Nat × Nat)
  representativeClouds : List (List (Nat × Nat × Nat × Nat × Nat × Nat))
  edgeOccurrenceCursor : Nat
  internalLabelCursor : Nat
  deriving Repr

/-- A bounded one-tag-at-a-time lookup over the exact emitted variable order.
`found` records the first index; uniqueness of the generated tag list makes it
the only index. -/
structure TagLookupState where
  tags : List (Nat × Nat × Nat × Nat)
  target : Nat × Nat × Nat × Nat
  cursor : Nat
  found : Option Nat
  complete : Bool
  deriving Repr

def encodeTag (tag : Nat × Nat × Nat × Nat) : List Bool :=
  let (kind, owner, ordinal, label) := tag
  encodeWords [kind, owner, ordinal, label]

def encodeTagLookupState (s : TagLookupState) : List Bool :=
  frameNatLists (s.tags.map fun t =>
    let (kind, owner, ordinal, label) := t
    [kind, owner, ordinal, label]) ++
    encodeTag s.target ++
    encodeWord s.cursor ++
    encodeWords [if s.found.isSome then 1 else 0, s.found.getD 0,
      if s.complete then 1 else 0]

def tagLookupStep (s : TagLookupState) : TagLookupState :=
  if s.complete then s
  else if s.cursor < s.tags.length then
    let candidate := s.tags.get ⟨s.cursor, by omega⟩
    if candidate = s.target then
      { s with found := some s.cursor, complete := true }
    else { s with cursor := s.cursor + 1 }
  else { s with complete := true }

theorem tagLookupStep_finds_current (s : TagLookupState)
    (hcomplete : s.complete = false)
    (hcursor : s.cursor < s.tags.length)
    (heq : s.tags.get ⟨s.cursor, by omega⟩ = s.target) :
    (tagLookupStep s).found = some s.cursor ∧
      (tagLookupStep s).complete = true := by
  simp [tagLookupStep, hcomplete, hcursor, heq]

theorem tagLookupStep_skips_current (s : TagLookupState)
    (hcomplete : s.complete = false)
    (hcursor : s.cursor < s.tags.length)
    (hne : s.tags.get ⟨s.cursor, by omega⟩ ≠ s.target) :
    (tagLookupStep s).cursor = s.cursor + 1 := by
  simp [tagLookupStep, hcomplete, hcursor, hne]

theorem tagLookupStep_complete_absorbing (s : TagLookupState)
    (hcomplete : s.complete = true) : tagLookupStep s = s := by
  simp [tagLookupStep, hcomplete]

/-- A length-prefixed frame for an arbitrary bit string. -/
def frameBits (bits : List Bool) : List Bool :=
  encodeWord bits.length ++ bits

/-- A length-prefixed frame for an arbitrary natural-number vector. -/
def frameNats (ns : List Nat) : List Bool :=
  encodeWords (ns.length :: ns)

def flattenTriples (xs : List (Nat × Nat × Nat)) : List Nat :=
  xs.flatMap fun (r, c, v) => [r, c, v]

def frameNatLists (xs : List (List Nat)) : List Bool :=
  encodeWords (xs.length :: xs.flatMap fun x => x.length :: x)

def flattenTags (xs : List (Nat × Nat × Nat × Nat)) : List Nat :=
  xs.flatMap fun (kind, owner, ordinal, label) => [kind, owner, ordinal, label]

def flattenDarts (xs : List (Nat × Nat × Nat × Nat × Nat × Nat)) : List Nat :=
  xs.flatMap fun (v, j, d, w, k, e) => [v, j, d, w, k, e]

def frameDartClouds (xs : List (List (Nat × Nat × Nat × Nat × Nat × Nat))) : List Bool :=
  encodeWords (xs.length :: xs.flatMap fun cloud =>
    cloud.length :: flattenDarts cloud)

/-- The eighteen fields are framed independently, so a fixed projection boundary
does not depend on any field contents. -/
def encodeState (s : State) : List Bool :=
  encodeWord (phaseCode s.phase) ++
    frameBits s.unread ++
    encodeWord s.unaryCount ++
    frameNats s.decodedWords ++
    encodeWord s.slotCursor ++
    frameNats (flattenTriples s.slotTrace) ++
    encodeWord s.ownerCursor ++
    encodeWord s.ownerScanCursor ++
    frameNats s.ownerSizes ++
    frameNats s.ownerSlotAcc ++
    frameNatLists s.ownerSlotLists ++
    encodeWord s.portOccurrenceCursor ++
    encodeWord s.portLabelCursor ++
    frameNats (flattenTags s.variableTags) ++
    frameNats (flattenDarts s.cloudRepAcc) ++
    frameDartClouds s.representativeClouds ++
    encodeWord s.edgeOccurrenceCursor ++
    encodeWord s.internalLabelCursor

def initial (bits : List Bool) : State :=
  { phase := .parse, unread := bits, unaryCount := 0, decodedWords := [],
    slotCursor := 0, slotTrace := [], ownerCursor := 0, ownerScanCursor := 0,
    ownerSizes := [], ownerSlotAcc := [], ownerSlotLists := [],
    portOccurrenceCursor := 0, portLabelCursor := 0, variableTags := [],
    cloudRepAcc := [], representativeClouds := [], edgeOccurrenceCursor := 0,
    internalLabelCursor := 0 }

def invalidState (s : State) : State :=
  { s with phase := .invalid, unread := [], unaryCount := 0 }

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
          ⟨s.slotCursor / 3, by omega⟩
        let coordinate := s.slotCursor % 3
        let row := input.equations.get rowIndex
        { s with slotCursor := s.slotCursor + 1,
          slotTrace := s.slotTrace ++
            [(rowIndex.val, coordinate, (ownerAt row coordinate).val)] }
      else
        { s with phase := .ownerScan, slotCursor := 0,
          ownerCursor := 0, ownerScanCursor := 0,
          ownerSizes := [], ownerSlotAcc := [], ownerSlotLists := [] }

/-- Scan the recorded source-slot stream once for the current owner. This is
the literal owner-prefix occurrence order: the inner cursor walks the original
row-major slot trace and retains exactly matching owner entries. -/
def ownerScanStep (s : State) : State :=
  match parsedInput s with
  | none => invalidState s
  | some input =>
      if s.ownerCursor < input.variables then
        if s.ownerScanCursor < s.slotTrace.length then
          let (r, c, v) := s.slotTrace.get ⟨s.ownerScanCursor, by omega⟩
          let nextAcc := if v = s.ownerCursor then
              s.ownerSlotAcc ++ [3 * r + c]
            else s.ownerSlotAcc
          { s with ownerScanCursor := s.ownerScanCursor + 1,
            ownerSlotAcc := nextAcc }
        else
          { s with ownerCursor := s.ownerCursor + 1,
            ownerScanCursor := 0,
            ownerSizes := s.ownerSizes ++ [s.ownerSlotAcc.length],
            ownerSlotLists := s.ownerSlotLists ++ [s.ownerSlotAcc],
            ownerSlotAcc := [] }
      else
        { s with phase := .portTags, ownerCursor := 0,
          portOccurrenceCursor := 0, portLabelCursor := 0 }

/-- Enumerate each owner's port variables in occurrence ordinal, then local
port-label order. Tag code 0 denotes a port tag `(owner, occurrence, label)`.
The finite label range is the fixed base degree and each call appends one tag. -/
def portTagStep (s : State) : State :=
  match parsedInput s with
  | none => invalidState s
  | some input =>
      if s.ownerCursor < input.variables then
        if s.ownerCursor < s.ownerSlotLists.length then
          let occurrences := s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩
          if s.portOccurrenceCursor < occurrences.length then
            if s.portLabelCursor < FixedPortCycleFamily.predecessor + 1 then
              { s with portLabelCursor := s.portLabelCursor + 1,
                variableTags := s.variableTags ++
                  [(0, s.ownerCursor, s.portOccurrenceCursor, s.portLabelCursor)] }
            else
              { s with portOccurrenceCursor := s.portOccurrenceCursor + 1,
                portLabelCursor := 0 }
          else
            { s with phase := .cloudDarts, ownerScanCursor := 0,
              cloudRepAcc := [], edgeOccurrenceCursor := 0,
              internalLabelCursor := 0 }
        else
          invalidState s
      else { s with phase := .tagsComplete }

/-- Scan the exact row-major `(vertex, port, dart)` product. The external dart
calls the fixed family string program; the two cycle darts use their explicit
modular successor and predecessor. -/
def cloudDartsStep (s : State) : State :=
  match parsedInput s with
  | none => invalidState s
  | some input =>
      if s.ownerCursor < input.variables then
        if s.ownerCursor < s.ownerSizes.length then
          let n := s.ownerSizes.get ⟨s.ownerCursor, by omega⟩
          if s.ownerScanCursor < n * cloudDegree * 3 then
            { s with ownerScanCursor := s.ownerScanCursor + 1,
              cloudRepAcc := s.cloudRepAcc ++ selectedDart n s.ownerScanCursor }
          else
            { s with phase := .internalTags, edgeOccurrenceCursor := 0,
              internalLabelCursor := 0 }
        else
          invalidState s
      else { s with phase := .tagsComplete }

/-- Append the five fresh internal tags for each representative dart in its
enumerated edge order. The current cloud's exact representatives are retained
for later row generation. -/
def internalTagStep (s : State) : State :=
  match parsedInput s with
  | none => invalidState s
  | some input =>
      if s.ownerCursor < input.variables then
        if s.edgeOccurrenceCursor < s.cloudRepAcc.length then
          if s.internalLabelCursor < 5 then
            { s with internalLabelCursor := s.internalLabelCursor + 1,
              variableTags := s.variableTags ++
                [(1, s.ownerCursor, s.edgeOccurrenceCursor, s.internalLabelCursor)] }
          else
            { s with edgeOccurrenceCursor := s.edgeOccurrenceCursor + 1,
              internalLabelCursor := 0 }
        else
          { s with phase := .portTags, ownerCursor := s.ownerCursor + 1,
            portOccurrenceCursor := 0, portLabelCursor := 0,
            ownerScanCursor := 0,
            representativeClouds := s.representativeClouds ++ [s.cloudRepAcc],
            cloudRepAcc := [], edgeOccurrenceCursor := 0,
            internalLabelCursor := 0 }
      else { s with phase := .tagsComplete }

/-- The global scheduler has explicit absorbing terminal states. -/
def step (s : State) : State :=
  match s.phase with
  | .parse => parseStep s
  | .slotScan => slotScanStep s
  | .ownerScan => ownerScanStep s
  | .portTags => portTagStep s
  | .cloudDarts => cloudDartsStep s
  | .internalTags => internalTagStep s
  | .tagsComplete => s
  | .invalid => s

def runSteps : Nat -> State -> State
  | 0, s => s
  | k + 1, s => runSteps k (step s)

theorem step_tagsComplete_absorbing (s : State) (h : s.phase = .tagsComplete) :
    step s = s := by
  simp [step, h]

theorem step_invalid_absorbing (s : State) (h : s.phase = .invalid) : step s = s := by
  simp [step, h]

theorem parseStep_consumes_true (s : State) (rest : List Bool)
    (h : s.unread = true :: rest) :
    (parseStep s).unread = rest ∧
      (parseStep s).unaryCount = s.unaryCount + 1 := by
  simp [parseStep, h]

theorem parseStep_closes_word (s : State) (rest : List Bool)
    (h : s.unread = false :: rest) :
    (parseStep s).unread = rest ∧
      (parseStep s).unaryCount = 0 ∧
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
        (ownerAt (input.equations.get ⟨s.slotCursor / 3, by omega⟩)
          (s.slotCursor % 3)).val] := by
  simp [slotScanStep, hparsed, hcursor]

theorem ownerScanStep_increments (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor < s.slotTrace.length) :
    (ownerScanStep s).ownerScanCursor = s.ownerScanCursor + 1 := by
  simp [ownerScanStep, hparsed, howner, hcursor]

theorem portTagStep_appends_exact_tag (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hlist : s.ownerCursor < s.ownerSlotLists.length)
    (hocc : s.portOccurrenceCursor <
      (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length)
    (hlabel : s.portLabelCursor < FixedPortCycleFamily.predecessor + 1) :
    (portTagStep s).variableTags = s.variableTags ++
      [(0, s.ownerCursor, s.portOccurrenceCursor, s.portLabelCursor)] := by
  simp [portTagStep, hparsed, howner, hocc, hlabel]

theorem cloudDartsStep_increments (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hcursor : s.ownerScanCursor <
      s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ * cloudDegree * 3) :
    (cloudDartsStep s).ownerScanCursor = s.ownerScanCursor + 1 := by
  simp [cloudDartsStep, hparsed, howner, hsize, hcursor]

theorem cloudDartsStep_appends_selected (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hcursor : s.ownerScanCursor <
      s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ * cloudDegree * 3) :
    (cloudDartsStep s).cloudRepAcc =
      s.cloudRepAcc ++
        selectedDart (s.ownerSizes.get ⟨s.ownerCursor, by omega⟩)
          s.ownerScanCursor := by
  simp [cloudDartsStep, hparsed, howner, hsize, hcursor]

theorem internalTagStep_appends_tag (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hedge : s.edgeOccurrenceCursor < s.cloudRepAcc.length)
    (hlabel : s.internalLabelCursor < 5) :
    (internalTagStep s).variableTags = s.variableTags ++
      [(1, s.ownerCursor, s.edgeOccurrenceCursor, s.internalLabelCursor)] := by
  simp [internalTagStep, hparsed, howner, hedge, hlabel]

theorem terminal_states_absorb (s : State)
    (h : s.phase = .tagsComplete ∨ s.phase = .invalid) : step s = s := by
  rcases h with h | h
  · exact step_tagsComplete_absorbing s h
  · exact step_invalid_absorbing s h

end
end PvNP.RealizableHardness.ActualOccurrenceBoundedRuntime

