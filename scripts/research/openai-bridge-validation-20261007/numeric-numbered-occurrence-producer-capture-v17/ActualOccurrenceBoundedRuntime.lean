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

/-- Lift the fixed scalar family string program to the one-coordinate
Cobham input-vector convention. -/
def familyRotationProgramVec (x : Fin 1 → List Bool) : List Bool :=
  familyRotationProgram (x 0)

/-- The fixed family subroutine embeds into Cobham composition. This certifies
the subroutine only, not the transition loop or complete producer. -/
theorem familyRotationProgramVec_mem_Cobham :
    Complexity.Cobham familyRotationProgramVec := by
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

/-- The numeral endpoints returned by the actual string family program are
the numeric endpoints of the source graph's pinned base rotation. -/
theorem familyRotationValue_eq_baseRotation (n v j : Nat)
    (hn : 0 < n) (hv : v < n) (hj : j < cloudDegree) :
    familyRotationValue n v j =
      ((FixedPortCycleFamily.baseRotation n
          (⟨v, hv⟩, ⟨j, by simpa [cloudDegree] using hj⟩)).1.val,
        (FixedPortCycleFamily.baseRotation n
          (⟨v, hv⟩, ⟨j, by simpa [cloudDegree] using hj⟩)).2.val) := by
  let v' : Fin n := ⟨v, hv⟩
  let j' : Fin (FixedPortCycleFamily.predecessor + 1) :=
    ⟨j, by simpa [cloudDegree] using hj⟩
  rw [familyRotationValue_eq n v j hn,
    FixedPortCycleFamily.baseRotation_values n v' j']
  simpa [v', j', FixedPortCycleFamily.labels, FixedPortCycleFamily.degree_eq,
    FixedPortCycleFamily.degree, Complexity.algFamily,
    Complexity.FinBase.toFamily] using
      (Complexity.FinBase.famRotVal_eq Complexity.algBase
        Complexity.one_lt_algBase_deg hn v'
        (FixedPortCycleFamily.labels.symm j'))

/-- The concrete family-string result is in range for the source cloud's
finite vertex and port coordinates. -/
theorem familyRotationValue_bounds (n v j : Nat)
    (hn : 0 < n) (hv : v < n) (hj : j < cloudDegree) :
    (familyRotationValue n v j).1 < n ∧
      (familyRotationValue n v j).2 < cloudDegree := by
  rw [familyRotationValue_eq_baseRotation n v j hn hv hj]
  exact ⟨(FixedPortCycleFamily.baseRotation n
      (⟨v, hv⟩, ⟨j, by simpa [cloudDegree] using hj⟩)).1.isLt,
    (FixedPortCycleFamily.baseRotation n
      (⟨v, hv⟩, ⟨j, by simpa [cloudDegree] using hj⟩)).2.isLt⟩

def portRank (v j : Nat) : Nat := j + cloudDegree * v

/-- Runtime rank is definitionally the pinned `finProdFinEquiv` rank used by
the source representative predicate. -/
theorem portRank_eq_sourceRank (n v j : Nat) (hv : v < n)
    (hj : j < cloudDegree) :
    portRank v j = ActualGraphEdges.rank ((⟨v, hv⟩, ⟨j, hj⟩)) := rfl

theorem finRotate_val_mod (j : Fin cloudDegree) :
    (finRotate cloudDegree j).val = (j.val + 1) % cloudDegree := by
  by_cases hlast : j = Fin.last FixedPortCycleFamily.predecessor
  · have hj : j.val = FixedPortCycleFamily.predecessor := congrArg Fin.val hlast
    rw [coe_finRotate]
    simp [cloudDegree, hlast, hj]
  · rw [coe_finRotate]
    have hjne : j.val ≠ FixedPortCycleFamily.predecessor := by
      intro he
      exact hlast (Fin.ext he)
    have hjlt : j.val + 1 < cloudDegree := by
      simp only [cloudDegree]
      omega
    simp [cloudDegree, hlast, Nat.mod_eq_of_lt hjlt]

theorem finRotate_symm_val_mod (j : Fin cloudDegree) :
    ((finRotate cloudDegree).symm j).val =
      (j.val + cloudDegree - 1) % cloudDegree := by
  by_cases hz : j.val = 0
  · have hj : j = 0 := Fin.ext hz
    subst j
    rw [finRotate_symm_apply]
    simp [cloudDegree, Fin.val_sub]
  · have hjne : j ≠ 0 := by
      intro he
      exact hz (congrArg Fin.val he)
    rw [coe_finRotate_symm_of_ne_zero hjne]
    have hmod : (j.val + cloudDegree - 1) % cloudDegree = j.val - 1 := by
      have hsum : j.val + cloudDegree - 1 = (j.val - 1) + cloudDegree := by
        have hjpos : 0 < j.val := Nat.pos_of_ne_zero hz
        omega
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    exact hmod.symm
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

/-- The three numeric reverse cases are exactly the source graph reverse on
its typed dart. This is the local endpoint bridge used by representative
selection: label zero is the actual family call, while labels one and two are
the source Fin cycle and its inverse. -/
theorem reverseDart_typed (n v j : Nat) (hv : v < n)
    (hj : j < cloudDegree) (hn : 0 < n) (d : Fin 3) :
    reverseDart n v j d.val =
      let r := ActualGraphEdges.reverse
        (((⟨v, hv⟩, ⟨j, hj⟩), d) : ActualGraphEdges.Dart n)
      (r.1.1.val, r.1.2.val, r.2.val) := by
  fin_cases d
  · simp only [Fin.val_zero, reverseDart, if_pos rfl]
    rw [familyRotationValue_eq_baseRotation n v j hn hv hj]
    simp [ActualGraphEdges.reverse, PortCycleReplacement.rotation, cloudDegree]
  · simp [reverseDart, ActualGraphEdges.reverse,
      PortCycleReplacement.rotation, finRotate_val_mod, cloudDegree]
  · simp [reverseDart, ActualGraphEdges.reverse,
      PortCycleReplacement.rotation, finRotate_symm_val_mod, cloudDegree]
/-- At the exact row-major product ordinal, runtime rank filtering agrees with
`ActualGraphEdges.IsRep` on the corresponding full typed dart. The retained
six-tuple keeps the complete dart identity, including its third coordinate. -/
theorem selectedDart_typed (n v j : Nat) (hv : v < n)
    (hj : j < cloudDegree) (hn : 0 < n) (d : Fin 3) :
    let source : ActualGraphEdges.Dart n := ((⟨v, hv⟩, ⟨j, hj⟩), d)
    let reverse := ActualGraphEdges.reverse source
    selectedDart n (3 * (v * cloudDegree + j) + d.val) =
      if ActualGraphEdges.IsRep source then
        [(v, j, d.val, reverse.1.1.val, reverse.1.2.val, reverse.2.val)]
      else [] := by
  let source : ActualGraphEdges.Dart n := ((⟨v, hv⟩, ⟨j, hj⟩), d)
  let reverse := ActualGraphEdges.reverse source
  have hreverse := reverseDart_typed n v j hv hj hn d
  simp [selectedDart, source, reverse, hreverse, portRank,
    Nat.mul_add_div, Nat.mul_add_mod, cloudDegree, ActualGraphEdges.IsRep,
    ActualGraphEdges.rank, d.isLt, hj]
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

/-- A length-prefixed frame for an arbitrary bit string. -/
def frameBits (bits : List Bool) : List Bool :=
  encodeWord bits.length ++ bits

/-- A length-prefixed frame for a list of natural-number lists. -/
def frameNatLists (xs : List (List Nat)) : List Bool :=
  encodeWords (xs.length :: xs.flatMap fun x => x.length :: x)

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

/-- A length-prefixed frame for an arbitrary natural-number vector. -/
def frameNats (ns : List Nat) : List Bool :=
  encodeWords (ns.length :: ns)

def flattenTriples (xs : List (Nat × Nat × Nat)) : List Nat :=
  xs.flatMap fun (r, c, v) => [r, c, v]

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

/-- The runtime's three coordinate cases are exactly the allocation's
list-indexed row variables, including repeated owners. -/
theorem ownerAt_asInstance (I : Input) (r : Fin I.equations.length)
    (c : Fin 3) :
    ownerAt (I.equations.get r) c.val = (allocation I).owner (r, c) := by
  fin_cases c <;>
    simp [ownerAt, allocation, ActualBooleanOccurrenceSource.asInstance,
      ActualOccurrenceAllocation.Instance.owner]

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

/-- Execute the parser transition on a concrete bit list. -/
def runParseBits : List Bool → State → State
  | [], s => s
  | _ :: bits, s => runParseBits bits (parseStep s)

theorem runParseBits_append (left right : List Bool) (s : State) :
    runParseBits (left ++ right) s =
      runParseBits right (runParseBits left s) := by
  induction left generalizing s with
  | nil => rfl
  | cons b left ih => simp [runParseBits, ih]

/-- A unary word consumes its delimiter and appends its natural value to the
decoded-word accumulator, even when earlier words are already present. -/
theorem runParseBits_encodeWord (n k : Nat) (s : State) (rest : List Bool)
    (hunread : s.unread = encodeWord n ++ rest)
    (hcount : s.unaryCount = k) :
    runParseBits (encodeWord n) s =
      { s with unread := rest, unaryCount := 0,
        decodedWords := s.decodedWords ++ [k + n] } := by
  induction n generalizing k s with
  | zero =>
      have hfalse : s.unread = false :: rest := by
        simpa [encodeWord] using hunread
      simp [runParseBits, encodeWord, parseStep, hfalse, hcount]
  | succ n ih =>
      have htrue : s.unread = true :: encodeWord n ++ rest := by
        simpa [encodeWord, List.replicate_succ, List.cons_append] using hunread
      have hstep := parseStep_consumes_true s (encodeWord n ++ rest) htrue
      have hu : (parseStep s).unread = encodeWord n ++ rest := hstep.1
      have hc : (parseStep s).unaryCount = k + 1 := by
        simpa [hcount] using hstep.2
      have htail := ih (k + 1) (parseStep s) rest hu hc
      simpa [runParseBits, htrue, parseStep, hcount, htail,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem runParseBits_encodeWords (words : List Nat) (s : State)
    (rest : List Bool) (hunread : s.unread = encodeWords words ++ rest)
    (hcount : s.unaryCount = 0) :
    runParseBits (encodeWords words) s =
      { s with unread := rest, unaryCount := 0,
        decodedWords := s.decodedWords ++ words } := by
  induction words generalizing s rest with
  | nil => simp [runParseBits, encodeWords, hunread, hcount]
  | cons n words ih =>
      let suffix := encodeWords words ++ rest
      have hword : s.unread = encodeWord n ++ suffix := by
        simpa [suffix, encodeWords, List.append_assoc] using hunread
      have hfirst := runParseBits_encodeWord n 0 s suffix hword hcount
      let t := { s with unread := suffix, unaryCount := 0,
        decodedWords := s.decodedWords ++ [n] }
      have htail : t.unread = encodeWords words ++ rest := by simp [t, suffix]
      have htailCount : t.unaryCount = 0 := by simp [t]
      have hrun := ih t rest htail htailCount
      rw [runParseBits_append, hfirst]
      simpa [t, suffix, List.append_assoc] using hrun

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
          (s.slotCursor % 3)).val)] := by
  simp [slotScanStep, hparsed, hcursor]

/-- The exact row-major triple written at slot cursor `q`. -/
def sourceSlotAt (input : Input) (q : Nat)
    (hq : q < input.equations.length * 3) : Nat × Nat × Nat :=
  (q / 3, q % 3,
    (ownerAt (input.equations.get ⟨q / 3, by omega⟩) (q % 3)).val)

/-- Semantic prefix of the literal source-slot stream scanned by the machine. -/
def sourceSlotTracePrefix (input : Input) :
    (k : Nat) → k ≤ input.equations.length * 3 → List (Nat × Nat × Nat)
  | 0, _ => []
  | k + 1, hk =>
      sourceSlotTracePrefix input k (by omega) ++
        [sourceSlotAt input k (by omega)]

theorem sourceSlotTracePrefix_eq_ofFn (input : Input) (k : Nat)
    (hk : k ≤ input.equations.length * 3) :
    sourceSlotTracePrefix input k hk =
      List.ofFn (fun i : Fin k => sourceSlotAt input i.val (by omega)) := by
  induction k with
  | zero => simp [sourceSlotTracePrefix]
  | succ k ih =>
      rw [sourceSlotTracePrefix, ih (by omega), List.ofFn_succ']
      simp [sourceSlotAt]

/-- The full runtime trace is the exact row-major finite product used by the
actual occurrence allocation. -/
theorem sourceSlotTracePrefix_eq_slotList (I : Input) :
    sourceSlotTracePrefix I (I.equations.length * 3) (by omega) =
      (ActualOccurrenceAllocation.slotList I.equations.length).map
        (fun o => (o.1.val, o.2.val,
          ((allocation I).owner o).val)) := by
  rw [sourceSlotTracePrefix_eq_ofFn]
  rw [List.ofFn_mul]
  simp [ActualOccurrenceAllocation.slotList, List.product, List.finRange,
    sourceSlotAt, ownerAt_asInstance, Nat.mul_add_div, Nat.mul_add_mod]

/-- Iterate the slot phase alone, stopping before its boundary transition. -/
def runSlotScan : Nat → State → State
  | 0, s => s
  | k + 1, s => slotScanStep (runSlotScan k s)

/-- Every slot-phase prefix is exactly the corresponding row-major prefix of
the input occurrence stream. Parsing data is preserved throughout the phase. -/
theorem runSlotScan_prefix (input : Input) (s : State) (k : Nat)
    (hk : k ≤ input.equations.length * 3)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor = 0) (htrace : s.slotTrace = []) :
    (runSlotScan k s).slotCursor = k ∧
    (runSlotScan k s).slotTrace = sourceSlotTracePrefix input k hk ∧
    parsedInput (runSlotScan k s) = some input := by
  induction k generalizing s with
  | zero => simp [runSlotScan, sourceSlotTracePrefix, hcursor, htrace, hparsed]
  | succ k ih =>
      have hkle : k ≤ input.equations.length * 3 := by omega
      have hklt : k < input.equations.length * 3 := by omega
      have hprev := ih s hkle hparsed hcursor htrace
      rcases hprev with ⟨hprevCursor, hprevTrace, hprevParsed⟩
      have happ := slotScanStep_appends_occurrence
        (runSlotScan k s) input hprevParsed (by simpa [hprevCursor] using hklt)
      have hnextParsed :
          parsedInput (slotScanStep (runSlotScan k s)) = some input := by
        simp [parsedInput, slotScanStep, hprevParsed, hprevCursor, hklt]
      refine ⟨?_, ?_, hnextParsed⟩
      · simpa [runSlotScan] using
          slotScanStep_increments (runSlotScan k s) input hprevParsed
            (by simpa [hprevCursor] using hklt)
      · change (slotScanStep (runSlotScan k s)).slotTrace =
          sourceSlotTracePrefix input (k + 1) hk
        rw [happ, hprevTrace]
        simp [sourceSlotTracePrefix, sourceSlotAt]

/-- Forward-iteration form matching the global machine's runSteps recursion. -/
def runSlotScanForward : Nat → State → State
  | 0, s => s
  | k + 1, s => runSlotScanForward k (slotScanStep s)

/-- Exact row-major prefix invariant with an arbitrary starting cursor. -/
theorem runSlotScanForward_prefix (input : Input) (s : State)
    (q k : Nat) (hqk : q + k ≤ input.equations.length * 3)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor = q)
    (htrace : s.slotTrace = sourceSlotTracePrefix input q (by omega))
    (hphase : s.phase = .slotScan) :
    (runSlotScanForward k s).slotCursor = q + k ∧
    (runSlotScanForward k s).slotTrace =
      sourceSlotTracePrefix input (q + k) hqk ∧
    parsedInput (runSlotScanForward k s) = some input ∧
    (runSlotScanForward k s).phase = .slotScan := by
  induction k generalizing q s with
  | zero => simp [runSlotScanForward, hcursor, htrace, hparsed, hphase]
  | succ k ih =>
      have hq : q < input.equations.length * 3 := by omega
      have hparsed' : parsedInput (slotScanStep s) = some input := by
        simp [parsedInput, slotScanStep, hparsed, hq, hcursor]
      have hcursor' : (slotScanStep s).slotCursor = q + 1 := by
        simpa [hcursor] using slotScanStep_increments s input hparsed
          (by simpa [hcursor] using hq)
      have htrace' : (slotScanStep s).slotTrace =
          sourceSlotTracePrefix input (q + 1) (by omega) := by
        rw [slotScanStep_appends_occurrence s input hparsed (by simpa [hcursor] using hq),
          htrace]
        simp [sourceSlotTracePrefix, sourceSlotAt, hcursor]
      have hphase' : (slotScanStep s).phase = .slotScan := by
        simp [slotScanStep, hparsed, hq, hcursor, hphase]
      have hprev := ih (q + 1) (slotScanStep s) (by omega)
        hparsed' hcursor' htrace' hphase'
      rcases hprev with ⟨hcur, htr, hpar, hph⟩
      refine ⟨by omega, ?_, hpar, hph⟩
      simpa [runSlotScanForward] using htr

/-- During the counted slot phase, the global dispatcher executes the same
slot transition sequence as the dedicated phase iterator. -/
theorem runSteps_eq_runSlotScanForward (input : Input) (s : State)
    (q k : Nat) (hqk : q + k ≤ input.equations.length * 3)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor = q)
    (htrace : s.slotTrace = sourceSlotTracePrefix input q (by omega))
    (hphase : s.phase = .slotScan) :
    runSteps k s = runSlotScanForward k s := by
  induction k generalizing q s with
  | zero => rfl
  | succ k ih =>
      have hq : q < input.equations.length * 3 := by omega
      have hparsed' : parsedInput (slotScanStep s) = some input := by
        simp [parsedInput, slotScanStep, hparsed, hq, hcursor]
      have hcursor' : (slotScanStep s).slotCursor = q + 1 := by
        simpa [hcursor] using slotScanStep_increments s input hparsed
          (by simpa [hcursor] using hq)
      have htrace' : (slotScanStep s).slotTrace =
          sourceSlotTracePrefix input (q + 1) (by omega) := by
        rw [slotScanStep_appends_occurrence s input hparsed (by simpa [hcursor] using hq),
          htrace]
        simp [sourceSlotTracePrefix, sourceSlotAt, hcursor]
      have hphase' : (slotScanStep s).phase = .slotScan := by
        simp [slotScanStep, hparsed, hq, hcursor, hphase]
      have hdispatch : step s = slotScanStep s := by
        simp [step, hphase]
      rw [runSteps, hdispatch, runSlotScanForward]
      exact ih (q + 1) (slotScanStep s) (by omega)
        hparsed' hcursor' htrace' hphase'

/-- Iterating one transition commutes with one additional transition. -/
theorem step_runSteps_commute (k : Nat) (s : State) :
    step (runSteps k s) = runSteps k (step s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      change step (runSteps k (step s)) = runSteps k (step (step s))
      exact ih (step s)

theorem runSteps_succ_eq_step (k : Nat) (s : State) :
    runSteps (k + 1) s = step (runSteps k s) := by
  rw [runSteps]
  exact (step_runSteps_commute k s).symm

/-- The real dispatcher completes the slot phase after exactly its `3m`
source slots and one boundary transition, retaining the complete row-major
trace and the parsed input. -/
theorem runSteps_slotPhase_complete (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (hcursor : s.slotCursor = 0) (htrace : s.slotTrace = [])
    (hphase : s.phase = .slotScan) :
    let S := input.equations.length * 3
    (runSteps (S + 1) s).phase = .ownerScan ∧
      (runSteps (S + 1) s).slotTrace = sourceSlotTracePrefix input S (by omega) ∧
      parsedInput (runSteps (S + 1) s) = some input := by
  let S := input.equations.length * 3
  have hrun := runSteps_eq_runSlotScanForward input s 0 S (by omega)
    hparsed hcursor htrace hphase
  have hpref := runSlotScanForward_prefix input s 0 S (by omega)
    hparsed hcursor htrace hphase
  rcases hpref with ⟨hscanCursor, hscanTrace, hscanParsed, hscanPhase⟩
  have hstep : step (runSlotScanForward S s) =
      slotScanStep (runSlotScanForward S s) := by
    simp [step, hscanPhase]
  have hboundary :
      (slotScanStep (runSlotScanForward S s)).phase = .ownerScan := by
    simp [slotScanStep, hscanParsed, hscanCursor, S]
  have htraceBoundary :
      (slotScanStep (runSlotScanForward S s)).slotTrace =
        sourceSlotTracePrefix input S (by omega) := by
    simp [slotScanStep, hscanParsed, hscanCursor, hscanTrace, S]
  have hparsedBoundary :
      parsedInput (slotScanStep (runSlotScanForward S s)) = some input := by
    simp [parsedInput, slotScanStep, hscanParsed, hscanCursor, S]
  rw [runSteps_succ_eq_step, hrun, hstep]
  exact ⟨hboundary, htraceBoundary, hparsedBoundary⟩

theorem ownerScanStep_increments (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor < s.slotTrace.length) :
    (ownerScanStep s).ownerScanCursor = s.ownerScanCursor + 1 := by
  simp [ownerScanStep, hparsed, howner, hcursor]

/-- The owner-filter prefix emitted from a fixed source-slot trace. -/
/-- Typed row-major source dart at a bounded unary cursor. Its three fields are
obtained by quotient/remainder against the fixed port and dart radices. -/
def sourceDartAt (n q : Nat) (hq : q < n * cloudDegree * 3) :
    ActualGraphEdges.Dart n :=
  let z := q / 3
  (((⟨z / cloudDegree, by omega⟩ : Fin n),
    (⟨z % cloudDegree, by omega⟩ : Fin cloudDegree)),
    (⟨q % 3, by omega⟩ : Fin 3))

def sourceDartTracePrefix (n : Nat) :
    (k : Nat) → k ≤ n * cloudDegree * 3 → List (ActualGraphEdges.Dart n)
  | 0, _ => []
  | k + 1, hk =>
      sourceDartTracePrefix n k (by omega) ++
        [sourceDartAt n k (by omega)]

theorem sourceDartTracePrefix_eq_ofFn (n k : Nat)
    (hk : k ≤ n * cloudDegree * 3) :
    sourceDartTracePrefix n k hk =
      List.ofFn (fun i : Fin k => sourceDartAt n i.val (by omega)) := by
  induction k with
  | zero => simp [sourceDartTracePrefix]
  | succ k ih =>
      rw [sourceDartTracePrefix, ih (by omega), List.ofFn_succ']
      simp [sourceDartAt]

/-- The typed cursor list is the exact nested Fin product scanned by the
source graph, in vertex/port/dart order. -/
theorem sourceDartTracePrefix_eq_dartList (n : Nat) :
    sourceDartTracePrefix n (n * cloudDegree * 3) (by omega) =
      ActualGraphEdges.dartList n := by
  rw [sourceDartTracePrefix_eq_ofFn]
  rw [List.ofFn_mul]
  rw [List.ofFn_mul]
  simp [ActualGraphEdges.dartList, sourceDartAt, List.product,
    List.finRange, cloudDegree, Nat.mul_add_div, Nat.mul_add_mod]
def ownerOccurrencePrefix (owner : Nat)
    (trace : List (Nat × Nat × Nat)) : Nat → List Nat
  | 0 => []
  | q + 1 =>
      ownerOccurrencePrefix owner trace q ++
        (if hq : q < trace.length then
          let (r, c, v) := trace.get ⟨q, hq⟩
          if v = owner then [3 * r + c] else []
        else [])

theorem ownerOccurrencePrefix_cons (owner : Nat) (a : Nat × Nat × Nat)
    (trace : List (Nat × Nat × Nat)) (k : Nat) :
    ownerOccurrencePrefix owner (a :: trace) (k + 1) =
      (if a.2.2 = owner then [3 * a.1 + a.2.1] else []) ++
        ownerOccurrencePrefix owner trace k := by
  induction k with
  | zero => simp [ownerOccurrencePrefix]
  | succ k ih =>
      simp [ownerOccurrencePrefix, ih, List.get_cons_succ, Nat.add_assoc]

theorem ownerOccurrencePrefix_full_eq_filterMap (owner : Nat)
    (trace : List (Nat × Nat × Nat)) :
    ownerOccurrencePrefix owner trace trace.length =
      trace.filterMap (fun t =>
        if t.2.2 = owner then some (3 * t.1 + t.2.1) else none) := by
  induction trace with
  | nil => simp [ownerOccurrencePrefix]
  | cons a trace ih =>
      rw [show (a :: trace).length = trace.length + 1 by simp,
        ownerOccurrencePrefix_cons]
      simp [ih]

/-- Filtering the exact scanned row-major trace by owner produces the actual
Fin-valued allocation occurrence list, mapped to its source-slot ordinal. -/
theorem ownerOccurrencePrefix_eq_occurrenceList (I : Input)
    (v : Fin I.variables) :
    ownerOccurrencePrefix v.val
        (sourceSlotTracePrefix I (I.equations.length * 3) (by omega))
        (I.equations.length * 3) =
      ((allocation I).occurrenceList v).map
        (fun o => 3 * o.1.val + o.2.val) := by
  let trace := sourceSlotTracePrefix I (I.equations.length * 3) (by omega)
  have hlen : trace.length = I.equations.length * 3 := by
    dsimp [trace]
    rw [sourceSlotTracePrefix_eq_ofFn]
    simp
  have htrace : trace =
      (ActualOccurrenceAllocation.slotList I.equations.length).map
        (fun o => (o.1.val, o.2.val, ((allocation I).owner o).val)) := by
    simpa [trace] using sourceSlotTracePrefix_eq_slotList I
  change ownerOccurrencePrefix v.val trace (I.equations.length * 3) = _
  rw [← hlen, ownerOccurrencePrefix_full_eq_filterMap, htrace]
  simp [ActualOccurrenceAllocation.Instance.occurrenceList,
    ActualOccurrenceAllocation.Instance.owner, List.filterMap_map,
    ownerAt_asInstance]

/-- Each owner-scan transition appends exactly the current matching source
slot number, preserving the row-major trace order. -/
theorem ownerScanStep_appends_exact_slot (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor < s.slotTrace.length) :
    (ownerScanStep s).ownerSlotAcc = s.ownerSlotAcc ++
      (let (r, c, v) := s.slotTrace.get ⟨s.ownerScanCursor, hcursor⟩
       if v = s.ownerCursor then [3 * r + c] else []) := by
  simp [ownerScanStep, hparsed, howner, hcursor]

/-- Forward iterator for one owner-filter scan, using the actual ownerScanStep
transition. -/
def runOwnerScanForward : Nat → State → State
  | 0, s => s
  | k + 1, s => runOwnerScanForward k (ownerScanStep s)

/-- Every prefix of an owner-filter pass is exactly the filtered prefix of its
fixed source-slot trace. -/
theorem runOwnerScanForward_prefix (input : Input) (s : State)
    (q k : Nat) (hqk : q + k ≤ s.slotTrace.length)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor = q)
    (hacc : s.ownerSlotAcc =
      ownerOccurrencePrefix s.ownerCursor s.slotTrace q)
    (hphase : s.phase = .ownerScan) :
    (runOwnerScanForward k s).ownerScanCursor = q + k ∧
    (runOwnerScanForward k s).ownerSlotAcc =
      ownerOccurrencePrefix s.ownerCursor s.slotTrace (q + k) ∧
    (runOwnerScanForward k s).slotTrace = s.slotTrace ∧
    parsedInput (runOwnerScanForward k s) = some input ∧
    (runOwnerScanForward k s).ownerCursor = s.ownerCursor ∧
    (runOwnerScanForward k s).phase = .ownerScan ∧
    (runOwnerScanForward k s).ownerSlotLists = s.ownerSlotLists ∧
    (runOwnerScanForward k s).ownerSizes = s.ownerSizes := by
  induction k generalizing q s with
  | zero => simp [runOwnerScanForward, hcursor, hacc, hparsed, howner, hphase]
  | succ k ih =>
      have hq : q < s.slotTrace.length := by omega
      have hcursor' : (ownerScanStep s).ownerScanCursor = q + 1 := by
        simpa [hcursor] using ownerScanStep_increments s input hparsed howner hq
      have hacc' : (ownerScanStep s).ownerSlotAcc =
          ownerOccurrencePrefix s.ownerCursor s.slotTrace (q + 1) := by
        rw [ownerScanStep_appends_exact_slot s input hparsed howner
          (by simpa [hcursor] using hq), hacc]
        simp [ownerOccurrencePrefix, hcursor, hq]
      have htrace' : (ownerScanStep s).slotTrace = s.slotTrace := by
        simp [ownerScanStep, hparsed, howner, hq]
      have hparsed' : parsedInput (ownerScanStep s) = some input := by
        simp [parsedInput, ownerScanStep, hparsed, howner, hq]
      have howner' : (ownerScanStep s).ownerCursor = s.ownerCursor := by
        simp [ownerScanStep, hparsed, howner, hq]
      have hphase' : (ownerScanStep s).phase = .ownerScan := by
        simp [ownerScanStep, hparsed, howner, hq, hphase]
      have hlists' : (ownerScanStep s).ownerSlotLists = s.ownerSlotLists := by
        simp [ownerScanStep, hparsed, howner, hq]
      have hsizes' : (ownerScanStep s).ownerSizes = s.ownerSizes := by
        simp [ownerScanStep, hparsed, howner, hq]
      have hprev := ih (q + 1) (ownerScanStep s) (by omega)
        hparsed' howner' hcursor' hacc' hphase'
      rcases hprev with ⟨hc, ha, ht, hp, ho, hph, hls, hsz⟩
      refine ⟨by omega, ?_, ?_, hp, ho, hph, ?_, ?_⟩
      · simpa [runOwnerScanForward] using ha
      · exact ht.trans htrace'
      · exact hls.trans hlists'
      · exact hsz.trans hsizes'

/-- At the owner boundary, the accumulated filtered prefix is committed as
exactly one owner list and its matching cloud size. -/
theorem ownerScanStep_finishes_owner (s : State) (input : Input)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hend : s.ownerScanCursor = s.slotTrace.length) :
    (ownerScanStep s).ownerSlotLists = s.ownerSlotLists ++ [s.ownerSlotAcc] ∧
    (ownerScanStep s).ownerSizes = s.ownerSizes ++ [s.ownerSlotAcc.length] ∧
    (ownerScanStep s).ownerCursor = s.ownerCursor + 1 ∧
    (ownerScanStep s).ownerSlotAcc = [] := by
  simp [ownerScanStep, hparsed, howner, hend]

/-- A complete one-owner filtering pass commits exactly the filtered source
slot ordinals in row-major order; the machine's recorded size is their length. -/
theorem runOwnerScan_owner_complete (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor = 0) (hacc : s.ownerSlotAcc = [])
    (hphase : s.phase = .ownerScan) :
    let t := ownerScanStep (runOwnerScanForward s.slotTrace.length s)
    t.ownerSlotLists = s.ownerSlotLists ++
      [ownerOccurrencePrefix s.ownerCursor s.slotTrace s.slotTrace.length] ∧
    t.ownerSizes = s.ownerSizes ++
      [(ownerOccurrencePrefix s.ownerCursor s.slotTrace s.slotTrace.length).length] ∧
    t.ownerCursor = s.ownerCursor + 1 := by
  have hpref := runOwnerScanForward_prefix input s 0 s.slotTrace.length
    (by omega) hparsed howner hcursor (by simpa [hacc]) hphase
  rcases hpref with ⟨hend, hfiltered, htrace, hparsed', howner', hphase',
    hslotLists, hownerSizes⟩
  have hfinish := ownerScanStep_finishes_owner
    (runOwnerScanForward s.slotTrace.length s) input hparsed' howner' hend
  exact ⟨by simpa [hslotLists, hfiltered] using hfinish.1,
    by simpa [hownerSizes, hfiltered] using hfinish.2.1,
    by simpa using hfinish.2.2.1⟩

/-- During a counted owner-filter phase, the global dispatcher follows the
same exact transition sequence as the dedicated owner iterator. -/
theorem runSteps_eq_runOwnerScanForward (input : Input) (s : State)
    (q k : Nat) (hqk : q + k ≤ s.slotTrace.length)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor = q)
    (hacc : s.ownerSlotAcc = ownerOccurrencePrefix s.ownerCursor s.slotTrace q)
    (hphase : s.phase = .ownerScan) :
    runSteps k s = runOwnerScanForward k s := by
  induction k generalizing q s with
  | zero => rfl
  | succ k ih =>
      have hq : q < s.slotTrace.length := by omega
      have hcursor' : (ownerScanStep s).ownerScanCursor = q + 1 := by
        simpa [hcursor] using ownerScanStep_increments s input hparsed howner hq
      have hacc' : (ownerScanStep s).ownerSlotAcc =
          ownerOccurrencePrefix s.ownerCursor s.slotTrace (q + 1) := by
        rw [ownerScanStep_appends_exact_slot s input hparsed howner
          (by simpa [hcursor] using hq), hacc]
        simp [ownerOccurrencePrefix, hcursor, hq]
      have htrace' : (ownerScanStep s).slotTrace = s.slotTrace := by
        simp [ownerScanStep, hparsed, howner, hq]
      have hparsed' : parsedInput (ownerScanStep s) = some input := by
        simp [parsedInput, ownerScanStep, hparsed, howner, hq]
      have howner' : (ownerScanStep s).ownerCursor = s.ownerCursor := by
        simp [ownerScanStep, hparsed, howner, hq]
      have hphase' : (ownerScanStep s).phase = .ownerScan := by
        simp [ownerScanStep, hparsed, howner, hq, hphase]
      have hdispatch : step s = ownerScanStep s := by simp [step, hphase]
      rw [runSteps, hdispatch, runOwnerScanForward]
      exact ih (q + 1) (ownerScanStep s) (by omega)
        hparsed' howner' hcursor' hacc' hphase'

/-- The global dispatcher completes one owner-filter phase after exactly one
pass over the stored slot trace and one boundary step. -/
theorem runSteps_ownerPhase_complete (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor = 0) (hacc : s.ownerSlotAcc = [])
    (hphase : s.phase = .ownerScan) :
    let S := s.slotTrace.length
    let t := runSteps (S + 1) s
    t.ownerSlotLists = s.ownerSlotLists ++
      [ownerOccurrencePrefix s.ownerCursor s.slotTrace S] ∧
    t.ownerSizes = s.ownerSizes ++
      [(ownerOccurrencePrefix s.ownerCursor s.slotTrace S).length] ∧
    t.ownerCursor = s.ownerCursor + 1 := by
  let S := s.slotTrace.length
  have hrun := runSteps_eq_runOwnerScanForward input s 0 S (by omega)
    hparsed howner hcursor (by simpa [hacc]) hphase
  have hpref := runOwnerScanForward_prefix input s 0 S (by omega)
    hparsed howner hcursor (by simpa [hacc]) hphase
  rcases hpref with ⟨hend, hfiltered, htrace, hparsed', howner', hphase',
    hslotLists, hownerSizes⟩
  have hfinish := ownerScanStep_finishes_owner
    (runOwnerScanForward S s) input hparsed' howner' hend
  have hdispatch : step (runOwnerScanForward S s) =
      ownerScanStep (runOwnerScanForward S s) := by
    simp [step, hphase']
  have hresult : runSteps (S + 1) s =
      ownerScanStep (runOwnerScanForward S s) := by
    rw [runSteps_succ_eq_step, hrun, hdispatch]
  exact ⟨by simpa [hresult, hfiltered, hslotLists, S] using hfinish.1,
    by simpa [hresult, hfiltered, hownerSizes, S] using hfinish.2.1,
    by simpa [hresult, S] using hfinish.2.2.1⟩

/-- Full owner-pass state result, including the reset cursors needed to start
the next owner from the actual global dispatcher. -/
theorem runSteps_ownerPhase_state_complete (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.ownerScanCursor = 0) (hacc : s.ownerSlotAcc = [])
    (hphase : s.phase = .ownerScan) :
    let S := s.slotTrace.length
    let t := runSteps (S + 1) s
    t.ownerSlotLists = s.ownerSlotLists ++
      [ownerOccurrencePrefix s.ownerCursor s.slotTrace S] ∧
    t.ownerSizes = s.ownerSizes ++
      [(ownerOccurrencePrefix s.ownerCursor s.slotTrace S).length] ∧
    t.ownerCursor = s.ownerCursor + 1 ∧
    t.ownerScanCursor = 0 ∧ t.ownerSlotAcc = [] ∧
    t.slotTrace = s.slotTrace ∧ parsedInput t = some input ∧
    t.phase = .ownerScan := by
  let S := s.slotTrace.length
  have hrun := runSteps_eq_runOwnerScanForward input s 0 S (by omega)
    hparsed howner hcursor (by simpa [hacc]) hphase
  have hpref := runOwnerScanForward_prefix input s 0 S (by omega)
    hparsed howner hcursor (by simpa [hacc]) hphase
  rcases hpref with ⟨hend, hfiltered, htrace, hparsed', howner', hphase',
    hslotLists, hownerSizes⟩
  have hdispatch : step (runOwnerScanForward S s) =
      ownerScanStep (runOwnerScanForward S s) := by
    simp [step, hphase']
  have hresult : runSteps (S + 1) s =
      ownerScanStep (runOwnerScanForward S s) := by
    rw [runSteps_succ_eq_step, hrun, hdispatch]
  have hfinish := ownerScanStep_finishes_owner
    (runOwnerScanForward S s) input hparsed' howner' hend
  have hownerLists :
      (runOwnerScanForward S s).ownerSlotLists = s.ownerSlotLists := hslotLists
  have hownerSizeList :
      (runOwnerScanForward S s).ownerSizes = s.ownerSizes := hownerSizes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hresult, hfiltered, hownerLists] using hfinish.1
  · simpa [hresult, hfiltered, hownerSizeList] using hfinish.2.1
  · simpa [hresult] using hfinish.2.2.1
  · simp [hresult, ownerScanStep, hparsed', howner', hend]
  · simp [hresult, ownerScanStep, hparsed', howner', hend]
  · simp [hresult, ownerScanStep, hparsed', howner', hend, htrace]
  · simp [hresult, parsedInput, ownerScanStep, hparsed', howner', hend]
  · simp [hresult, ownerScanStep, hparsed', howner', hend, hphase']

/-- Exact owner occurrence lists contributed by k consecutive owner passes
starting at owner q. -/
def ownerOccurrenceBlocks (trace : List (Nat × Nat × Nat)) (q : Nat) :
    Nat → List (List Nat)
  | 0 => []
  | k + 1 => ownerOccurrenceBlocks trace q k ++
      [ownerOccurrencePrefix (q + k) trace trace.length]

theorem ownerOccurrenceBlocks_succ (trace : List (Nat × Nat × Nat))
    (q k : Nat) :
    ownerOccurrenceBlocks trace q (k + 1) =
      [ownerOccurrencePrefix q trace trace.length] ++
        ownerOccurrenceBlocks trace (q + 1) k := by
  induction k with
  | zero => simp [ownerOccurrenceBlocks]
  | succ k ih =>
      simp [ownerOccurrenceBlocks, ih, List.append_assoc, Nat.add_assoc]

/-- Consecutive runtime owner blocks over the exact source trace are precisely
the occurrence lists of the corresponding Fin owners, in owner order. -/
theorem ownerOccurrenceBlocks_eq_occurrenceLists (I : Input)
    (q k : Nat) (hqk : q + k ≤ I.variables) :
    ownerOccurrenceBlocks
        (sourceSlotTracePrefix I (I.equations.length * 3) (by omega)) q k =
      (List.finRange k).map (fun i =>
        ((allocation I).occurrenceList
          ⟨q + i.val, by omega⟩).map (fun o => 3 * o.1.val + o.2.val)) := by
  induction k generalizing q with
  | zero => simp [ownerOccurrenceBlocks]
  | succ k ih =>
      rw [ownerOccurrenceBlocks_succ, List.finRange_succ]
      rw [ownerOccurrencePrefix_eq_occurrenceList I ⟨q, by omega⟩]
      simp only [List.singleton_append, List.map_cons, List.map_map,
        Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (q + 1) (by omega)

def runOwnerBlocks (S : Nat) : Nat → State → State
  | 0, s => s
  | k + 1, s => runOwnerBlocks S k (runSteps (S + 1) s)

/-- Repeated actual owner-phase transitions construct precisely the ordered
owner-prefix lists and their sizes. This does not assume any precomputed
occurrence list: every entry is filtered from the scanned source-slot trace. -/
theorem runOwnerBlocks_exact (input : Input) (s : State)
    (S q k : Nat) (hqk : q + k ≤ input.variables)
    (baseLists : List (List Nat)) (baseSizes : List Nat)
    (htraceLen : s.slotTrace.length = S)
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = q)
    (hscan : s.ownerScanCursor = 0) (hacc : s.ownerSlotAcc = [])
    (hlists : s.ownerSlotLists = baseLists)
    (hsizes : s.ownerSizes = baseSizes)
    (hphase : s.phase = .ownerScan) :
    (runOwnerBlocks S k s).ownerSlotLists =
        baseLists ++ ownerOccurrenceBlocks s.slotTrace q k ∧
    (runOwnerBlocks S k s).ownerSizes =
        baseSizes ++ (ownerOccurrenceBlocks s.slotTrace q k).map List.length ∧
    (runOwnerBlocks S k s).ownerCursor = q + k ∧
    (runOwnerBlocks S k s).ownerScanCursor = 0 ∧
    (runOwnerBlocks S k s).ownerSlotAcc = [] ∧
    (runOwnerBlocks S k s).slotTrace = s.slotTrace ∧
    parsedInput (runOwnerBlocks S k s) = some input ∧
    (runOwnerBlocks S k s).phase = .ownerScan := by
  induction k generalizing q s baseLists baseSizes with
  | zero =>
      simp [runOwnerBlocks, ownerOccurrenceBlocks, hcursor, hscan,
        hacc, hlists, hsizes, htraceLen, hparsed, hphase]
  | succ k ih =>
      have hq : q < input.variables := by omega
      have hS : s.slotTrace.length = S := htraceLen
      have hsowner : s.ownerCursor < input.variables := by
        simpa [hcursor] using hq
      have hpass := runSteps_ownerPhase_state_complete input s hparsed hsowner
        hscan hacc hphase
      let t := runSteps (S + 1) s
      have hlists' : t.ownerSlotLists =
          s.ownerSlotLists ++ [ownerOccurrencePrefix q s.slotTrace S] := by
        simpa [t, hS, hcursor] using hpass.1
      have hsizes' : t.ownerSizes =
          s.ownerSizes ++ [(ownerOccurrencePrefix q s.slotTrace S).length] := by
        simpa [t, hS, hcursor] using hpass.2.1
      have howner' : t.ownerCursor = q + 1 := by
        simpa [t, hS, hcursor] using hpass.2.2.1
      have hscan' : t.ownerScanCursor = 0 := by
        simpa [t, hS, hcursor] using hpass.2.2.2.1
      have hacc' : t.ownerSlotAcc = [] := by
        simpa [t, hS, hcursor] using hpass.2.2.2.2.1
      have htrace' : t.slotTrace = s.slotTrace := by
        simpa [t, hS, hcursor] using hpass.2.2.2.2.2.1
      have hparsed' : parsedInput t = some input := by
        simpa [t, hS, hcursor] using hpass.2.2.2.2.2.2.1
      have hphase' : t.phase = .ownerScan := by
        simpa [t, hS, hcursor] using hpass.2.2.2.2.2.2.2
      have hlists'' : t.ownerSlotLists =
          baseLists ++ [ownerOccurrencePrefix q s.slotTrace S] := by
        simpa [hlists, hcursor, hS] using hlists'
      have hsizes'' : t.ownerSizes =
          baseSizes ++ [(ownerOccurrencePrefix q s.slotTrace S).length] := by
        simpa [hsizes, hcursor, hS] using hsizes'
      have hprev := ih (q + 1) t (by omega)
        (baseLists ++ [ownerOccurrencePrefix q s.slotTrace S])
        (baseSizes ++ [(ownerOccurrencePrefix q s.slotTrace S).length])
        (by simpa [htrace'] using hS) hparsed' (by simpa [howner'] using howner')
        hscan' hacc' hlists'' hsizes'' hphase'
      rcases hprev with ⟨hl, hs, ho, hsc, ha, ht, hp, hph⟩
      refine ⟨?_, ?_, ?_, hsc, ha, ?_, hp, hph⟩
      · rw [ownerOccurrenceBlocks_succ]
        simpa [runOwnerBlocks, List.append_assoc, htrace'] using hl
      · rw [ownerOccurrenceBlocks_succ, List.map_append]
        simpa [runOwnerBlocks, List.append_assoc, htrace'] using hs
      · omega
      · exact ht.trans htrace'

/-- The full actual owner-filter phase, including the final transition to
port enumeration, stores exactly one filtered source-slot list per owner. -/
theorem runAllOwnerSlots_complete (input : Input) (s : State)
    (S : Nat) (htraceLen : s.slotTrace.length = S)
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = 0)
    (hscan : s.ownerScanCursor = 0) (hacc : s.ownerSlotAcc = [])
    (hlists : s.ownerSlotLists = []) (hsizes : s.ownerSizes = [])
    (hphase : s.phase = .ownerScan) :
    let q := runOwnerBlocks S input.variables s
    let t := step q
    t.phase = .portTags ∧ t.ownerCursor = 0 ∧
    t.ownerSlotLists =
      ownerOccurrenceBlocks s.slotTrace 0 input.variables ∧
    t.ownerSizes =
      (ownerOccurrenceBlocks s.slotTrace 0 input.variables).map List.length := by
  have hblocks := runOwnerBlocks_exact input s S 0 input.variables
    (by omega) [] [] htraceLen hparsed hcursor hscan hacc hlists hsizes hphase
  let q := runOwnerBlocks S input.variables s
  have hparsedQ : parsedInput q = some input := by simpa [q] using hblocks.2.2.2.2.2.2.1
  have hownerQ : q.ownerCursor = input.variables := by simpa [q] using hblocks.2.2.1
  have hphaseQ : q.phase = .ownerScan := by simpa [q] using hblocks.2.2.2.2.2.2.2
  have hlistQ : q.ownerSlotLists =
      ownerOccurrenceBlocks s.slotTrace 0 input.variables := by
    simpa [q] using hblocks.1
  have hsizeQ : q.ownerSizes =
      (ownerOccurrenceBlocks s.slotTrace 0 input.variables).map List.length := by
    simpa [q] using hblocks.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [step, hphaseQ, ownerScanStep, hparsedQ, hownerQ]
  · simp [step, hphaseQ, ownerScanStep, hparsedQ, hownerQ]
  · simpa [step, hphaseQ, ownerScanStep, hparsedQ, hownerQ] using hlistQ
  · simpa [step, hphaseQ, ownerScanStep, hparsedQ, hownerQ] using hsizeQ

/-- After the real all-owner scan, both state vectors are the exact Fin-indexed
allocation occurrence lists and their lengths. -/
theorem runAllOwnerSlots_complete_typed (input : Input) (s : State)
    (htrace : s.slotTrace =
      sourceSlotTracePrefix input (input.equations.length * 3) (by omega))
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = 0)
    (hscan : s.ownerScanCursor = 0) (hacc : s.ownerSlotAcc = [])
    (hlists : s.ownerSlotLists = []) (hsizes : s.ownerSizes = [])
    (hphase : s.phase = .ownerScan) :
    let q := runOwnerBlocks s.slotTrace.length input.variables s
    let t := step q
    t.phase = .portTags ∧ t.ownerCursor = 0 ∧
      t.ownerSlotLists = (List.finRange input.variables).map (fun v =>
        ((allocation input).occurrenceList v).map
          (fun o => 3 * o.1.val + o.2.val)) ∧
      t.ownerSizes = ((List.finRange input.variables).map (fun v =>
        ((allocation input).occurrenceList v).map
          (fun o => 3 * o.1.val + o.2.val))).map List.length := by
  let q := runOwnerBlocks s.slotTrace.length input.variables s
  let t := step q
  have hall := runAllOwnerSlots_complete input s s.slotTrace.length
    rfl hparsed hcursor hscan hacc hlists hsizes hphase
  have htyped := ownerOccurrenceBlocks_eq_occurrenceLists input 0 input.variables
    (by omega)
  rcases hall with ⟨hp, hc, hlist, hsize⟩
  have hlist' : t.ownerSlotLists = (List.finRange input.variables).map (fun v =>
      ((allocation input).occurrenceList v).map
        (fun o => 3 * o.1.val + o.2.val)) := by
    dsimp [t, q] at hlist ⊢
    rw [htrace] at hlist
    exact hlist.trans htyped
  have hsize' : t.ownerSizes =
      ((List.finRange input.variables).map (fun v =>
        ((allocation input).occurrenceList v).map
          (fun o => 3 * o.1.val + o.2.val))).map List.length := by
    dsimp [t, q] at hsize ⊢
    rw [htrace] at hsize
    simpa [htyped] using hsize
  exact ⟨by simpa [t, q] using hp, by simpa [t, q] using hc,
    hlist', hsize'⟩

/-- Port-tag emissions are separated by one explicit occurrence-rollover
transition. The resulting prefix is occurrence-major, then local-port-major. -/
def portTagStepPrefix (owner : Nat) : Nat → List (Nat × Nat × Nat × Nat)
  | 0 => []
  | q + 1 => portTagStepPrefix owner q ++
      (if q % (cloudDegree + 1) < cloudDegree then
        [(0, owner, q / (cloudDegree + 1), q % (cloudDegree + 1))]
      else [])

def runPortTagForward : Nat → State → State
  | 0, s => s
  | k + 1, s => runPortTagForward k (portTagStep s)

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


/-- Every port-tag phase prefix emits exactly its ordered owner/occurrence/
label prefix and maintains the quotient/remainder cursor decomposition. -/
theorem runPortTagForward_prefix (input : Input) (s : State)
    (q k occurrences : Nat) (hqk : q + k ≤ occurrences * (cloudDegree + 1))
    (baseTags : List (Nat × Nat × Nat × Nat))
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hlist : s.ownerCursor < s.ownerSlotLists.length)
    (hoccurrences :
      (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = occurrences)
    (hcursor : s.portOccurrenceCursor = q / (cloudDegree + 1))
    (hlabel : s.portLabelCursor = q % (cloudDegree + 1))
    (htags : s.variableTags = baseTags ++ portTagStepPrefix s.ownerCursor q)
    (hphase : s.phase = .portTags) :
    (runPortTagForward k s).portOccurrenceCursor =
      (q + k) / (cloudDegree + 1) ∧
    (runPortTagForward k s).portLabelCursor =
      (q + k) % (cloudDegree + 1) ∧
    (runPortTagForward k s).variableTags =
      baseTags ++ portTagStepPrefix s.ownerCursor (q + k) ∧
    (runPortTagForward k s).ownerSlotLists = s.ownerSlotLists ∧
    parsedInput (runPortTagForward k s) = some input ∧
    (runPortTagForward k s).ownerCursor = s.ownerCursor ∧
    (runPortTagForward k s).phase = .portTags := by
  induction k generalizing q s with
  | zero => simp [runPortTagForward, hcursor, hlabel, htags, hphase]
  | succ k ih =>
      have hq : q < occurrences * (cloudDegree + 1) := by omega
      have hocc : q / (cloudDegree + 1) < occurrences := by omega
      have hroll :
          (portTagStep s).portOccurrenceCursor = (q + 1) / (cloudDegree + 1) ∧
          (portTagStep s).portLabelCursor = (q + 1) % (cloudDegree + 1) := by
        by_cases hrem : q % (cloudDegree + 1) < cloudDegree
        · simp [portTagStep, hparsed, howner, hlist, hocc, hcursor,
            hlabel, hrem, hoccurrences] <;> omega
        · have hlast : q % (cloudDegree + 1) = cloudDegree := by omega
          simp [portTagStep, hparsed, howner, hlist, hocc, hcursor,
            hlabel, hrem, hlast, hoccurrences] <;> omega
      have htags' : (portTagStep s).variableTags =
          baseTags ++ portTagStepPrefix s.ownerCursor (q + 1) := by
        by_cases hrem : q % (cloudDegree + 1) < cloudDegree
        · have hlabelBound : s.portLabelCursor < cloudDegree := by omega
          rw [portTagStep_appends_exact_tag s input hparsed howner hlist
            (by omega) hlabelBound]
          rw [htags]
          simp [portTagStepPrefix, hcursor, hlabel, hrem, List.append_assoc]
        · have hlabelBound : ¬ s.portLabelCursor < cloudDegree := by omega
          have hoccBound :
              s.portOccurrenceCursor <
                (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length := by omega
          simp [portTagStep, hparsed, howner, hlist, hoccBound, hlabelBound,
            htags, portTagStepPrefix, hcursor, hlabel, hrem]
      have hlist' : (portTagStep s).ownerSlotLists = s.ownerSlotLists := by
        simp [portTagStep, hparsed, howner, hlist, hocc, hcursor, hlabel,
          hoccurrences, hq]
      have hparsed' : parsedInput (portTagStep s) = some input := by
        simp [parsedInput, portTagStep, hparsed, howner, hlist, hocc,
          hcursor, hlabel, hoccurrences, hq]
      have howner' : (portTagStep s).ownerCursor = s.ownerCursor := by
        simp [portTagStep, hparsed, howner, hlist, hocc, hcursor, hlabel,
          hoccurrences, hq]
      have hphase' : (portTagStep s).phase = .portTags := by
        simp [portTagStep, hparsed, howner, hlist, hocc, hcursor, hlabel,
          hoccurrences, hq, hphase]
      have hprev := ih (q + 1) (portTagStep s) (by omega)
        (by simpa [howner'] using hparsed')
        (by simpa [howner'] using howner) (by simpa [howner', hlist'] using hlist)
        (by simpa [howner', hlist'] using hoccurrences)
        hroll.1 hroll.2 htags' hphase'
      rcases hprev with ⟨ho, hl, ht, hls, hp, hov, hph⟩
      exact ⟨ho, hl, ht, hls.trans hlist', hp, hov.trans howner', hph⟩

/-- A complete owner port pass emits all occurrence-major port tags and the
single boundary transition enters the same owner's cloud-dart scan. -/
theorem runPortTag_complete (input : Input) (s : State)
    (occurrences : Nat) (baseTags : List (Nat × Nat × Nat × Nat))
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hlist : s.ownerCursor < s.ownerSlotLists.length)
    (hoccurrences :
      (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = occurrences)
    (hcursor : s.portOccurrenceCursor = 0)
    (hlabel : s.portLabelCursor = 0)
    (htags : s.variableTags = baseTags)
    (hphase : s.phase = .portTags) :
    let t := portTagStep (runPortTagForward (occurrences * (cloudDegree + 1)) s)
    t.phase = .cloudDarts ∧
    t.variableTags = baseTags ++
      (List.range occurrences).flatMap fun occurrence =>
        (List.range cloudDegree).map fun label => (0, s.ownerCursor, occurrence, label) := by
  have hpref := runPortTagForward_prefix input s 0 (occurrences * (cloudDegree + 1))
    occurrences (by omega) baseTags hparsed howner hlist hoccurrences
    hcursor hlabel (by simpa [htags]) hphase
  rcases hpref with ⟨ho, hl, ht, hls, hp, hov, hph⟩
  have hboundary :
      (portTagStep (runPortTagForward (occurrences * (cloudDegree + 1)) s)).phase =
        .cloudDarts := by
    simp [portTagStep, hp, howner, hlist, hls, hov, hoccurrences, ho, hl,
      occurrences]
  have htagsEq :
      portTagStepPrefix s.ownerCursor (occurrences * (cloudDegree + 1)) =
        (List.range occurrences).flatMap fun occurrence =>
          (List.range cloudDegree).map fun label =>
            (0, s.ownerCursor, occurrence, label) := by
    induction occurrences with
    | zero => rfl
    | succ occ ih =>
        simp [portTagStepPrefix, Nat.mul_succ, ih, Nat.add_mul,
          List.range_succ, List.flatMap_append, List.flatMap_map]
  exact ⟨hboundary, by simpa [ht, htagsEq]⟩

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

/-- Prefix of the actual fixed-order dart enumeration used by one cloud.
Every cursor inspects exactly one vertex-port-dart-label tuple; a tuple
contributes only when the source's rank-based representative test accepts it. -/
def selectedDartPrefix (n : Nat) : Nat → List (Nat × Nat × Nat × Nat × Nat × Nat)
  | 0 => []
  | k + 1 => selectedDartPrefix n k ++ selectedDart n k

/-- Dedicated forward iterator for the concrete cloud scan transition. -/
def runCloudDartsForward : Nat → State → State
  | 0, s => s
  | k + 1, s => runCloudDartsForward k (cloudDartsStep s)

/-- Every cloud-scan prefix contains exactly the accepted tuples among the
first k actual product ordinals, in product order. -/
/-- The row emitted for a typed source dart, or no row when it is the reverse
non-representative. -/
def sourceRepresentativeChunk {n : Nat} (d : ActualGraphEdges.Dart n) :
    List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  let r := ActualGraphEdges.reverse d
  if ActualGraphEdges.IsRep d then
    [(d.1.1.val, d.1.2.val, d.2.val,
      r.1.1.val, r.1.2.val, r.2.val)]
  else []

theorem selectedDart_eq_sourceRepresentativeChunk (n q : Nat)
    (hq : q < n * cloudDegree * 3) :
    selectedDart n q = sourceRepresentativeChunk (sourceDartAt n q hq) := by
  let d := sourceDartAt n q hq
  have hencode : q = 3 * (d.1.1.val * cloudDegree + d.1.2.val) + d.2.val := by
    dsimp [d, sourceDartAt]
    omega
  have hn : 0 < n := by omega
  have htyped := selectedDart_typed n d.1.1.val d.1.2.val
    d.1.1.isLt d.1.2.isLt hn d.2
  rw [← hencode] at htyped
  simpa [sourceRepresentativeChunk, d] using htyped

/-- Filtering every actual row-major typed dart by `IsRep` gives exactly the
runtime's numeric representative list, including its full dart labels. -/
theorem selectedDartPrefix_eq_typedRepresentatives (n k : Nat)
    (hk : k ≤ n * cloudDegree * 3) :
    selectedDartPrefix n k =
      (sourceDartTracePrefix n k hk).flatMap sourceRepresentativeChunk := by
  induction k with
  | zero => simp [selectedDartPrefix, sourceDartTracePrefix]
  | succ k ih =>
      have hstep := selectedDart_eq_sourceRepresentativeChunk n k (by omega)
      rw [selectedDartPrefix, sourceDartTracePrefix, ih (by omega),
        List.flatMap_append, hstep]
/-- The complete runtime dart scan equals the actual typed edge list after
forgetting each edge's proof field and retaining all six numeric dart fields. -/
theorem selectedDartPrefix_eq_edgeList (n : Nat) :
    selectedDartPrefix n (n * cloudDegree * 3) =
      (ActualEqualityCloud.edgeList n).map fun e =>
        let r := ActualGraphEdges.reverse e.val
        (e.val.1.1.val, e.val.1.2.val, e.val.2.val,
          r.1.1.val, r.1.2.val, r.2.val) := by
  rw [selectedDartPrefix_eq_typedRepresentatives,
    sourceDartTracePrefix_eq_dartList]
  simp [sourceRepresentativeChunk, ActualEqualityCloud.edgeList,
    ActualGraphEdges.representativeList, ActualGraphEdges.dartList,
    ActualGraphEdges.IsRep, List.flatMap, List.map_map, Function.comp_def]
theorem runCloudDartsForward_prefix (input : Input) (s : State)
    (q k n : Nat) (hqk : q + k ≤ n * cloudDegree * 3)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hn : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hcursor : s.ownerScanCursor = q)
    (hacc : s.cloudRepAcc = selectedDartPrefix n q)
    (hphase : s.phase = .cloudDarts) :
    (runCloudDartsForward k s).ownerScanCursor = q + k ∧
    (runCloudDartsForward k s).cloudRepAcc = selectedDartPrefix n (q + k) ∧
    parsedInput (runCloudDartsForward k s) = some input ∧
    (runCloudDartsForward k s).ownerCursor = s.ownerCursor ∧
    (runCloudDartsForward k s).ownerSizes = s.ownerSizes ∧
    (runCloudDartsForward k s).phase = .cloudDarts := by
  induction k generalizing q s with
  | zero =>
      simp [runCloudDartsForward, hcursor, hacc, hparsed, hphase]
  | succ k ih =>
      have hq : q < n * cloudDegree * 3 := by omega
      have hcursor' : (cloudDartsStep s).ownerScanCursor = q + 1 := by
        simpa [hcursor, hn] using
          cloudDartsStep_increments s input hparsed howner hsize
            (by simpa [hcursor, hn] using hq)
      have hacc' : (cloudDartsStep s).cloudRepAcc = selectedDartPrefix n (q + 1) := by
        rw [cloudDartsStep_appends_selected s input hparsed howner hsize
          (by simpa [hcursor, hn] using hq), hacc]
        simp [selectedDartPrefix, hcursor]
      have hparsed' : parsedInput (cloudDartsStep s) = some input := by
        simp [parsedInput, cloudDartsStep, hparsed, howner, hsize,
          hcursor, hn, hq]
      have howner' : (cloudDartsStep s).ownerCursor = s.ownerCursor := by
        simp [cloudDartsStep, hparsed, howner, hsize, hcursor, hn, hq]
      have hsize' : (cloudDartsStep s).ownerSizes = s.ownerSizes := by
        simp [cloudDartsStep, hparsed, howner, hsize, hcursor, hn, hq]
      have hphase' : (cloudDartsStep s).phase = .cloudDarts := by
        simp [cloudDartsStep, hparsed, howner, hsize, hcursor, hn, hq, hphase]
      have hprev := ih (q + 1) (cloudDartsStep s) (by omega)
        hparsed' (by simpa [howner'] using howner)
        (by simpa [hsize'] using hsize)
        (by simpa [howner', hsize'] using hn) hcursor' hacc' hphase'
      rcases hprev with ⟨hc, ha, hp, ho, hs, hph⟩
      exact ⟨by omega, by simpa [runCloudDartsForward] using ha,
        hp, ho.trans howner', hs.trans hsize', hph⟩

/-- One full cloud scan commits precisely the accepted fixed-order dart list
and enters internal-tag enumeration. -/
theorem runCloudDarts_complete (input : Input) (s : State) (n : Nat)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hn : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hcursor : s.ownerScanCursor = 0) (hacc : s.cloudRepAcc = [])
    (hphase : s.phase = .cloudDarts) :
    let t := cloudDartsStep (runCloudDartsForward (n * cloudDegree * 3) s)
    t.phase = .internalTags ∧
    t.cloudRepAcc = selectedDartPrefix n (n * cloudDegree * 3) ∧
    t.ownerScanCursor = n * cloudDegree * 3 := by
  have hpref := runCloudDartsForward_prefix input s 0 (n * cloudDegree * 3) n
    (by omega) hparsed howner hsize hn hcursor (by simpa [hacc]) hphase
  rcases hpref with ⟨hc, ha, hp, ho, hs, hph⟩
  have hboundary :
      (cloudDartsStep (runCloudDartsForward (n * cloudDegree * 3) s)).phase =
        .internalTags := by
    simp [cloudDartsStep, hp, howner, hsize, hn, hc, ho, hs]
  have haccBoundary :
      (cloudDartsStep (runCloudDartsForward (n * cloudDegree * 3) s)).cloudRepAcc =
        selectedDartPrefix n (n * cloudDegree * 3) := by
    simp [cloudDartsStep, hp, howner, hsize, hn, hc, ho, hs]
  have hcursorBoundary :
      (cloudDartsStep (runCloudDartsForward (n * cloudDegree * 3) s)).ownerScanCursor =
        n * cloudDegree * 3 := by
    simp [cloudDartsStep, hp, howner, hsize, hn, hc, ho, hs]
  exact ⟨hboundary, haccBoundary, hcursorBoundary⟩

/-- The emitted internal-tag prefix for a phase clock. Every edge occupies six
transition ordinals: five output labels followed by a cursor-rollover step. -/
def internalTagStepPrefix (owner : Nat) : Nat → List (Nat × Nat × Nat × Nat)
  | 0 => []
  | q + 1 => internalTagStepPrefix owner q ++
      (if q % 6 < 5 then [(1, owner, q / 6, q % 6)] else [])

/-- Dedicated forward iterator for the actual six-transition-per-edge
internal-tag phase. -/
def runInternalTagForward : Nat → State → State
  | 0, s => s
  | k + 1, s => runInternalTagForward k (internalTagStep s)

/-- Every prefix of internal-tag transitions has exact edge/label cursors,
the literal emitted-tag prefix, and leaves the chosen representative list in
place. -/
theorem runInternalTagForward_prefix (input : Input) (s : State)
    (q k : Nat) (hqk : q + k ≤ s.cloudRepAcc.length * 6)
    (baseTags : List (Nat × Nat × Nat × Nat))
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.edgeOccurrenceCursor = q / 6)
    (hlabel : s.internalLabelCursor = q % 6)
    (htags : s.variableTags = baseTags ++ internalTagStepPrefix s.ownerCursor q)
    (hphase : s.phase = .internalTags) :
    (runInternalTagForward k s).edgeOccurrenceCursor = (q + k) / 6 ∧
    (runInternalTagForward k s).internalLabelCursor = (q + k) % 6 ∧
    (runInternalTagForward k s).variableTags =
      baseTags ++ internalTagStepPrefix s.ownerCursor (q + k) ∧
    (runInternalTagForward k s).cloudRepAcc = s.cloudRepAcc ∧
    parsedInput (runInternalTagForward k s) = some input ∧
    (runInternalTagForward k s).ownerCursor = s.ownerCursor ∧
    (runInternalTagForward k s).phase = .internalTags := by
  induction k generalizing q s with
  | zero =>
      simp [runInternalTagForward, hcursor, hlabel, htags, hphase]
  | succ k ih =>
      have hq : q < s.cloudRepAcc.length * 6 := by omega
      have hedge : q / 6 < s.cloudRepAcc.length := by omega
      have hnext :
          (internalTagStep s).edgeOccurrenceCursor = (q + 1) / 6 ∧
          (internalTagStep s).internalLabelCursor = (q + 1) % 6 := by
        by_cases hrem : q % 6 < 5
        · simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel,
            hrem] <;> omega
        · have hfive : q % 6 = 5 := by omega
          simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel,
            hrem, hfive] <;> omega
      have htags' : (internalTagStep s).variableTags =
          baseTags ++ internalTagStepPrefix s.ownerCursor (q + 1) := by
        by_cases hrem : q % 6 < 5
        · have hl : s.internalLabelCursor < 5 := by omega
          rw [internalTagStep_appends_tag s input hparsed howner hedge hl]
          rw [htags]
          simp [internalTagStepPrefix, hcursor, hlabel, hrem, List.append_assoc]
        · have hl : ¬ s.internalLabelCursor < 5 := by omega
          simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel, hl,
            htags, internalTagStepPrefix, hrem]
      have hcloud' : (internalTagStep s).cloudRepAcc = s.cloudRepAcc := by
        by_cases hrem : q % 6 < 5
        · simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel, hrem]
        · simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel, hrem]
      have hparsed' : parsedInput (internalTagStep s) = some input := by
        simp [parsedInput, internalTagStep, hparsed, howner, hedge, hcursor,
          hlabel, hq]
      have howner' : (internalTagStep s).ownerCursor = s.ownerCursor := by
        simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel, hq]
      have hphase' : (internalTagStep s).phase = .internalTags := by
        simp [internalTagStep, hparsed, howner, hedge, hcursor, hlabel, hq,
          hphase]
      have hcursor' : (internalTagStep s).edgeOccurrenceCursor = (q + 1) / 6 :=
        hnext.1
      have hlabel' : (internalTagStep s).internalLabelCursor = (q + 1) % 6 :=
        hnext.2
      have hprev := ih (q + 1) (internalTagStep s) (by omega)
        (by simpa [howner'] using hparsed') (by simpa [howner'] using howner)
        (by simpa [hcursor'] using hcursor') (by simpa [hlabel'] using hlabel')
        (by simpa [htags'] using htags') hphase'
      rcases hprev with ⟨he, hl, ht, hc, hp, ho, hph⟩
      exact ⟨he, hl, ht, hc.trans hcloud', hp, ho.trans howner', hph⟩

/-- Completing the internal-tag loop appends precisely the five labels for
each stored representative dart, in representative-list order, and commits
that exact cloud to representativeClouds. -/
theorem runInternalTag_complete (input : Input) (s : State)
    (baseTags : List (Nat × Nat × Nat × Nat))
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hcursor : s.edgeOccurrenceCursor = 0)
    (hlabel : s.internalLabelCursor = 0)
    (htags : s.variableTags = baseTags)
    (hphase : s.phase = .internalTags) :
    let e := s.cloudRepAcc.length
    let t := internalTagStep (runInternalTagForward (6 * e) s)
    t.phase = .portTags ∧ t.ownerCursor = s.ownerCursor + 1 ∧
    t.variableTags = baseTags ++
      ((List.range e).flatMap fun edge =>
        (List.range 5).map fun label => (1, s.ownerCursor, edge, label)) ∧
    t.representativeClouds = s.representativeClouds ++ [s.cloudRepAcc] := by
  let e := s.cloudRepAcc.length
  have hpref := runInternalTagForward_prefix input s 0 (6 * e) (by omega)
    baseTags hparsed howner hcursor hlabel (by simpa [htags]) hphase
  rcases hpref with ⟨he, hl, ht, hc, hp, ho, hph⟩
  have hend : (runInternalTagForward (6 * e) s).edgeOccurrenceCursor = e := by
    simpa [e] using he
  have htagsEq :
      internalTagStepPrefix s.ownerCursor (6 * e) =
        (List.range e).flatMap fun edge =>
          (List.range 5).map fun label => (1, s.ownerCursor, edge, label) := by
    induction e with
    | zero => rfl
    | succ e ih =>
        simp [internalTagStepPrefix, Nat.mul_succ, ih,
          List.range_succ, List.flatMap_append, List.flatMap_map]
  exact ⟨by simp [internalTagStep, hp, howner, hend, hc],
    by simp [internalTagStep, hp, howner, hend, hc],
    by simpa [internalTagStep, hp, howner, hend, hc, ht, htagsEq],
    by simp [internalTagStep, hp, howner, hend, hc]⟩

/-- Compose one actual cloud-dart scan with its internal-tag scan. Starting
from the cloud phase, the concrete dispatcher components commit exactly the
rank-filtered dart list, emit its five labels per representative, and advance
to the next owner's port phase. -/
theorem runCloudAndInternal_complete (input : Input) (s : State) (n : Nat)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hn : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hcursor : s.ownerScanCursor = 0) (hacc : s.cloudRepAcc = [])
    (hphase : s.phase = .cloudDarts) :
    let N := n * cloudDegree * 3
    let darts := selectedDartPrefix n N
    let e := darts.length
    let c := cloudDartsStep (runCloudDartsForward N s)
    let t := internalTagStep (runInternalTagForward (6 * e) c)
    t.phase = .portTags ∧
    t.ownerCursor = s.ownerCursor + 1 ∧
    t.variableTags = s.variableTags ++
      ((List.range e).flatMap fun edge =>
        (List.range 5).map fun label => (1, s.ownerCursor, edge, label)) ∧
    t.representativeClouds = s.representativeClouds ++ [darts] := by
  let N := n * cloudDegree * 3
  let darts := selectedDartPrefix n N
  let e := darts.length
  let u := runCloudDartsForward N s
  have hpref := runCloudDartsForward_prefix input s 0 N n (by omega)
    hparsed howner hsize hn hcursor (by simpa [hacc]) hphase
  rcases hpref with ⟨hucursor, huacc, huparsed, huowner, husizes, uphase⟩
  have hphaseC : (cloudDartsStep u).phase = .internalTags := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N, u]
  have haccC : (cloudDartsStep u).cloudRepAcc = darts := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N,
      huacc, darts, u]
  have hparsedC : parsedInput (cloudDartsStep u) = some input := by
    simp [parsedInput, cloudDartsStep, huparsed, huowner, husizes, hn,
      hucursor, N, u]
  have hownerC : (cloudDartsStep u).ownerCursor = s.ownerCursor := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N, u]
  have hcursorC : (cloudDartsStep u).edgeOccurrenceCursor = 0 := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N, u]
  have hlabelC : (cloudDartsStep u).internalLabelCursor = 0 := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N, u]
  have htagsC : (cloudDartsStep u).variableTags = s.variableTags := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N, u]
  have hrepresentativesC :
      (cloudDartsStep u).representativeClouds = s.representativeClouds := by
    simp [cloudDartsStep, huparsed, huowner, husizes, hn, hucursor, N, u]
  have hinternalRaw := runInternalTag_complete input (cloudDartsStep u)
    s.variableTags hparsedC (by simpa [hownerC] using howner)
    hcursorC hlabelC (by simpa [htagsC]) hphaseC
  have hinternal := by
    simpa [haccC, e, darts] using hinternalRaw
  rcases hinternal with ⟨hphaseT, hownerT, htagsT, hcloudsT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hphaseT
  · simpa [hownerC] using hownerT
  · simpa [htagsC, e, darts] using htagsT
  · simpa [hrepresentativesC, haccC, darts] using hcloudsT

/-- A completed real cloud scan appends exactly the internal variables indexed
by the actual typed edge list, and commits the numeric full-dart projection in
the same order. -/
theorem runCloudAndInternal_complete_edgeList (input : Input) (s : State)
    (n : Nat) (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hn : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hcursor : s.ownerScanCursor = 0) (hacc : s.cloudRepAcc = [])
    (hphase : s.phase = .cloudDarts) :
    let N := n * cloudDegree * 3
    let darts := selectedDartPrefix n N
    let e := darts.length
    let c := cloudDartsStep (runCloudDartsForward N s)
    let t := internalTagStep (runInternalTagForward (6 * e) c)
    t.variableTags = s.variableTags ++
      ((List.range (ActualEqualityCloud.edgeList n).length).flatMap fun edge =>
        (List.range 5).map fun label => (1, s.ownerCursor, edge, label)) ∧
    t.representativeClouds = s.representativeClouds ++
      [(ActualEqualityCloud.edgeList n).map fun edge =>
        let r := ActualGraphEdges.reverse edge.val
        (edge.val.1.1.val, edge.val.1.2.val, edge.val.2.val,
          r.1.1.val, r.1.2.val, r.2.val)] := by
  let N := n * cloudDegree * 3
  let darts := selectedDartPrefix n N
  let e := darts.length
  let c := cloudDartsStep (runCloudDartsForward N s)
  let t := internalTagStep (runInternalTagForward (6 * e) c)
  have hmain := runCloudAndInternal_complete input s n
    hparsed howner hsize hn hcursor hacc hphase
  have hmain' :
      t.phase = .portTags ∧
      t.ownerCursor = s.ownerCursor + 1 ∧
      t.variableTags = s.variableTags ++
        ((List.range e).flatMap fun edge =>
          (List.range 5).map fun label => (1, s.ownerCursor, edge, label)) ∧
      t.representativeClouds = s.representativeClouds ++ [darts] := by
    simpa [N, darts, e, c, t] using hmain
  have hedge := selectedDartPrefix_eq_edgeList n
  have he : e = (ActualEqualityCloud.edgeList n).length := by
    dsimp [e, darts, N]
    rw [hedge]
    simp
  rcases hmain' with ⟨_, _, htags, hcloud⟩
  constructor
  · simpa [he] using htags
  · simpa [hedge] using hcloud
/-- One owner’s concrete machine block: port enumeration, the boundary
transition, the typed representative-dart scan, and internal-label emission.
Every phase is an iteration of the actual dispatcher components above. -/
def runOneOwnerTagBlock (n : Nat) (s : State) : State :=
  let p := portTagStep (runPortTagForward (n * (cloudDegree + 1)) s)
  let N := n * cloudDegree * 3
  let darts := selectedDartPrefix n N
  let c := cloudDartsStep (runCloudDartsForward N p)
  internalTagStep (runInternalTagForward (6 * darts.length) c)

/-- The one-owner machine block appends exactly the numeric serialization
of its port variables followed by its actual typed-edge internal variables.
The owner’s edge order is the source `edgeList`, not an arbitrary enumeration. -/
theorem runOneOwnerTagBlock_complete (input : Input) (s : State) (n : Nat)
    (baseTags : List (Nat × Nat × Nat × Nat))
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hlist : s.ownerCursor < s.ownerSlotLists.length)
    (hocc : (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = n)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hsizeEq : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (htags : s.variableTags = baseTags) (hphase : s.phase = .portTags) :
    let t := runOneOwnerTagBlock n s
    t.phase = .portTags ∧ t.ownerCursor = s.ownerCursor + 1 ∧
      t.variableTags =
        baseTags ++
          ((List.range n).flatMap fun occurrence =>
            (List.range cloudDegree).map fun label =>
              (0, s.ownerCursor, occurrence, label)) ++
          ((List.range (ActualEqualityCloud.edgeList n).length).flatMap fun edge =>
            (List.range 5).map fun label =>
              (1, s.ownerCursor, edge, label)) := by
  let p := portTagStep (runPortTagForward (n * (cloudDegree + 1)) s)
  let N := n * cloudDegree * 3
  let darts := selectedDartPrefix n N
  let c := cloudDartsStep (runCloudDartsForward N p)
  let t := internalTagStep (runInternalTagForward (6 * darts.length) c)
  have hprefix := runPortTagForward_prefix input s 0
    (n * (cloudDegree + 1)) n (by omega) baseTags hparsed howner hlist
    hocc hpc hlc (by simpa [htags]) hphase
  rcases hprefix with ⟨hoccEnd, hlabEnd, htagsPort, hlistsPort,
    hparsedPort, hownerPort, hphasePort⟩
  have hport := runPortTag_complete input s n baseTags hparsed howner hlist
    hocc hpc hlc htags hphase
  have hphaseP : p.phase = .cloudDarts := by simpa [p] using hport.1
  have htagsP : p.variableTags = baseTags ++
      (List.range n).flatMap (fun occurrence =>
        (List.range cloudDegree).map fun label =>
          (0, s.ownerCursor, occurrence, label)) := by
    simpa [p] using hport.2
  have hparsedP : parsedInput p = some input := by
    simpa [p] using hparsed
  have hownerP : p.ownerCursor = s.ownerCursor := by
    simp [p, portTagStep, hparsed, howner, hlist, hoccEnd, hlabEnd, hocc]
  have hsizeP : p.ownerSizes = s.ownerSizes := by
    simp [p, portTagStep, hparsed, howner, hlist, hoccEnd, hlabEnd, hocc]
  have hcursorP : p.ownerScanCursor = 0 := by
    simp [p, portTagStep, hparsed, howner, hlist, hoccEnd, hlabEnd, hocc]
  have haccP : p.cloudRepAcc = [] := by
    simp [p, portTagStep, hparsed, howner, hlist, hoccEnd, hlabEnd, hocc]
  have hsizeP' : p.ownerCursor < p.ownerSizes.length := by
    rw [hownerP, hsizeP]
    exact hsize
  have hnP : p.ownerSizes.get ⟨p.ownerCursor, by omega⟩ = n := by
    rw [hownerP, hsizeP]
    exact hsizeEq
  have hcloud := runCloudAndInternal_complete input p n
    hparsedP (by simpa [hownerP] using howner) hsizeP' hnP hcursorP haccP hphaseP
  have hedge := selectedDartPrefix_eq_edgeList n
  have he : darts.length = (ActualEqualityCloud.edgeList n).length := by
    dsimp [darts, N]
    rw [hedge]
    simp
  rcases hcloud with ⟨hphaseT, hownerT, htagsT, hcloudT⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [runOneOwnerTagBlock, p, N, darts, c, t] using hphaseT
  · simpa [runOneOwnerTagBlock, p, N, darts, c, t, hownerP] using hownerT
  · simpa [runOneOwnerTagBlock, p, N, darts, c, t, htagsP, he,
      List.append_assoc] using htagsT
/-- Values of the canonical Fin enumeration are the ordinary bounded
counter sequence used by the unary state machine. -/
/-- Untouched projections for the actual scan primitives. Iteration proofs use
these one-step equalities, rather than relying on simp to unroll unknown loop
counts. -/
theorem portTagStep_ownerSlotLists (s : State) : (portTagStep s).ownerSlotLists = s.ownerSlotLists := by
  simp [portTagStep, invalidState]
theorem portTagStep_ownerSizes (s : State) : (portTagStep s).ownerSizes = s.ownerSizes := by
  simp [portTagStep, invalidState]
theorem portTagStep_representativeClouds (s : State) :
    (portTagStep s).representativeClouds = s.representativeClouds := by
  simp [portTagStep, invalidState]theorem portTagStep_parsedInput (s : State) : parsedInput (portTagStep s) = parsedInput s := by
  simp [parsedInput, portTagStep, invalidState]
theorem runPortTagForward_ownerSlotLists (k : Nat) (s : State) :
    (runPortTagForward k s).ownerSlotLists = s.ownerSlotLists := by
  induction k with | zero => rfl | succ k ih => simp [runPortTagForward, ih, portTagStep_ownerSlotLists]
theorem runPortTagForward_ownerSizes (k : Nat) (s : State) :
    (runPortTagForward k s).ownerSizes = s.ownerSizes := by
  induction k with | zero => rfl | succ k ih => simp [runPortTagForward, ih, portTagStep_ownerSizes]
theorem runPortTagForward_representativeClouds (k : Nat) (s : State) :
    (runPortTagForward k s).representativeClouds = s.representativeClouds := by
  induction k with
  | zero => rfl
  | succ k ih => simp [runPortTagForward, ih, portTagStep_representativeClouds]theorem runPortTagForward_parsedInput (k : Nat) (s : State) :
    parsedInput (runPortTagForward k s) = parsedInput s := by
  induction k with | zero => rfl | succ k ih => simp [runPortTagForward, ih, portTagStep_parsedInput]
theorem cloudDartsStep_ownerSlotLists (s : State) : (cloudDartsStep s).ownerSlotLists = s.ownerSlotLists := by
  simp [cloudDartsStep, invalidState]
theorem cloudDartsStep_ownerSizes (s : State) : (cloudDartsStep s).ownerSizes = s.ownerSizes := by
  simp [cloudDartsStep, invalidState]
theorem cloudDartsStep_parsedInput (s : State) : parsedInput (cloudDartsStep s) = parsedInput s := by
  simp [parsedInput, cloudDartsStep, invalidState]
theorem cloudDartsStep_variableTags (s : State) : (cloudDartsStep s).variableTags = s.variableTags := by
  simp [cloudDartsStep, invalidState]
theorem runCloudDartsForward_ownerSlotLists (k : Nat) (s : State) :
    (runCloudDartsForward k s).ownerSlotLists = s.ownerSlotLists := by
  induction k with | zero => rfl | succ k ih => simp [runCloudDartsForward, ih, cloudDartsStep_ownerSlotLists]
theorem runCloudDartsForward_ownerSizes (k : Nat) (s : State) :
    (runCloudDartsForward k s).ownerSizes = s.ownerSizes := by
  induction k with | zero => rfl | succ k ih => simp [runCloudDartsForward, ih, cloudDartsStep_ownerSizes]
theorem runCloudDartsForward_parsedInput (k : Nat) (s : State) :
    parsedInput (runCloudDartsForward k s) = parsedInput s := by
  induction k with | zero => rfl | succ k ih => simp [runCloudDartsForward, ih, cloudDartsStep_parsedInput]
theorem runCloudDartsForward_variableTags (k : Nat) (s : State) :
    (runCloudDartsForward k s).variableTags = s.variableTags := by
  induction k with | zero => rfl | succ k ih => simp [runCloudDartsForward, ih, cloudDartsStep_variableTags]
theorem internalTagStep_ownerSlotLists (s : State) : (internalTagStep s).ownerSlotLists = s.ownerSlotLists := by
  simp [internalTagStep, invalidState]
theorem internalTagStep_ownerSizes (s : State) : (internalTagStep s).ownerSizes = s.ownerSizes := by
  simp [internalTagStep, invalidState]
theorem internalTagStep_parsedInput (s : State) : parsedInput (internalTagStep s) = parsedInput s := by
  simp [parsedInput, internalTagStep, invalidState]
theorem runInternalTagForward_ownerSlotLists (k : Nat) (s : State) :
    (runInternalTagForward k s).ownerSlotLists = s.ownerSlotLists := by
  induction k with | zero => rfl | succ k ih => simp [runInternalTagForward, ih, internalTagStep_ownerSlotLists]
theorem runInternalTagForward_ownerSizes (k : Nat) (s : State) :
    (runInternalTagForward k s).ownerSizes = s.ownerSizes := by
  induction k with | zero => rfl | succ k ih => simp [runInternalTagForward, ih, internalTagStep_ownerSizes]
theorem runInternalTagForward_parsedInput (k : Nat) (s : State) :
    parsedInput (runInternalTagForward k s) = parsedInput s := by
  induction k with | zero => rfl | succ k ih => simp [runInternalTagForward, ih, internalTagStep_parsedInput]
/-- The completed owner block returns the scheduler to a clean port phase,
leaving all parsed input and owner-indexed source data unchanged. These
projection facts support iteration over every owner, including empty clouds. -/
theorem runOneOwnerTagBlock_ready (input : Input) (s : State) (n : Nat)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hlist : s.ownerCursor < s.ownerSlotLists.length)
    (hocc : (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = n)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hsizeEq : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (hphase : s.phase = .portTags) :
    let t := runOneOwnerTagBlock n s
    t.phase = .portTags ∧ t.ownerCursor = s.ownerCursor + 1 ∧
      t.portOccurrenceCursor = 0 ∧ t.portLabelCursor = 0 ∧
      t.ownerSlotLists = s.ownerSlotLists ∧ t.ownerSizes = s.ownerSizes ∧
      parsedInput t = some input ∧ t.cloudRepAcc = [] := by
  let p := portTagStep (runPortTagForward (n * (cloudDegree + 1)) s)
  let N := n * cloudDegree * 3
  let darts := selectedDartPrefix n N
  let u := runCloudDartsForward N p
  let c := cloudDartsStep u
  let e := darts.length
  let w := runInternalTagForward (6 * e) c
  let t := internalTagStep w
  have hprefix := runPortTagForward_prefix input s 0
    (n * (cloudDegree + 1)) n (by omega) s.variableTags hparsed howner hlist
    hocc hpc hlc rfl hphase
  rcases hprefix with ⟨hoccEnd, hlabEnd, _, hlistsPort,
    hparsedPort, hownerPort, hphasePort⟩
  have hphaseP : p.phase = .cloudDarts := by
    simp [p, portTagStep, hparsedPort, hownerPort, hlistP,
      hoccEnd, hlabEnd, hocc]
  have hparsedP : parsedInput p = some input := by
    simpa [p, portTagStep_parsedInput] using hparsedPort
  have hownerP : p.ownerCursor = s.ownerCursor := by
    simp [p, portTagStep, hparsedPort, hownerPort, hlistP,
      hoccEnd, hlabEnd, hocc]
  have hsizeP : p.ownerSizes = s.ownerSizes := by
    simp [p, runPortTagForward_ownerSizes, portTagStep_ownerSizes]
  have hlistP : p.ownerSlotLists = s.ownerSlotLists := by
    simp [p, runPortTagForward_ownerSlotLists, portTagStep_ownerSlotLists]
  have hsizeP' : p.ownerCursor < p.ownerSizes.length := by
    rw [hownerP, hsizeP]
    exact hsize
  have hnP : p.ownerSizes.get ⟨p.ownerCursor, by omega⟩ = n := by
    rw [hownerP, hsizeP]
    exact hsizeEq
  have hcloudPrefix := runCloudDartsForward_prefix input p 0 N n (by omega)
    hparsedP (by simpa [hownerP] using howner) hsizeP' hnP
    (by simp [p, portTagStep, hparsedPort, hownerPort, hlistP, hoccEnd, hlabEnd, hocc])
    (by simp [selectedDartPrefix]) hphaseP
  rcases hcloudPrefix with ⟨hscanU, haccU, hparsedU, hownerU, hsizesU, hphaseU⟩
  have haccC : c.cloudRepAcc = darts := by
    simp [c, cloudDartsStep, hparsedU, hownerU, hsizesU, hscanU,
      selectedDartPrefix, haccU, N, darts]
  have hphaseC : c.phase = .internalTags := by
    simp [c, cloudDartsStep, hparsedU, hownerU, hsizesU, hnP,
      hscanU, N, darts]
  have hparsedC : parsedInput c = some input := by
    simp [parsedInput, c, cloudDartsStep, hparsedU, hownerU, hsizesU,
      hnP, hscanU, N, darts]
  have hownerC : c.ownerCursor = s.ownerCursor := by
    simp [c, cloudDartsStep, hparsedU, hownerU, hsizesU, hnP,
      hscanU, N, darts]
  have htagsC : c.variableTags = p.variableTags := by
    simp [c, runCloudDartsForward_variableTags, cloudDartsStep_variableTags]
  have hinternalPrefix := runInternalTagForward_prefix input c 0 (6 * e)
    (by rw [haccC]; omega) p.variableTags hparsedC
    (by simpa [hownerC] using howner)
    (by simp [c, cloudDartsStep, hparsedU, hownerU, hsizesU, hnP,
      hscanU, N, darts])
    (by simp [c, cloudDartsStep, hparsedU, hownerU, hsizesU, hnP,
      hscanU, N, darts])
    (by simpa [internalTagStepPrefix] using htagsC) hphaseC
  rcases hinternalPrefix with ⟨hEdge, hLabel, _, haccW, hparsedW,
    hownerW, hphaseW⟩
  have hboundary : w.edgeOccurrenceCursor = w.cloudRepAcc.length := by
    rw [hEdge, haccW, haccC]
    simp [e, darts, selectedDartPrefix_eq_edgeList]
  have hphaseT : t.phase = .portTags := by
    simp [t, internalTagStep, hparsedW, hownerW, hboundary, hphaseW]
  have hownerT : t.ownerCursor = s.ownerCursor + 1 := by
    simp [t, internalTagStep, hparsedW, hownerW, hboundary, hphaseW]
  have hportT : t.portOccurrenceCursor = 0 ∧ t.portLabelCursor = 0 := by
    simp [t, internalTagStep, hparsedW, hownerW, hboundary, hphaseW]
  have hlistT : t.ownerSlotLists = s.ownerSlotLists := by
    simp [t, w, c, u, p, runInternalTagForward_ownerSlotLists,
      internalTagStep_ownerSlotLists, runCloudDartsForward_ownerSlotLists,
      cloudDartsStep_ownerSlotLists, runPortTagForward_ownerSlotLists,
      portTagStep_ownerSlotLists]
  have hsizeT : t.ownerSizes = s.ownerSizes := by
    simp [t, w, c, u, p, runInternalTagForward_ownerSizes,
      internalTagStep_ownerSizes, runCloudDartsForward_ownerSizes,
      cloudDartsStep_ownerSizes, runPortTagForward_ownerSizes,
      portTagStep_ownerSizes]
  have hparsedT : parsedInput t = some input := by
    rw [internalTagStep_parsedInput, runInternalTagForward_parsedInput,
      cloudDartsStep_parsedInput, runCloudDartsForward_parsedInput,
      portTagStep_parsedInput, runPortTagForward_parsedInput]
    exact hparsed
  have haccT : t.cloudRepAcc = [] := by
    simp [t, internalTagStep, hparsedW, hownerW, hboundary, hphaseW]
  refine ⟨?_, ?_, hportT.1, hportT.2, hlistT, hsizeT, hparsedT, haccT⟩
  · simpa [runOneOwnerTagBlock, p, N, darts, c, u, e, w, t] using hphaseT
  · simpa [runOneOwnerTagBlock, p, N, darts, c, u, e, w, t] using hownerT
theorem finRange_val_eq_range (n : Nat) :
    (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.finRange_succ, List.range_succ, ih, List.map_map]

/-- For a nodup source list, mapping each element to its first-list position
produces every bounded numeric ordinal exactly once, in order. -/
theorem nodup_idxOf_eq_range {α : Type} [DecidableEq α]
    (xs : List α) (hn : xs.Nodup) :
    xs.map (fun x => xs.idxOf x) = List.range xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hparts := List.nodup_cons.mp hn
      have htail := ih hparts.2
      have hneq : ∀ x ∈ xs, x ≠ a := by
        intro x hx heq
        subst x
        exact hparts.1 hx
      have hmap : xs.map (fun x => (a :: xs).idxOf x) =
          xs.map (fun x => xs.idxOf x + 1) := by
        apply List.map_congr_left
        intro x hx
        simpa using List.idxOf_cons_ne xs (hneq x hx)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.idxOf_cons_self]
      rw [hmap, ← htail]
      simp [List.map_map, Function.comp_def, Nat.succ_eq_add_one]

theorem idxOf_get_eq_of_nodup {α : Type} [DecidableEq α]
    (xs : List α) (hn : xs.Nodup) (i : Fin xs.length) :
    xs.idxOf (xs.get i) = i.val := by
  have h := congrArg (fun ys : List Nat => ys.get i)
    (nodup_idxOf_eq_range xs hn)
  simpa using h

/-- The concrete local typed enumeration, mapped to the four-field runtime
wire tag (owner component fixed), is exactly the two sequential counter loops:
all occurrence/port pairs, then edge/Fin-5 pairs. -/
/-- First-list positions are injective on a nodup list. -/
theorem idxOf_injective_on_nodup {α : Type} [DecidableEq α]
    (xs : List α) (hn : xs.Nodup) {a b : α}
    (ha : a ∈ xs) (hb : b ∈ xs) (hidx : xs.idxOf a = xs.idxOf b) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      have hparts := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        rcases List.mem_cons.mp hb with hb | hb
        · simpa [hb]
        · have hne : b ≠ x := by
            intro he
            subst b
            exact hparts.1 hb
          simp [List.idxOf_cons_ne xs hne] at hidx
      · rcases List.mem_cons.mp hb with hb | hb
        · subst b
          have hne : a ≠ x := by
            intro he
            subst a
            exact hparts.1 ha
          simp [List.idxOf_cons_ne xs hne] at hidx
        · have hneA : a ≠ x := by
            intro he
            subst a
            exact hparts.1 ha
          have hneB : b ≠ x := by
            intro he
            subst b
            exact hparts.1 hb
          have htail : xs.idxOf a = xs.idxOf b := by
            simpa [List.idxOf_cons_ne xs hneA,
              List.idxOf_cons_ne xs hneB] using hidx
          exact ih hparts.2 ha hb htail
def localVariableTag (n owner : Nat) :
    ActualEqualityCloud.GlobalVar n → Nat × Nat × Nat × Nat
  | Sum.inl (occurrence, port) => (0, owner, occurrence.val, port.val)
  | Sum.inr (edge, label) =>
      (1, owner, (ActualEqualityCloud.edgeList n).idxOf edge, label.val)

theorem localVariableList_map_localVariableTag (n owner : Nat) :
    (ActualNumberedOccurrenceProducer.localVariableList n).map
      (localVariableTag n owner) =
      ((List.range n).flatMap fun occurrence =>
        (List.range cloudDegree).map fun label =>
          (0, owner, occurrence, label)) ++
      ((List.range (ActualEqualityCloud.edgeList n).length).flatMap fun edge =>
        (List.range 5).map fun label => (1, owner, edge, label)) := by
  have hfin : (List.finRange cloudDegree).map Fin.val = List.range cloudDegree :=
    finRange_val_eq_range cloudDegree
  have hedge := nodup_idxOf_eq_range (ActualEqualityCloud.edgeList n)
    (ActualEqualityCloud.edgeList_nodup n)
  simp [ActualNumberedOccurrenceProducer.localVariableList,
    localVariableTag, List.product, List.flatMap_map, List.map_map,
    finRange_val_eq_range, hfin, hedge]
/-- Numeric tag block used to state the all-owner loop invariant in the exact
owner-prefix order selected by `variableList`. -/
def runtimeOwnerTagBlock (owner n : Nat) : List (Nat × Nat × Nat × Nat) :=
  ((List.range n).flatMap fun occurrence =>
    (List.range cloudDegree).map fun label => (0, owner, occurrence, label)) ++
  ((List.range (ActualEqualityCloud.edgeList n).length).flatMap fun edge =>
    (List.range 5).map fun label => (1, owner, edge, label))

def runtimeOwnerTagBlocks : Nat → List Nat → List (Nat × Nat × Nat × Nat)
  | _, [] => []
  | owner, n :: ns => runtimeOwnerTagBlock owner n ++
      runtimeOwnerTagBlocks (owner + 1) ns

/-- The scheduler's owner loop is the recursion over its concrete size vector.
Each iteration is `runOneOwnerTagBlock`, which in turn calls the fixed phase
transition loops; this wrapper does not consult the semantic producer. -/
def runOwnerTagSequence : List Nat → State → State
  | [], s => s
  | n :: ns, s => runOwnerTagSequence ns (runOneOwnerTagBlock n s)

/-- Exact all-owner tag accumulation. The invariant ties every runtime size and
slot-list length to the current owner index; no ordinal equivalence is chosen
by this theorem. The full scan theorem supplies these vector invariants. -/
/-- The runtime tag of a global sigma variable is the owner numeral followed
by the local port/internal tag. -/
def globalVariableTag (I : Input)
    (x : (ActualNumberedOccurrenceProducer.allocation I).GlobalVar) :
    Nat × Nat × Nat × Nat :=
  localVariableTag ((ActualNumberedOccurrenceProducer.allocation I).size x.1)
    x.1.val x.2

/-- Mapping the exact global owner-prefix enumeration to runtime tuples yields
those same local counter blocks in order. This identifies the *entire* typed
variable list with the concrete tag representation, before row lookup. -/
theorem globalVariableTag_injective (I : Input) :
    Function.Injective (globalVariableTag I) := by
  intro x y h
  rcases x with ⟨v, a⟩
  rcases y with ⟨w, b⟩
  cases a with
  | inl ap =>
      cases b with
      | inl bp =>
          simp [globalVariableTag, localVariableTag] at h
          rcases h with ⟨howner, hocc, hport⟩
          have hv : v = w := Fin.ext howner
          subst w
          have hp : ap = bp := by
            apply Prod.ext
            · exact Fin.ext hocc
            · exact Fin.ext hport
          subst bp
          rfl
      | inr bp =>
          simp [globalVariableTag, localVariableTag] at h
  | inr ap =>
      cases b with
      | inl bp =>
          simp [globalVariableTag, localVariableTag] at h
      | inr bp =>
          simp [globalVariableTag, localVariableTag] at h
          rcases h with ⟨howner, hedge, hlabel⟩
          have hv : v = w := Fin.ext howner
          subst w
          have he : ap.1 = bp.1 := idxOf_injective_on_nodup
            (ActualEqualityCloud.edgeList ((ActualNumberedOccurrenceProducer.allocation I).size v))
            (ActualEqualityCloud.edgeList_nodup _)
            (ActualEqualityCloud.mem_edgeList ap.1)
            (ActualEqualityCloud.mem_edgeList bp.1) hedge
          have hp : ap = bp := by
            apply Prod.ext
            · exact he
            · exact Fin.ext hlabel
          subst bp
          rfl
theorem variableList_map_globalVariableTag (I : Input) :
    (ActualNumberedOccurrenceProducer.variableList I).map
      (globalVariableTag I) =
      (List.finRange I.variables).flatMap fun v =>
        runtimeOwnerTagBlock v.val
          ((ActualNumberedOccurrenceProducer.allocation I).size v) := by
  simp [ActualNumberedOccurrenceProducer.variableList, globalVariableTag,
    localVariableList_map_localVariableTag, runtimeOwnerTagBlock,
    ActualNumberedOccurrenceProducer.allocation,
    ActualOccurrenceAllocation.Instance.tag, List.map_flatMap,
    List.flatMap_map, Function.comp_def]
/-- The numeric owner counter advances exactly with the canonical Fin owner
enumeration, even when some owner contributes an empty local list. -/
theorem runtimeOwnerTagBlocks_finRange (owner : Nat) (n : Nat)
    (size : Fin n → Nat) :
    runtimeOwnerTagBlocks owner ((List.finRange n).map size) =
      (List.finRange n).flatMap fun v =>
        runtimeOwnerTagBlock (owner + v.val) (size v) := by
  induction n generalizing owner with
  | zero => rfl
  | succ n ih =>
      simp [List.finRange_succ, runtimeOwnerTagBlocks,
        List.flatMap_map, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem runOwnerTagSequence_tags (input : Input) (q : Nat)
    (sizes : List Nat) (s : State) (baseTags : List (Nat × Nat × Nat × Nat))
    (hparsed : parsedInput s = some input)
    (hownerCursor : s.ownerCursor = q)
    (hownerLists : s.ownerSlotLists.length = input.variables)
    (hownerSizes : s.ownerSizes.length = input.variables)
    (hbound : q + sizes.length ≤ input.variables)
    (hdata : ∀ i (hi : i < sizes.length),
      s.ownerSizes.get ⟨q + i, by omega⟩ = sizes.get ⟨i, hi⟩ ∧
      (s.ownerSlotLists.get ⟨q + i, by omega⟩).length = sizes.get ⟨i, hi⟩)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (htags : s.variableTags = baseTags) (hphase : s.phase = .portTags) :
    (runOwnerTagSequence sizes s).variableTags =
      baseTags ++ runtimeOwnerTagBlocks q sizes := by
  induction sizes generalizing q s baseTags with
  | nil =>
      simp [runOwnerTagSequence, runtimeOwnerTagBlocks]
  | cons n ns ih =>
      have hq : q < input.variables := by omega
      have hdata0 := hdata 0 (by simp)
      have hsizeEq : s.ownerSizes.get ⟨q, by omega⟩ = n := by
        simpa using hdata0.1
      have hocc : (s.ownerSlotLists.get ⟨q, by omega⟩).length = n := by
        simpa using hdata0.2
      have hslot : s.ownerCursor < s.ownerSlotLists.length := by
        rw [hownerCursor]
        exact hq.trans_le (by omega)
      have hsize : s.ownerCursor < s.ownerSizes.length := by
        rw [hownerCursor]
        exact hq.trans_le (by omega)
      have hocc' : (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = n := by
        simpa [hownerCursor] using hocc
      have hsizeEq' : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n := by
        simpa [hownerCursor] using hsizeEq
      let t := runOneOwnerTagBlock n s
      have hblock := runOneOwnerTagBlock_complete input s n baseTags
        hparsed (by simpa [hownerCursor] using hq) hslot hocc' hsize hsizeEq'
        hpc hlc htags hphase
      have hready := runOneOwnerTagBlock_ready input s n hparsed
        (by simpa [hownerCursor] using hq) hslot hocc' hsize hsizeEq'
        hpc hlc hphase
      have hparsedT : parsedInput t = some input := by
        simpa [t] using hready.2.2.2.2.2.2.1
      have hownerT : t.ownerCursor = q + 1 := by
        simpa [t, hownerCursor] using hready.2.1
      have hlistT : t.ownerSlotLists.length = input.variables := by
        calc
          t.ownerSlotLists.length = s.ownerSlotLists.length :=
            congrArg List.length hready.2.2.2.2.1
          _ = input.variables := hownerLists
      have hsizeT : t.ownerSizes.length = input.variables := by
        calc
          t.ownerSizes.length = s.ownerSizes.length :=
            congrArg List.length hready.2.2.2.2.2.1
          _ = input.variables := hownerSizes
      have hpcT : t.portOccurrenceCursor = 0 := by
        simpa [t] using hready.2.2.1
      have hlcT : t.portLabelCursor = 0 := by
        simpa [t] using hready.2.2.2.1
      have htagsT : t.variableTags =
          baseTags ++ runtimeOwnerTagBlock q n := by
        simpa [runtimeOwnerTagBlock, hownerCursor] using hblock.2.2
      have hdataT : ∀ i (hi : i < ns.length),
          t.ownerSizes.get ⟨q + 1 + i, by omega⟩ = ns.get ⟨i, hi⟩ ∧
          (t.ownerSlotLists.get ⟨q + 1 + i, by omega⟩).length = ns.get ⟨i, hi⟩ := by
        intro i hi
        have hnext := hdata (i + 1) (by simp; omega)
        simpa [t, hready.2.2.2.2.2.1, hready.2.2.2.2.1,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get_cons_succ] using hnext
      have htail := ih (q + 1) t (baseTags ++ runtimeOwnerTagBlock q n)
        hparsedT hownerT hlistT hsizeT (by omega) hdataT hpcT hlcT
        htagsT (by simpa [t] using hready.1)
      simpa [runOwnerTagSequence, runtimeOwnerTagBlocks, t,
        List.append_assoc] using htail
/-- When the completed slot scan has supplied the actual owner sizes and each
slot-list length agrees with its size, the concrete all-owner tag machine is
exactly the map of the numbered producer's owner-prefix variable enumeration.
This is the semantic handoff needed by first-match row lookup. -/
theorem runAllOwnerTags_eq_variableList (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = 0)
    (hownerLists : s.ownerSlotLists.length = input.variables)
    (hownerSizesLen : s.ownerSizes.length = input.variables)
    (hownerSizes : s.ownerSizes =
      (List.finRange input.variables).map
        (ActualNumberedOccurrenceProducer.allocation input).size)
    (hslotSizes : ∀ i (hi : i < input.variables),
      (s.ownerSlotLists.get ⟨i, by omega⟩).length =
        s.ownerSizes.get ⟨i, by omega⟩)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (htags : s.variableTags = []) (hphase : s.phase = .portTags) :
    (runOwnerTagSequence s.ownerSizes s).variableTags =
      (ActualNumberedOccurrenceProducer.variableList input).map
        (globalVariableTag input) := by
  have hall := runOwnerTagSequence_tags input 0 s.ownerSizes s [] hparsed
    (by simpa [hcursor]) hownerLists hownerSizesLen (by omega)
    (by
      intro i hi
      exact ⟨rfl, hslotSizes i (by omega)⟩)
    hpc hlc htags hphase
  rw [hownerSizes] at hall
  rw [runtimeOwnerTagBlocks_finRange 0 input.variables
    (ActualNumberedOccurrenceProducer.allocation input).size] at hall
  simpa [runtimeOwnerTagBlock, Nat.zero_add] using
    hall.trans (variableList_map_globalVariableTag input).symm
/-- The owner block commits exactly the source representative edges, with the
full dart identity and source edge order retained for gadget-row output. -/
theorem runOneOwnerTagBlock_representatives (input : Input) (s : State) (n : Nat)
    (hparsed : parsedInput s = some input)
    (howner : s.ownerCursor < input.variables)
    (hlist : s.ownerCursor < s.ownerSlotLists.length)
    (hocc : (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = n)
    (hsize : s.ownerCursor < s.ownerSizes.length)
    (hsizeEq : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (hphase : s.phase = .portTags) :
    (runOneOwnerTagBlock n s).representativeClouds =
      s.representativeClouds ++
        [(ActualEqualityCloud.edgeList n).map fun edge =>
          let r := ActualGraphEdges.reverse edge.val
          (edge.val.1.1.val, edge.val.1.2.val, edge.val.2.val,
            r.1.1.val, r.1.2.val, r.2.val)] := by
  let p := portTagStep (runPortTagForward (n * (cloudDegree + 1)) s)
  have hprefix := runPortTagForward_prefix input s 0
    (n * (cloudDegree + 1)) n (by omega) s.variableTags hparsed howner hlist
    hocc hpc hlc rfl hphase
  rcases hprefix with ⟨hoccEnd, hlabEnd, _, hlistsPort,
    hparsedPort, hownerPort, hphasePort⟩
  have hlistP : p.ownerSlotLists = s.ownerSlotLists := by
    simp [p, runPortTagForward_ownerSlotLists, portTagStep_ownerSlotLists]
  have hphaseP : p.phase = .cloudDarts := by
    simp [p, portTagStep, hparsedPort, hownerPort, hlistP,
      hoccEnd, hlabEnd, hocc]
  have hparsedP : parsedInput p = some input := by
    simpa [p, portTagStep_parsedInput] using hparsedPort
  have hownerP : p.ownerCursor = s.ownerCursor := by
    simp [p, portTagStep, hparsedPort, hownerPort, hoccEnd, hlabEnd, hocc]
  have hsizeP : p.ownerSizes = s.ownerSizes := by
    simp [p, runPortTagForward_ownerSizes, portTagStep_ownerSizes]
  have hsizeP' : p.ownerCursor < p.ownerSizes.length := by
    rw [hownerP, hsizeP]
    exact hsize
  have hnP : p.ownerSizes.get ⟨p.ownerCursor, by omega⟩ = n := by
    rw [hownerP, hsizeP]
    exact hsizeEq
  have hcursorP : p.ownerScanCursor = 0 := by
    simp [p, portTagStep, hparsedPort, hownerPort, hoccEnd, hlabEnd, hocc]
  have haccP : p.cloudRepAcc = [] := by
    simp [p, portTagStep, hparsedPort, hownerPort, hoccEnd, hlabEnd, hocc]
  have hrepP : p.representativeClouds = s.representativeClouds := by
    simp [p, runPortTagForward_representativeClouds,
      portTagStep_representativeClouds]
  have hcloud := runCloudAndInternal_complete_edgeList input p n hparsedP
    (by simpa [hownerP] using howner) hsizeP' hnP hcursorP haccP hphaseP
  simpa [runOneOwnerTagBlock, p, hrepP, List.append_assoc] using hcloud.2

def runtimeOwnerCloudBlock (n : Nat) :
    List (List (Nat × Nat × Nat × Nat × Nat × Nat)) :=
  [(ActualEqualityCloud.edgeList n).map fun edge =>
    let r := ActualGraphEdges.reverse edge.val
    (edge.val.1.1.val, edge.val.1.2.val, edge.val.2.val,
      r.1.1.val, r.1.2.val, r.2.val)]

/-- The completed owner traversal stores one exact typed representative cloud
per owner, in owner-prefix order, including empty clouds. -/
theorem runOwnerTagSequence_representatives (input : Input) (q : Nat)
    (sizes : List Nat) (s : State)
    (hparsed : parsedInput s = some input)
    (hownerCursor : s.ownerCursor = q)
    (hownerLists : s.ownerSlotLists.length = input.variables)
    (hownerSizes : s.ownerSizes.length = input.variables)
    (hbound : q + sizes.length ≤ input.variables)
    (hdata : ∀ i (hi : i < sizes.length),
      s.ownerSizes.get ⟨q + i, by omega⟩ = sizes.get ⟨i, hi⟩ ∧
      (s.ownerSlotLists.get ⟨q + i, by omega⟩).length = sizes.get ⟨i, hi⟩)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (hphase : s.phase = .portTags) :
    (runOwnerTagSequence sizes s).representativeClouds =
      s.representativeClouds ++ sizes.flatMap runtimeOwnerCloudBlock := by
  induction sizes generalizing q s with
  | nil => simp [runOwnerTagSequence]
  | cons n ns ih =>
      have hq : q < input.variables := by omega
      have hdata0 := hdata 0 (by simp)
      have hsizeEq : s.ownerSizes.get ⟨q, by omega⟩ = n := by simpa using hdata0.1
      have hocc : (s.ownerSlotLists.get ⟨q, by omega⟩).length = n := by
        simpa using hdata0.2
      have hslot : s.ownerCursor < s.ownerSlotLists.length := by
        rw [hownerCursor]
        exact hq.trans_le (by omega)
      have hsize : s.ownerCursor < s.ownerSizes.length := by
        rw [hownerCursor]
        exact hq.trans_le (by omega)
      have hocc' : (s.ownerSlotLists.get ⟨s.ownerCursor, by omega⟩).length = n := by
        simpa [hownerCursor] using hocc
      have hsizeEq' : s.ownerSizes.get ⟨s.ownerCursor, by omega⟩ = n := by
        simpa [hownerCursor] using hsizeEq
      let t := runOneOwnerTagBlock n s
      have hready := runOneOwnerTagBlock_ready input s n hparsed
        (by simpa [hownerCursor] using hq) hslot hocc' hsize hsizeEq'
        hpc hlc hphase
      have hblock := runOneOwnerTagBlock_representatives input s n hparsed
        (by simpa [hownerCursor] using hq) hslot hocc' hsize hsizeEq'
        hpc hlc hphase
      have hparsedT : parsedInput t = some input := by
        simpa [t] using hready.2.2.2.2.2.2.1
      have hownerT : t.ownerCursor = q + 1 := by
        simpa [t, hownerCursor] using hready.2.1
      have hlistT : t.ownerSlotLists.length = input.variables := by
        calc
          t.ownerSlotLists.length = s.ownerSlotLists.length :=
            congrArg List.length hready.2.2.2.2.1
          _ = input.variables := hownerLists
      have hsizeT : t.ownerSizes.length = input.variables := by
        calc
          t.ownerSizes.length = s.ownerSizes.length :=
            congrArg List.length hready.2.2.2.2.2.1
          _ = input.variables := hownerSizes
      have hpcT : t.portOccurrenceCursor = 0 := by simpa [t] using hready.2.2.1
      have hlcT : t.portLabelCursor = 0 := by simpa [t] using hready.2.2.2.1
      have hdataT : ∀ i (hi : i < ns.length),
          t.ownerSizes.get ⟨q + 1 + i, by omega⟩ = ns.get ⟨i, hi⟩ ∧
          (t.ownerSlotLists.get ⟨q + 1 + i, by omega⟩).length = ns.get ⟨i, hi⟩ := by
        intro i hi
        have hnext := hdata (i + 1) (by simp; omega)
        simpa [t, hready.2.2.2.2.2.1, hready.2.2.2.2.1,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get_cons_succ] using hnext
      have htail := ih (q + 1) t hparsedT hownerT hlistT hsizeT
        (by omega) hdataT hpcT hlcT (by simpa [t] using hready.1)
      simpa [runOwnerTagSequence, runtimeOwnerCloudBlock, t,
        List.append_assoc] using htail

theorem runAllOwnerTagSequence_representatives (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = 0)
    (hownerLists : s.ownerSlotLists.length = input.variables)
    (hownerSizesLen : s.ownerSizes.length = input.variables)
    (hownerSizes : s.ownerSizes =
      (List.finRange input.variables).map
        (ActualNumberedOccurrenceProducer.allocation input).size)
    (hslotSizes : ∀ i (hi : i < input.variables),
      (s.ownerSlotLists.get ⟨i, by omega⟩).length =
        s.ownerSizes.get ⟨i, by omega⟩)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (hphase : s.phase = .portTags) :
    (runOwnerTagSequence s.ownerSizes s).representativeClouds =
      s.representativeClouds ++
        (List.finRange input.variables).flatMap fun v =>
          runtimeOwnerCloudBlock
            ((ActualNumberedOccurrenceProducer.allocation input).size v) := by
  have hrun := runOwnerTagSequence_representatives input 0 s.ownerSizes s
    hparsed (by simpa [hcursor]) hownerLists hownerSizesLen (by omega)
    (by intro i hi; exact ⟨rfl, hslotSizes i (by omega)⟩)
    hpc hlc hphase
  rw [hownerSizes] at hrun
  simpa using hrun
theorem terminal_states_absorb (s : State)
    (h : s.phase = .tagsComplete ∨ s.phase = .invalid) : step s = s := by
  rcases h with h | h
  · exact step_tagsComplete_absorbing s h
  · exact step_invalid_absorbing s h

/-- List lookup used by the explicit unary row serializer. -/
def getNat? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getNat? xs n

/-- Structural, bounded linear search returning the first exact match index. -/
def firstIndex? {α : Type} [DecidableEq α] (target : α) :
    List α → Option Nat
  | [] => none
  | x :: xs =>
      if x = target then some 0 else (firstIndex? target xs).map Nat.succ

/-- Exact lookup transport across an injective concrete tag map. -/
theorem firstIndex?_map_injective {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (target : α) (xs : List α) :
    firstIndex? (f target) (xs.map f) = firstIndex? target xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x = target
      · subst x
        simp [firstIndex?]
      · have hne : f x ≠ f target := fun he => h (hf he)
        simp [firstIndex?, h, hne, ih]
/-- Every membership hit has a successful bounded first-match search. -/
theorem firstIndex?_some_of_mem {α : Type} [DecidableEq α]
    (target : α) (xs : List α) (hmem : target ∈ xs) :
    ∃ n, firstIndex? target xs = some n := by
  induction xs with
  | nil => simp at hmem
  | cons x xs ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact ⟨0, by simp [firstIndex?]⟩
      · rcases ih htail with ⟨n, hn⟩
        by_cases hxt : x = target
        · exact ⟨0, by simp [firstIndex?, hxt]⟩
        · exact ⟨n + 1, by simp [firstIndex?, hxt, hn]⟩
/-- Every typed producer variable has a successful runtime tag lookup once the
explicit owner loop has produced its exact mapped variable list. This is the
success half used for both original anchors and gadget labels. -/
theorem globalVariableTag_search_success_of_exact_tags
    (I : Input) (tags : List (Nat × Nat × Nat × Nat))
    (hexact : tags =
      (ActualNumberedOccurrenceProducer.variableList I).map
        (globalVariableTag I))
    (x : (ActualNumberedOccurrenceProducer.allocation I).GlobalVar) :
    ∃ n, firstIndex? (globalVariableTag I x) tags = some n := by
  rw [hexact]
  apply firstIndex?_some_of_mem
  exact List.mem_map.mpr ⟨x,
    ActualNumberedOccurrenceProducer.variableList_mem I x, rfl⟩

/-- Structural first search follows the list's own `idxOf` convention. -/
theorem firstIndex?_eq_idxOf {α : Type} [DecidableEq α]
    (target : α) (xs : List α) (hmem : target ∈ xs) :
    firstIndex? target xs = some (xs.idxOf target) := by
  induction xs with
  | nil => simp at hmem
  | cons x xs ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        simp [firstIndex?]
      · by_cases hxt : x = target
        · simp [firstIndex?, hxt]
        · have hidx : (x :: xs).idxOf target = xs.idxOf target + 1 := by
            simpa [List.idxOf_cons_ne xs (Ne.symm hxt)]
          simp [firstIndex?, hxt, ih htail, hidx]

/-- Every successful structural search result names a genuine occurrence.
This is the membership half needed before identifying the returned index with
the inverse of the concrete `variableList` enumeration. -/
theorem firstIndex?_some_mem {α : Type} [DecidableEq α]
    (target : α) (xs : List α) (n : Nat)
    (h : firstIndex? target xs = some n) : target ∈ xs := by
  induction xs with
  | nil => simp [firstIndex?] at h
  | cons x xs ih =>
      by_cases hxt : x = target
      · simp [firstIndex?, hxt] at h
        simp [hxt]
      · cases hx : firstIndex? target xs with
        | none => simp [firstIndex?, hxt, hx] at h
        | some i =>
            have hi : firstIndex? target xs = some i := hx
            exact List.mem_cons_of_mem x (ih hi)

/-- The index returned by the structural search is in range. -/
theorem firstIndex?_some_lt {α : Type} [DecidableEq α]
    (target : α) (xs : List α) (n : Nat)
    (h : firstIndex? target xs = some n) : n < xs.length := by
  induction xs generalizing n with
  | nil => simp [firstIndex?] at h
  | cons x xs ih =>
      by_cases hxt : x = target
      · simp [firstIndex?, hxt] at h
        simp [h]
      · cases hx : firstIndex? target xs with
        | none => simp [firstIndex?, hxt, hx] at h
        | some i =>
            have hn : Nat.succ i = n := by
              simpa [firstIndex?, hxt, hx] using h
            subst n
            have hi : firstIndex? target xs = some i := hx
            exact Nat.succ_lt_succ (ih hi)

/-- The successful index selects exactly the requested list element. -/
theorem firstIndex?_some_get {α : Type} [DecidableEq α]
    (target : α) (xs : List α) (n : Nat)
    (h : firstIndex? target xs = some n) :
    xs.get ⟨n, firstIndex?_some_lt target xs n h⟩ = target := by
  induction xs generalizing n with
  | nil => simp [firstIndex?] at h
  | cons x xs ih =>
      by_cases hxt : x = target
      · have hn : n = 0 := by simpa [firstIndex?, hxt] using h
        subst n
        simp
      · cases hx : firstIndex? target xs with
        | none => simp [firstIndex?, hxt, hx] at h
        | some i =>
            have hn : Nat.succ i = n := by
              simpa [firstIndex?, hxt, hx] using h
            subst n
            have hi : firstIndex? target xs = some i := hx
            simpa using ih hi

/-- On a nodup enumeration, structural first-match lookup is precisely the
inverse list-get equivalence used for the producer's variable numbering. -/
theorem firstIndex?_eq_nodupGetEquiv_symm_val {α : Type} [DecidableEq α]
    (target : α) (xs : List α) (n : Nat) (hnodup : xs.Nodup)
    (h : firstIndex? target xs = some n) :
    n = ((List.Nodup.getEquiv xs hnodup).symm
      ⟨target, firstIndex?_some_mem target xs n h⟩).val := by
  let e := List.Nodup.getEquiv xs hnodup
  let ht : {x // x ∈ xs} := ⟨target, firstIndex?_some_mem target xs n h⟩
  have hp : n < xs.length := firstIndex?_some_lt target xs n h
  have hget : xs.get ⟨n, hp⟩ = target := firstIndex?_some_get target xs n h
  have happly : e ⟨n, hp⟩ = ht := by
    apply Subtype.ext
    simpa [e, ht] using hget
  have hfin : (⟨n, hp⟩ : Fin xs.length) = e.symm ht := by
    apply e.injective
    calc
      e ⟨n, hp⟩ = ht := happly
      _ = e (e.symm ht) := by simp [e]
  simpa [e] using congrArg Fin.val hfin

/-- The producer's ordinal is the actual filtered-list position; this pins
the original anchor's runtime occurrence coordinate to its `idxOf` scan. -/
theorem allocationOrdinal_eq_idxOf (I : Input)
    (slot : ActualOccurrenceAllocation.Slot I.equations.length) :
    let a := ActualNumberedOccurrenceProducer.allocation I
    let v := a.owner slot
    (a.ordinal v ⟨slot, rfl⟩).val = (a.occurrenceList v).idxOf slot := by
  let a := ActualNumberedOccurrenceProducer.allocation I
  let v := a.owner slot
  have hmem : slot ∈ a.occurrenceList v := (a.mem_occurrenceList v slot).2 rfl
  have hsearch := firstIndex?_eq_idxOf slot (a.occurrenceList v) hmem
  have hpos := firstIndex?_eq_nodupGetEquiv_symm_val slot
    (a.occurrenceList v) ((a.occurrenceList v).idxOf slot)
    (a.occurrenceList_nodup v) hsearch
  simpa [a, v, ActualOccurrenceAllocation.Instance.ordinal,
    ActualOccurrenceAllocation.Instance.occurrenceMembership] using hpos.symm

def slotNumber {m : Nat} (slot : ActualOccurrenceAllocation.Slot m) : Nat :=
  3 * slot.1.val + slot.2.val

theorem slotNumber_injective {m : Nat} :
    Function.Injective (slotNumber (m := m)) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    · have ha := a.2.isLt
      have hb := b.2.isLt
      have hr := a.1.isLt
      have hs := b.1.isLt
      simp [slotNumber] at h
      omega
  · apply Fin.ext
    · have ha := a.2.isLt
      have hb := b.2.isLt
      have hr := a.1.isLt
      have hs := b.1.isLt
      simp [slotNumber] at h
      omega

/-- The first matching source-slot number in an owner's exact occurrence list
is its numbered-producer ordinal. This handles repeated source variables by
retaining the row/coordinate slot itself. -/
theorem firstIndex_slotNumber_eq_ordinal (I : Input)
    (slot : ActualOccurrenceAllocation.Slot I.equations.length) :
    let a := ActualNumberedOccurrenceProducer.allocation I
    let v := a.owner slot
    firstIndex? (slotNumber slot)
      ((a.occurrenceList v).map slotNumber) =
      some (a.ordinal v ⟨slot, rfl⟩).val := by
  let a := ActualNumberedOccurrenceProducer.allocation I
  let v := a.owner slot
  have hmem : slot ∈ a.occurrenceList v := (a.mem_occurrenceList v slot).2 rfl
  have hmapmem : slotNumber slot ∈ (a.occurrenceList v).map slotNumber :=
    List.mem_map.mpr ⟨slot, hmem, rfl⟩
  have hsearch := firstIndex?_map_injective slotNumber slotNumber_injective
    slot (a.occurrenceList v)
  rw [hsearch, firstIndex?_eq_idxOf slot (a.occurrenceList v) hmem]
  have hordinal := allocationOrdinal_eq_idxOf I slot
  simpa [a, v] using congrArg (fun n => some n) hordinal.symm

/-- Specialization to the exact owner-prefix variable enumeration of the
numbered producer: first-match search returns `variableIndexEquiv`'s numeral. -/
theorem variableListSearchIndex_eq_variableIndex
    (I : BooleanParityInput.Input)
    (x : (ActualNumberedOccurrenceProducer.allocation I).GlobalVar)
    (n : Nat)
    (h : firstIndex? x (ActualNumberedOccurrenceProducer.variableList I) = some n) :
    n = (ActualNumberedOccurrenceProducer.variableIndexEquiv I x).val := by
  have heq := firstIndex?_eq_nodupGetEquiv_symm_val x
    (ActualNumberedOccurrenceProducer.variableList I) n
    (ActualNumberedOccurrenceProducer.variableList_nodup I) h
  simpa [ActualNumberedOccurrenceProducer.variableIndexEquiv] using heq

/-- Any successful row-serializer search in the completed state is the exact
owner-prefix ordinal selected by `variableIndexEquiv`. The proof transports
first-match lookup through the injective runtime encoding of the actual list. -/
theorem runAllOwnerTags_lookup_index (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = 0)
    (hownerLists : s.ownerSlotLists.length = input.variables)
    (hownerSizesLen : s.ownerSizes.length = input.variables)
    (hownerSizes : s.ownerSizes =
      (List.finRange input.variables).map
        (ActualNumberedOccurrenceProducer.allocation input).size)
    (hslotSizes : ∀ i (hi : i < input.variables),
      (s.ownerSlotLists.get ⟨i, by omega⟩).length =
        s.ownerSizes.get ⟨i, by omega⟩)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (htags : s.variableTags = []) (hphase : s.phase = .portTags)
    (x : (ActualNumberedOccurrenceProducer.allocation input).GlobalVar)
    (n : Nat)
    (hsearch : firstIndex? (globalVariableTag input x)
      (runOwnerTagSequence s.ownerSizes s).variableTags = some n) :
    n = (ActualNumberedOccurrenceProducer.variableIndexEquiv input x).val := by
  have hlist := runAllOwnerTags_eq_variableList input s hparsed hcursor
    hownerLists hownerSizesLen hownerSizes hslotSizes hpc hlc htags hphase
  have htransport := firstIndex?_map_injective (globalVariableTag input)
    (globalVariableTag_injective input) x
    (ActualNumberedOccurrenceProducer.variableList input)
  rw [hlist, variableList_map_globalVariableTag] at hsearch
  rw [htransport] at hsearch
  exact variableListSearchIndex_eq_variableIndex input x n hsearch
/-- Completeness of the generated tag list makes every actual producer
variable available to the structural row lookup. This removes Option failure
as a premise for original and gadget row construction. -/
theorem runAllOwnerTags_search_success (input : Input) (s : State)
    (hparsed : parsedInput s = some input)
    (hcursor : s.ownerCursor = 0)
    (hownerLists : s.ownerSlotLists.length = input.variables)
    (hownerSizesLen : s.ownerSizes.length = input.variables)
    (hownerSizes : s.ownerSizes =
      (List.finRange input.variables).map
        (ActualNumberedOccurrenceProducer.allocation input).size)
    (hslotSizes : ∀ i (hi : i < input.variables),
      (s.ownerSlotLists.get ⟨i, by omega⟩).length =
        s.ownerSizes.get ⟨i, by omega⟩)
    (hpc : s.portOccurrenceCursor = 0) (hlc : s.portLabelCursor = 0)
    (htags : s.variableTags = []) (hphase : s.phase = .portTags)
    (x : (ActualNumberedOccurrenceProducer.allocation input).GlobalVar)
    (hmem : x ∈ ActualNumberedOccurrenceProducer.variableList input) :
    ∃ n, firstIndex? (globalVariableTag input x)
      (runOwnerTagSequence s.ownerSizes s).variableTags = some n := by
  have hlist := runAllOwnerTags_eq_variableList input s hparsed hcursor
    hownerLists hownerSizesLen hownerSizes hslotSizes hpc hlc htags hphase
  have htagmem : globalVariableTag input x ∈
      (ActualNumberedOccurrenceProducer.variableList input).map
        (globalVariableTag input) :=
    List.mem_map.mpr ⟨x, hmem, rfl⟩
  have hsearch := firstIndex?_some_of_mem (globalVariableTag input x)
    ((ActualNumberedOccurrenceProducer.variableList input).map
      (globalVariableTag input)) htagmem
  rcases hsearch with ⟨n, hn⟩
  exact ⟨n, by simpa [hlist] using hn⟩
def originalCoordinateIndex? (s : State) (coordinate : Nat) : Option Nat := do
  let slot ← getNat? s.slotTrace coordinate
  let (_, _, owner) := slot
  let ownerSlots ← getNat? s.ownerSlotLists owner
  let occurrence ← firstIndex? coordinate ownerSlots
  firstIndex? (0, owner, occurrence, 0) s.variableTags

/-- Given the exact scanned source slot and its owner-prefix list, the
original-row anchor lookup always succeeds by the producer's typed variable
completeness. No successful search is assumed by this theorem. -/
theorem originalCoordinateIndex?_search_success
    (I : Input) (s : State)
    (hTags : s.variableTags =
      (ActualNumberedOccurrenceProducer.variableList I).map
        (globalVariableTag I))
    (slot : ActualOccurrenceAllocation.Slot I.equations.length)
    (hslotTrace : getNat? s.slotTrace (slotNumber slot) =
      some (slot.1.val, slot.2.val,
        ((ActualNumberedOccurrenceProducer.allocation I).owner slot).val))
    (hownerSlots : getNat? s.ownerSlotLists
      ((ActualNumberedOccurrenceProducer.allocation I).owner slot).val =
        some (((ActualNumberedOccurrenceProducer.allocation I).occurrenceList
          ((ActualNumberedOccurrenceProducer.allocation I).owner slot)).map slotNumber)) :
    ∃ n, originalCoordinateIndex? s (slotNumber slot) = some n := by
  let a := ActualNumberedOccurrenceProducer.allocation I
  let v := a.owner slot
  have hocc : firstIndex? (slotNumber slot)
      ((a.occurrenceList v).map slotNumber) =
        some (a.ordinal v ⟨slot, rfl⟩).val := by
    simpa [a, v] using firstIndex_slotNumber_eq_ordinal I slot
  have hanchor : globalVariableTag I (a.anchor slot) =
      (0, v.val, (a.ordinal v ⟨slot, rfl⟩).val, 0) := by
    simp [globalVariableTag, localVariableTag, a, v,
      ActualNumberedOccurrenceProducer.allocation,
      ActualOccurrenceAllocation.Instance.anchor]
  rcases globalVariableTag_search_success_of_exact_tags I s.variableTags hTags
      (a.anchor slot) with ⟨n, htag⟩
  have htag' : firstIndex? (0, v.val, (a.ordinal v ⟨slot, rfl⟩).val, 0)
      s.variableTags = some n := by
    rw [← hanchor]
    exact htag
  refine ⟨n, ?_⟩
  simp [originalCoordinateIndex?, hslotTrace, hownerSlots, hocc, htag']

/-- The successful original-coordinate search returns the exact owner-prefix
ordinal of the corresponding actual source anchor. -/
/-- The original row's three source slots use owner-prefix port zero.
Repeated owners remain distinct because each slot has its own row-major index. -/
theorem originalCoordinateIndex?_eq_variableIndex
    (I : Input) (s : State)
    (hTags : s.variableTags =
      (ActualNumberedOccurrenceProducer.variableList I).map
        (globalVariableTag I))
    (slot : ActualOccurrenceAllocation.Slot I.equations.length)
    (hslotTrace : getNat? s.slotTrace (slotNumber slot) =
      some (slot.1.val, slot.2.val,
        ((ActualNumberedOccurrenceProducer.allocation I).owner slot).val))
    (hownerSlots : getNat? s.ownerSlotLists
      ((ActualNumberedOccurrenceProducer.allocation I).owner slot).val =
        some (((ActualNumberedOccurrenceProducer.allocation I).occurrenceList
          ((ActualNumberedOccurrenceProducer.allocation I).owner slot)).map slotNumber)) :
    originalCoordinateIndex? s (slotNumber slot) =
      some ((ActualNumberedOccurrenceProducer.variableIndexEquiv I
        ((ActualNumberedOccurrenceProducer.allocation I).anchor slot)).val) := by
  let a := ActualNumberedOccurrenceProducer.allocation I
  let v := a.owner slot
  have hocc : firstIndex? (slotNumber slot)
      ((a.occurrenceList v).map slotNumber) =
        some (a.ordinal v ⟨slot, rfl⟩).val := by
    simpa [a, v] using firstIndex_slotNumber_eq_ordinal I slot
  have hanchor : globalVariableTag I (a.anchor slot) =
      (0, v.val, (a.ordinal v ⟨slot, rfl⟩).val, 0) := by
    simp [globalVariableTag, localVariableTag, a, v,
      ActualNumberedOccurrenceProducer.allocation,
      ActualOccurrenceAllocation.Instance.anchor]
  rcases globalVariableTag_search_success_of_exact_tags I s.variableTags hTags
      (a.anchor slot) with ⟨n, htag⟩
  have htag' : firstIndex? (0, v.val, (a.ordinal v ⟨slot, rfl⟩).val, 0)
      s.variableTags = some n := by
    rw [← hanchor]
    exact htag
  have hrun : originalCoordinateIndex? s (slotNumber slot) = some n := by
    simp [originalCoordinateIndex?, hslotTrace, hownerSlots, hocc, htag']
  have htyped : firstIndex? (a.anchor slot)
      (ActualNumberedOccurrenceProducer.variableList I) = some n := by
    rw [hTags] at htag
    rw [firstIndex?_map_injective (globalVariableTag I)
      (globalVariableTag_injective I) (a.anchor slot)
      (ActualNumberedOccurrenceProducer.variableList I)] at htag
    exact htag
  have hindex := variableListSearchIndex_eq_variableIndex I (a.anchor slot) n htyped
  simpa [a] using hrun.trans (congrArg some hindex)

/-- Each original row serializer lookup returns the three exact indices of the
actual allocation anchors, including when some or all owners repeat. -/

def originalRowWords? (s : State) (input : Input) (row : Nat) :
    Option (List Nat) := do
  let x₀ ← originalCoordinateIndex? s (3 * row)
  let x₁ ← originalCoordinateIndex? s (3 * row + 1)
  let x₂ ← originalCoordinateIndex? s (3 * row + 2)
  let equation ← getNat? input.equations row
  pure [x₀, x₁, x₂, if equation.rhs then 1 else 0]


/-- The four fixed equality-gadget rows. Every right-hand side is false. -/
def equalityGadgetRowTable : List (List Nat) :=
  [[0, 2, 3], [1, 4, 5], [2, 4, 6], [3, 5, 6]]

theorem originalRowWords?_eq_anchorIndices
    (I : Input) (s : State)
    (hTags : s.variableTags =
      (ActualNumberedOccurrenceProducer.variableList I).map
        (globalVariableTag I))
    (r : Fin I.equations.length)
    (hTrace : ∀ i : Fin 3, getNat? s.slotTrace (3 * r.val + i.val) =
      some (r.val, i.val,
        ((ActualNumberedOccurrenceProducer.allocation I).owner (r, i)).val))
    (hOwnerSlots : ∀ i : Fin 3,
      getNat? s.ownerSlotLists
        ((ActualNumberedOccurrenceProducer.allocation I).owner (r, i)).val =
        some (((ActualNumberedOccurrenceProducer.allocation I).occurrenceList
          ((ActualNumberedOccurrenceProducer.allocation I).owner (r, i))).map slotNumber))
    (equation : Equation (Fin I.variables))
    (hEquation : getNat? I.equations r.val = some equation) :
    originalRowWords? s I r.val = some [
      (ActualNumberedOccurrenceProducer.variableIndexEquiv I
        ((ActualNumberedOccurrenceProducer.allocation I).originalRow r 0)).val,
      (ActualNumberedOccurrenceProducer.variableIndexEquiv I
        ((ActualNumberedOccurrenceProducer.allocation I).originalRow r 1)).val,
      (ActualNumberedOccurrenceProducer.variableIndexEquiv I
        ((ActualNumberedOccurrenceProducer.allocation I).originalRow r 2)).val,
      if equation.rhs then 1 else 0] := by
  let a := ActualNumberedOccurrenceProducer.allocation I
  have h0 := originalCoordinateIndex?_eq_variableIndex I s hTags (r, (0 : Fin 3))
    (by simpa [slotNumber] using hTrace 0) (hOwnerSlots 0)
  have h1 := originalCoordinateIndex?_eq_variableIndex I s hTags (r, (1 : Fin 3))
    (by simpa [slotNumber] using hTrace 1) (hOwnerSlots 1)
  have h2 := originalCoordinateIndex?_eq_variableIndex I s hTags (r, (2 : Fin 3))
    (by simpa [slotNumber] using hTrace 2) (hOwnerSlots 2)
  simpa [originalRowWords?, a, h0, h1, h2, hEquation,
    ActualOccurrenceAllocation.Instance.originalRow,
    ActualOccurrenceAllocation.Instance.anchor]



def gadgetVariableTag (owner edgeOrdinal : Nat)
    (dart : Nat × Nat × Nat × Nat × Nat × Nat) (localVariable : Nat) :
    Nat × Nat × Nat × Nat :=
  let (v, j, _, w, k, _) := dart
  if localVariable = 0 then (0, owner, v, j)
  else if localVariable = 1 then (0, owner, w, k)
  else (1, owner, edgeOrdinal, localVariable - 2)

/-- All seven runtime gadget labels are exactly the concrete edge embedding
used by the source `EqualityGadget`, at the corresponding Fin-7 coordinate. -/
theorem gadgetVariableTag_eq_sourceEmbedding
    (I : Input) (v : Fin I.variables)
    (e : ActualEqualityCloud.Edge
      ((ActualNumberedOccurrenceProducer.allocation I).size v))
    (edgeOrdinal : Nat)
    (hordinal : edgeOrdinal =
      (ActualEqualityCloud.edgeList
        ((ActualNumberedOccurrenceProducer.allocation I).size v)).idxOf e)
    (j : Fin 7) :
    let r := ActualGraphEdges.reverse e.val
    let dart := (e.val.1.1.val, e.val.1.2.val, e.val.2.val,
      r.1.1.val, r.1.2.val, r.2.val)
    gadgetVariableTag v.val edgeOrdinal dart j.val =
      globalVariableTag I ⟨v, ActualEqualityCloud.embedding e j⟩ := by
  fin_cases j <;>
    simp [gadgetVariableTag, globalVariableTag, localVariableTag, hordinal,
      ActualEqualityCloud.embedding, ActualEqualityCloud.embedFn,
      ActualNumberedOccurrenceProducer.allocation]

/-- Each of the seven labels used by an equality gadget is the tag of its
actual typed source variable. Endpoint labels retain the two oriented dart
ports; internal labels retain the source edge ordinal and Fin-5 coordinate. -/
theorem gadgetVariableTag_eq_globalVariableTag
    (I : Input) (v : Fin I.variables)
    (e : ActualEqualityCloud.Edge
      ((ActualNumberedOccurrenceProducer.allocation I).size v))
    (edgeOrdinal : Nat)
    (hordinal : edgeOrdinal =
      (ActualEqualityCloud.edgeList
        ((ActualNumberedOccurrenceProducer.allocation I).size v)).idxOf e)
    (t : Fin 5) :
    let r := ActualGraphEdges.reverse e.val
    let dart := (e.val.1.1.val, e.val.1.2.val, e.val.2.val,
      r.1.1.val, r.1.2.val, r.2.val)
    gadgetVariableTag v.val edgeOrdinal dart (2 + t.val) =
      globalVariableTag I ⟨v, Sum.inr (e, t)⟩ := by
  simp [gadgetVariableTag, globalVariableTag, localVariableTag,
    ActualNumberedOccurrenceProducer.allocation, hordinal]

theorem gadgetVariableTag_sourceEndpoint_eq_globalVariableTag
    (I : Input) (v : Fin I.variables)
    (e : ActualEqualityCloud.Edge
      ((ActualNumberedOccurrenceProducer.allocation I).size v))
    (edgeOrdinal endpoint : Nat)
    (hend : endpoint = 0 ∨ endpoint = 1) :
    let r := ActualGraphEdges.reverse e.val
    let dart := (e.val.1.1.val, e.val.1.2.val, e.val.2.val,
      r.1.1.val, r.1.2.val, r.2.val)
    gadgetVariableTag v.val edgeOrdinal dart endpoint =
      globalVariableTag I ⟨v, Sum.inl
        (if endpoint = 0 then e.val.1.1 else r.1.1,
         if endpoint = 0 then e.val.1.2 else r.1.2)⟩ := by
  rcases hend with h | h
  · subst endpoint
    simp [gadgetVariableTag, globalVariableTag, localVariableTag,
      ActualNumberedOccurrenceProducer.allocation]

/-- With the actual source edge ordinal, every one of the five internal labels
of an emitted equality gadget is guaranteed to be found by the serializer. -/
theorem gadgetInternalTag_search_success_of_exact_tags
    (I : Input) (tags : List (Nat × Nat × Nat × Nat))
    (hexact : tags =
      (ActualNumberedOccurrenceProducer.variableList I).map
        (globalVariableTag I))
    (v : Fin I.variables)
    (e : ActualEqualityCloud.Edge
      ((ActualNumberedOccurrenceProducer.allocation I).size v))
    (edgeOrdinal : Nat)
    (hordinal : edgeOrdinal =
      (ActualEqualityCloud.edgeList
        ((ActualNumberedOccurrenceProducer.allocation I).size v)).idxOf e)
    (t : Fin 5) :
    ∃ n, firstIndex?
      (gadgetVariableTag v.val edgeOrdinal
        (let r := ActualGraphEdges.reverse e.val
         (e.val.1.1.val, e.val.1.2.val, e.val.2.val,
          r.1.1.val, r.1.2.val, r.2.val)) (2 + t.val)) tags = some n := by
  rw [gadgetVariableTag_eq_globalVariableTag I v e edgeOrdinal hordinal t]
  exact globalVariableTag_search_success_of_exact_tags I tags hexact
    ⟨v, Sum.inr (e, t)⟩

theorem gadgetEndpointTag_search_success_of_exact_tags
    (I : Input) (tags : List (Nat × Nat × Nat × Nat))
    (hexact : tags =
      (ActualNumberedOccurrenceProducer.variableList I).map
        (globalVariableTag I))
    (v : Fin I.variables)
    (e : ActualEqualityCloud.Edge
      ((ActualNumberedOccurrenceProducer.allocation I).size v))
    (edgeOrdinal endpoint : Nat)
    (hend : endpoint = 0 ∨ endpoint = 1) :
    ∃ n, firstIndex?
      (gadgetVariableTag v.val edgeOrdinal
        (let r := ActualGraphEdges.reverse e.val
         (e.val.1.1.val, e.val.1.2.val, e.val.2.val,
          r.1.1.val, r.1.2.val, r.2.val)) endpoint) tags = some n := by
  rw [gadgetVariableTag_sourceEndpoint_eq_globalVariableTag
    I v e edgeOrdinal hend]
  rcases hend with h | h
  · subst endpoint
    exact globalVariableTag_search_success_of_exact_tags I tags hexact
      ⟨v, Sum.inl (e.val.1.1, e.val.1.2)⟩
  · subst endpoint
    exact globalVariableTag_search_success_of_exact_tags I tags hexact
      ⟨v, Sum.inl
        ((ActualGraphEdges.reverse e.val).1.1,
         (ActualGraphEdges.reverse e.val).1.2)⟩
  · subst endpoint
    simp [gadgetVariableTag, globalVariableTag, localVariableTag,
      ActualNumberedOccurrenceProducer.allocation]

def gadgetRowWords? (s : State) (owner edgeOrdinal : Nat)
    (dart : Nat × Nat × Nat × Nat × Nat × Nat) (gadgetRow : Nat) :
    Option (List Nat) := do
  let rowVariables ← getNat? equalityGadgetRowTable gadgetRow
  let x₀ ← getNat? rowVariables 0
  let x₁ ← getNat? rowVariables 1
  let x₂ ← getNat? rowVariables 2
  let y₀ ← firstIndex? (gadgetVariableTag owner edgeOrdinal dart x₀) s.variableTags
  let y₁ ← firstIndex? (gadgetVariableTag owner edgeOrdinal dart x₁) s.variableTags
  let y₂ ← firstIndex? (gadgetVariableTag owner edgeOrdinal dart x₂) s.variableTags
  pure [y₀, y₁, y₂, 0]

def gadgetRowsForCloudAux (s : State) (owner : Nat) :
    List (Nat × Nat × Nat × Nat × Nat × Nat) → Nat → Option (List (List Nat))
  | [], _ => some []
  | dart :: rest, edgeOrdinal => do
      let rows ← (List.range 4).mapM (gadgetRowWords? s owner edgeOrdinal dart)
      let remaining ← gadgetRowsForCloudAux s owner rest (edgeOrdinal + 1)
      pure (rows ++ remaining)

def gadgetRowsForCloudsAux (s : State) :
    List (List (Nat × Nat × Nat × Nat × Nat × Nat)) → Nat → Option (List (List Nat))
  | [], _ => some []
  | cloud :: rest, owner => do
      let rows ← gadgetRowsForCloudAux s owner cloud 0
      let remaining ← gadgetRowsForCloudsAux s rest (owner + 1)
      pure (rows ++ remaining)

def sourceRowsWords? (s : State) (input : Input) : Option (List (List Nat)) := do
  let originalRows ← (List.range input.equations.length).mapM
    (originalRowWords? s input)
  let cloudRows ← gadgetRowsForCloudsAux s s.representativeClouds 0
  pure (originalRows ++ cloudRows)

/-- Exact unary serialization of the explicit state. Malformed inputs use the
fixed legal fallback; a missing generated tag fails closed. -/
def serializedOutput? (s : State) : Option (List Bool) :=
  if s.phase = .invalid then
    some (encodeWords [3, 1, 0, 1, 2, 0])
  else if s.phase = .tagsComplete then
    match parsedInput s with
    | none => none
    | some input => do
        let rows ← sourceRowsWords? s input
        pure (encodeWords ([s.variableTags.length, rows.length] ++ rows.flatten))
  else none

theorem serializedOutput_invalid_fallback (s : State)
    (h : s.phase = .invalid) :
    serializedOutput? s = some (encodeWords [3, 1, 0, 1, 2, 0]) := by
  simp [serializedOutput?, h]

inductive OutputPhase where
  | waiting
  | originalRows
  | cloudRows
  | finish
  | invalid
  | done
  deriving DecidableEq, Repr

def outputPhaseCode : OutputPhase → Nat
  | .waiting => 0
  | .originalRows => 1
  | .cloudRows => 2
  | .finish => 3
  | .invalid => 4
  | .done => 5

/-- A fixed seven-field output accumulator. It emits one original or gadget row
per transition, then applies the exact unary wire encoder. -/
structure OutputState where
  phase : OutputPhase
  rowCursor : Nat
  ownerCursor : Nat
  edgeCursor : Nat
  gadgetRowCursor : Nat
  emittedRows : List (List Nat)
  outputBits : List Bool
  deriving Repr

def encodeOutputState (s : OutputState) : List Bool :=
  encodeWord (outputPhaseCode s.phase) ++
    encodeWords [s.rowCursor, s.ownerCursor, s.edgeCursor, s.gadgetRowCursor] ++
    frameNatLists s.emittedRows ++ frameBits s.outputBits

def initialOutputState : OutputState :=
  { phase := .waiting, rowCursor := 0, ownerCursor := 0, edgeCursor := 0,
    gadgetRowCursor := 0, emittedRows := [], outputBits := [] }

/-- One row-emission transition. Original rows precede owner-ordered clouds;
each cloud uses representative-edge order and the fixed four-row table. -/
def outputStep (scan : State) (s : OutputState) : OutputState :=
  match s.phase with
  | .waiting =>
      if scan.phase = .invalid then { s with phase := .invalid }
      else if scan.phase = .tagsComplete then { s with phase := .originalRows }
      else s
  | .originalRows =>
      match parsedInput scan with
      | none => { s with phase := .invalid }
      | some input =>
          if s.rowCursor < input.equations.length then
            match originalRowWords? scan input s.rowCursor with
            | none => { s with phase := .invalid }
            | some row =>
                { s with rowCursor := s.rowCursor + 1,
                  emittedRows := s.emittedRows ++ [row] }
          else
            { s with phase := .cloudRows, ownerCursor := 0,
              edgeCursor := 0, gadgetRowCursor := 0 }
  | .cloudRows =>
      if s.ownerCursor < scan.representativeClouds.length then
        match getNat? scan.representativeClouds s.ownerCursor with
        | none => { s with phase := .invalid }
        | some cloud =>
            if s.edgeCursor < cloud.length then
              match getNat? cloud s.edgeCursor with
              | none => { s with phase := .invalid }
              | some dart =>
                  match gadgetRowWords? scan s.ownerCursor s.edgeCursor dart
                      s.gadgetRowCursor with
                  | none => { s with phase := .invalid }
                  | some row =>
                      if s.gadgetRowCursor + 1 < 4 then
                        { s with gadgetRowCursor := s.gadgetRowCursor + 1,
                          emittedRows := s.emittedRows ++ [row] }
                      else
                        { s with gadgetRowCursor := 0,
                          edgeCursor := s.edgeCursor + 1,
                          emittedRows := s.emittedRows ++ [row] }
            else
              { s with ownerCursor := s.ownerCursor + 1, edgeCursor := 0,
                gadgetRowCursor := 0 }
      else { s with phase := .finish }
  | .finish =>
      { s with phase := .done,
        outputBits := encodeWords
          ([scan.variableTags.length, s.emittedRows.length] ++ s.emittedRows.flatten) }
  | .invalid =>
      { s with phase := .done, outputBits := encodeWords [3, 1, 0, 1, 2, 0] }
  | .done => s

/-- A successful original-row lookup is emitted verbatim by the output
transition, with the row cursor advanced exactly once. -/
theorem outputStep_originalRows_emits (scan : State) (s : OutputState)
    (input : Input) (row : List Nat)
    (hphase : s.phase = .originalRows)
    (hparsed : parsedInput scan = some input)
    (hbound : s.rowCursor < input.equations.length)
    (hrow : originalRowWords? scan input s.rowCursor = some row) :
    outputStep scan s =
      { s with rowCursor := s.rowCursor + 1,
        emittedRows := s.emittedRows ++ [row] } := by
  simp [outputStep, hphase, hparsed, hbound, hrow]

/-- A successful gadget-row lookup is emitted verbatim. The fourth row of a
gadget advances to the next dart; the first three advance only its row cursor. -/
theorem outputStep_cloudRows_emits (scan : State) (s : OutputState)
    (cloud : List (Nat × Nat × Nat × Nat × Nat × Nat))
    (dart : Nat × Nat × Nat × Nat × Nat × Nat) (row : List Nat)
    (hphase : s.phase = .cloudRows)
    (howner : s.ownerCursor < scan.representativeClouds.length)
    (hcloud : getNat? scan.representativeClouds s.ownerCursor = some cloud)
    (hedge : s.edgeCursor < cloud.length)
    (hdart : getNat? cloud s.edgeCursor = some dart)
    (hrowBound : s.gadgetRowCursor < 4)
    (hrow : gadgetRowWords? scan s.ownerCursor s.edgeCursor dart
      s.gadgetRowCursor = some row) :
    outputStep scan s =
      if s.gadgetRowCursor + 1 < 4 then
        { s with gadgetRowCursor := s.gadgetRowCursor + 1,
          emittedRows := s.emittedRows ++ [row] }
      else
        { s with gadgetRowCursor := 0, edgeCursor := s.edgeCursor + 1,
          emittedRows := s.emittedRows ++ [row] } := by
  simp [outputStep, hphase, howner, hcloud, hedge, hdart, hrow]

/-- The finish transition serializes exactly the rows already accumulated,
using the committed `[N,m] ++ rows.flatten` unary schema. -/
theorem outputStep_finish_serializes (scan : State) (s : OutputState)
    (hphase : s.phase = .finish) :
    (outputStep scan s).outputBits =
      encodeWords ([scan.variableTags.length, s.emittedRows.length] ++
        s.emittedRows.flatten) := by
  simp [outputStep, hphase]

def runOutput (steps : Nat) (scan : State) (s : OutputState := initialOutputState) :
    OutputState :=
  match steps with
  | 0 => s
  | k + 1 => runOutput k scan (outputStep scan s)

/-- Explicit two-stage machine composition. The clock bounds are arguments
until the reachable-state and termination bounds are proved. -/
def completeRun (scanSteps outputSteps : Nat) (bits : List Bool) : OutputState :=
  runOutput outputSteps (runSteps scanSteps (initial bits))

def completeOutput (scanSteps outputSteps : Nat) (bits : List Bool) : List Bool :=
  (completeRun scanSteps outputSteps bits).outputBits

/-- Explicit polynomial clock candidates for the two stages. Their sufficiency
is an open invariant obligation; the final source function does not require a
caller to choose its clocks. -/
def candidateScanClock (bits : List Bool) : Nat :=
  100 * (cloudDegree + 1) * (bits.length + 1) ^ 2

def candidateOutputClock (bits : List Bool) : Nat :=
  100 * (cloudDegree + 1) * (bits.length + 1)

def candidateCompleteProducer (bits : List Bool) : List Bool :=
  completeOutput (candidateScanClock bits) (candidateOutputClock bits) bits

theorem outputStep_done_absorbing (scan : State) (s : OutputState)
    (h : s.phase = .done) : outputStep scan s = s := by
  simp [outputStep, h]

theorem outputStep_invalid_uses_fallback (scan : State) (s : OutputState)
    (h : s.phase = .invalid) :
    (outputStep scan s).outputBits = encodeWords [3, 1, 0, 1, 2, 0] := by
  simp [outputStep, h]

/-- Exact valid-input transition count obtained by summing the parser, slot,
owner-filter, port, dart, internal-label, and terminal phase costs. Here `S`
is the number of source slots, `v` the owner count, and `E` the retained dart
count. -/
def scanPhaseBudget (D L S v E : Nat) : Nat :=
  L + (4 * D + 2) * S + 6 * E + v * S + 4 * v + 4

/-- The phase-cost polynomial is dominated by the concrete proposed scan
clock whenever fields are bounded by input length and retained darts by the
full `3DS` dart scan. This is arithmetic only; the phase execution count and
the field bounds must still be connected to reachable machine states. -/
theorem scanPhaseBudget_le_candidate (D L S v E : Nat)
    (hS : S ≤ L) (hv : v ≤ L) (hE : E ≤ 3 * D * S) :
    scanPhaseBudget D L S v E ≤ 100 * (D + 1) * (L + 1) ^ 2 := by
  have hDS : 3 * D * S ≤ 3 * D * L := by
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left D hS)
  have hE' : E ≤ 3 * D * L := le_trans hE hDS
  have hvS : v * S ≤ L * L := Nat.mul_le_mul hv hS
  have hlinear : scanPhaseBudget D L S v E ≤
      L * L + (22 * D + 7) * L + 4 := by
    unfold scanPhaseBudget
    nlinarith
  nlinarith [hlinear, Nat.zero_le (D * L * L), Nat.zero_le (D * L)]

end
end PvNP.RealizableHardness.ActualOccurrenceBoundedRuntime

