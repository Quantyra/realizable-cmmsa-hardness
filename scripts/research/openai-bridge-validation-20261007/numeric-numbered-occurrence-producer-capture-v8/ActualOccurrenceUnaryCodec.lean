import PvNP.RealizableHardness.ActualNumberedOccurrenceProducer
import Mathlib.Tactic

/-! The exact unary parity wire format and an output validator for the
numbered occurrence producer. This file defines semantic parsers and output
roundtrips; it makes no Complexity.FP claim. -/
namespace PvNP.RealizableHardness.ActualOccurrenceUnaryCodec

open ActualNumberedOccurrenceProducer
open BooleanParityInput
open PvNP.RealizableHardness.RandomizedReduction

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Upstream source wire format: n true bits followed by a false delimiter. -/
def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat -> List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool -> Nat -> Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append,
        List.append_assoc, decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

/-- Parse one exact four-word parity equation. Repeated variable names are
allowed here; generated-source injectivity is checked only by the outer parser. -/
def parseEquation (variables : Nat) :
    List Nat -> Option (Equation (Fin variables) × List Nat)
  | first :: second :: third :: rhs :: rest =>
      if hfirst : first < variables then
        if hsecond : second < variables then
          if hthird : third < variables then
            if rhs = 0 then
              some ({ first := ⟨first, hfirst⟩, second := ⟨second, hsecond⟩,
                third := ⟨third, hthird⟩, rhs := false }, rest)
            else if rhs = 1 then
              some ({ first := ⟨first, hfirst⟩, second := ⟨second, hsecond⟩,
                third := ⟨third, hthird⟩, rhs := true }, rest)
            else none
          else none
        else none
      else none
  | _ => none

@[simp] theorem parseEquation_encoded {n : Nat} (e : Equation (Fin n))
    (rest : List Nat) :
    parseEquation n (equationWords e ++ rest) = some (e, rest) := by
  cases e with
  | mk first second third rhs =>
      have hfirst := first.isLt
      have hsecond := second.isLt
      have hthird := third.isLt
      cases rhs <;> simp [equationWords, parseEquation,
        first.isLt, second.isLt, third.isLt]

def parseEquations (variables : Nat) :
    Nat -> List Nat -> Option (List (Equation (Fin variables)) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (equation, words) <- parseEquation variables words
      let (equations, words) <- parseEquations variables count words
      return (equation :: equations, words)

@[simp] theorem parseEquations_encoded {n : Nat}
    (equations : List (Equation (Fin n))) (rest : List Nat) :
    parseEquations n equations.length (equations.flatMap equationWords ++ rest) =
      some (equations, rest) := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp [List.append_assoc, parseEquations, parseEquation_encoded, ih]

def decodeInputWords : List Nat -> Option Input
  | variables :: count :: words => do
      let (equations, trailing) <- parseEquations variables count words
      if trailing = [] then
        if nonempty : 0 < equations.length then
          some { variables := variables, equations := equations,
            nonempty := List.length_pos_iff.mp nonempty }
        else none
      else none
  | _ => none

@[simp] theorem decodeInputWords_encoded (input : Input) :
    decodeInputWords (inputWords input) = some input := by
  cases input with
  | mk variables equations nonempty =>
      have parsed := parseEquations_encoded equations []
      have positive := List.length_pos_iff.mpr nonempty
      simp only [List.append_nil] at parsed
      simp [decodeInputWords, inputWords, parsed, positive]

def decodeInputBits (bits : List Bool) : Option Input :=
  decodeWords bits >>= decodeInputWords

def sharedInputBits (input : Input) : List Bool :=
  encodeWords (inputWords input)

@[simp] theorem decodeInputBits_shared (input : Input) :
    decodeInputBits (sharedInputBits input) = some input := by
  simp [decodeInputBits, sharedInputBits]

/-- Concatenating encoded words agrees with concatenating natural-number lists. -/
theorem encodeWords_append (left right : List Nat) :
    encodeWords (left ++ right) = encodeWords left ++ encodeWords right := by
  induction left with
  | nil => rfl
  | cons n left ih => simp [encodeWords, ih, List.append_assoc]

theorem equationWireLength_le {n : Nat} (e : Equation (Fin n)) :
    (encodeWords (equationWords e)).length ≤ 3 * n + 2 := by
  cases e with
  | mk first second third rhs =>
      have hfirst := first.isLt
      have hsecond := second.isLt
      have hthird := third.isLt
      cases rhs <;>
        simp [equationWords, encodeWords, encodeWord, List.length_append] <;>
        omega

theorem equationRowsWireLength_le {n : Nat}
    (equations : List (Equation (Fin n))) :
    (encodeWords (equations.flatMap equationWords)).length ≤
      equations.length * (3 * n + 2) := by
  induction equations with
  | nil => simp [encodeWords]
  | cons e equations ih =>
      have he := equationWireLength_le e
      rw [List.flatMap_cons, encodeWords_append, List.length_append]
      simp only [List.length_cons]
      omega

theorem inputWireLength_le (input : Input) :
    (encodeWords (BooleanParityInput.inputWords input)).length ≤
      input.variables + input.equations.length + 2 +
        input.equations.length * (3 * input.variables + 2) := by
  change (encodeWords
    ([input.variables, input.equations.length] ++
      input.equations.flatMap equationWords)).length ≤ _
  rw [encodeWords_append]
  have hrows := equationRowsWireLength_le input.equations
  simp only [encodeWords, encodeWord, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- Row data interpreted under the exact ordered wire parser. -/
def inputRow (input : Input) (r : Fin input.equations.length) :
    Fin 3 -> Fin input.variables := fun c =>
  let e := input.equations.get r
  if c.val = 0 then e.first else if c.val = 1 then e.second else e.third

def inputRhs (input : Input) (r : Fin input.equations.length) : ZMod 2 :=
  ActualOccurrenceGapBridge.valueOf (input.equations.get r).rhs

def inputSupport (input : Input) (r : Fin input.equations.length) : Finset (Fin input.variables) :=
  Finset.univ.image (inputRow input r)

def inputRowsInjective (input : Input) : Prop :=
  forall r, Function.Injective (inputRow input r)

def inputDegreeTen (input : Input) : Prop :=
  forall v : Fin input.variables,
    (Finset.univ.filter fun r : Fin input.equations.length =>
      v ∈ inputSupport input r).card <= 10

def inputOverlapOne (input : Input) : Prop :=
  forall r s : Fin input.equations.length, r ≠ s ->
    ((inputSupport input r) ∩ (inputSupport input s)).card <= 1

def decodeEncodedInput (input : Input) : Option ActualMZOuterSourceContract.Encoded3Lin := by
  classical
  exact if hrow : inputRowsInjective input then
    if hdegree : inputDegreeTen input then
      if hoverlap : inputOverlapOne input then
        some {
          vars := input.variables
          rows := input.equations.length
          rows_pos := List.length_pos_iff.mpr input.nonempty
          source := {
            row := inputRow input
            rhs := inputRhs input
            row_injective := hrow
          }
          degree_ten := hdegree
          overlap_one := hoverlap
        }
      else none
    else none
  else none



theorem outputRowsLength (input : Input) :
    (ActualNumberedOccurrenceProducer.output input).equations.length =
      (ActualNumberedOccurrenceProducer.allocation input).rows.length := by
  simp [ActualNumberedOccurrenceProducer.output,
    ActualNumberedOccurrenceProducer.outputEquations]

def outputRowIndexEquiv (input : Input) :
    Fin (ActualNumberedOccurrenceProducer.output input).equations.length ≃
      Fin (ActualNumberedOccurrenceProducer.allocation input).rows.length :=
  finCongr (outputRowsLength input)

theorem output_inputRow_eq (input : Input)
    (r : Fin (ActualNumberedOccurrenceProducer.output input).equations.length)
    (c : Fin 3) :
    inputRow (ActualNumberedOccurrenceProducer.output input) r c =
      (ActualNumberedOccurrenceProducer.encoded3Lin input).source.row
        (outputRowIndexEquiv input r) c := by
  fin_cases c <;>
    simp [inputRow, ActualNumberedOccurrenceProducer.output,
      ActualNumberedOccurrenceProducer.outputEquations,
      ActualNumberedOccurrenceProducer.encodeRow,
      ActualNumberedOccurrenceProducer.encoded3Lin,
      ActualNumberedOccurrenceProducer.finiteSource,
      ActualNumberedOccurrenceProducer.rows_get_eq_rowIndex,
      outputRowIndexEquiv]

theorem output_inputRhs_eq (input : Input)
    (r : Fin (ActualNumberedOccurrenceProducer.output input).equations.length) :
    inputRhs (ActualNumberedOccurrenceProducer.output input) r =
      (ActualNumberedOccurrenceProducer.encoded3Lin input).source.rhs
        (outputRowIndexEquiv input r) := by
  simp [inputRhs, ActualNumberedOccurrenceProducer.output,
    ActualNumberedOccurrenceProducer.outputEquations,
    ActualNumberedOccurrenceProducer.encodeRow,
    ActualNumberedOccurrenceProducer.encoded3Lin,
    ActualNumberedOccurrenceProducer.finiteSource,
    ActualNumberedOccurrenceProducer.rows_get_eq_rowIndex,
    ActualOccurrenceGapBridge.valueOf_bitOf,
    outputRowIndexEquiv]

theorem output_inputSupport_eq (input : Input)
    (r : Fin (ActualNumberedOccurrenceProducer.output input).equations.length) :
    inputSupport (ActualNumberedOccurrenceProducer.output input) r =
      (ActualNumberedOccurrenceProducer.encoded3Lin input).source.support
        (outputRowIndexEquiv input r) := by
  ext x
  simp [inputSupport, PvNP.RealizableHardness.Finite3LinSource.support,
    output_inputRow_eq]

theorem output_inputRowsInjective (input : Input) :
    inputRowsInjective (ActualNumberedOccurrenceProducer.output input) := by
  intro r
  have h := (ActualNumberedOccurrenceProducer.encoded3Lin input).source.row_injective
    (outputRowIndexEquiv input r)
  simpa only [output_inputRow_eq] using h

theorem output_inputDegreeTen (input : Input) :
    inputDegreeTen (ActualNumberedOccurrenceProducer.output input) := by
  intro v
  let e := outputRowIndexEquiv input
  let left := Finset.univ.filter fun r : Fin (ActualNumberedOccurrenceProducer.output input).equations.length =>
    v ∈ inputSupport (ActualNumberedOccurrenceProducer.output input) r
  let right := Finset.univ.filter fun r : Fin (ActualNumberedOccurrenceProducer.allocation input).rows.length =>
    v ∈ (ActualNumberedOccurrenceProducer.encoded3Lin input).source.support r
  have hm : left.map e.toEmbedding = right := by
    ext r
    simp only [left, right, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [output_inputSupport_eq] using hq
    · intro hr
      refine ⟨e.symm r, by simpa [output_inputSupport_eq] using hr, by simp [e]⟩
  have hcard : left.card = right.card := by
    simpa only [Finset.card_map] using congrArg Finset.card hm
  change left.card ≤ 10
  rw [hcard]
  exact (ActualNumberedOccurrenceProducer.encoded3Lin input).degree_ten v

theorem output_inputOverlapOne (input : Input) :
    inputOverlapOne (ActualNumberedOccurrenceProducer.output input) := by
  intro r s hrs
  rw [output_inputSupport_eq, output_inputSupport_eq]
  apply (ActualNumberedOccurrenceProducer.encoded3Lin input).overlap_one
  intro heq
  exact hrs ((outputRowIndexEquiv input).injective heq)
theorem decodeEncodedInput_output (input : Input) :
    decodeEncodedInput (ActualNumberedOccurrenceProducer.output input) =
      some (ActualNumberedOccurrenceProducer.encoded3Lin input) := by
  have hrow := output_inputRowsInjective input
  have hdegree := output_inputDegreeTen input
  have hoverlap := output_inputOverlapOne input
  simp only [decodeEncodedInput, dif_pos hrow, dif_pos hdegree, dif_pos hoverlap]
  congr 1
  cases outputRowsLength input
  ext <;> simp [ActualNumberedOccurrenceProducer.encoded3Lin,
    ActualNumberedOccurrenceProducer.output, ActualNumberedOccurrenceProducer.outputEquations,
    output_inputRow_eq, output_inputRhs_eq]

def decodeOutput (bits : List Bool) :
    Option ActualMZOuterSourceContract.Encoded3Lin :=
  (decodeInputBits bits).bind decodeEncodedInput

def outerEncoding : ActualMZOuterSourceContract.OuterEncoding where
  decode := decodeOutput

def serializeOutput (input : Input) : List Bool :=
  encodeWords (BooleanParityInput.inputWords (ActualNumberedOccurrenceProducer.output input))

theorem serializeOutput_wireLength_le (input : Input) :
    (serializeOutput input).length ≤
      (ActualNumberedOccurrenceProducer.output input).variables +
        (ActualNumberedOccurrenceProducer.output input).equations.length + 2 +
        (ActualNumberedOccurrenceProducer.output input).equations.length *
          (3 * (ActualNumberedOccurrenceProducer.output input).variables + 2) := by
  exact inputWireLength_le (ActualNumberedOccurrenceProducer.output input)

theorem serializeOutput_polynomial_length_bound (input : Input) :
    (serializeOutput input).length ≤
      51 * FixedPortCycleFamily.degree * input.equations.length +
      (1 + 18 * FixedPortCycleFamily.degree) * input.equations.length + 2 +
      ((1 + 18 * FixedPortCycleFamily.degree) * input.equations.length) *
        (3 * (51 * FixedPortCycleFamily.degree * input.equations.length) + 2) := by
  let rows := (ActualNumberedOccurrenceProducer.output input).equations.length
  let vars := (ActualNumberedOccurrenceProducer.output input).variables
  let rowBound := (1 + 18 * FixedPortCycleFamily.degree) * input.equations.length
  let varBound := 51 * FixedPortCycleFamily.degree * input.equations.length
  have hrows : rows ≤ rowBound := by
    exact ActualNumberedOccurrenceProducer.row_count_bound input
  have hvars : vars ≤ varBound := by
    have h := ActualNumberedOccurrenceProducer.variable_count_bound input
    dsimp [vars]
    omega
  have hfactor : 3 * vars + 2 ≤ 3 * varBound + 2 := by omega
  have hproduct : rows * (3 * vars + 2) ≤ rowBound * (3 * varBound + 2) :=
    Nat.mul_le_mul hrows hfactor
  have hwire := serializeOutput_wireLength_le input
  change (serializeOutput input).length ≤ _
  dsimp [rows, vars, rowBound, varBound] at hrows hvars hfactor hproduct
  dsimp [rows, vars, rowBound, varBound]
  nlinarith [hwire, hrows, hvars, hproduct]

theorem decodeOutput_serializeOutput (input : Input) :
    outerEncoding.decode (serializeOutput input) =
      some (ActualNumberedOccurrenceProducer.encoded3Lin input) := by
  simp [outerEncoding, decodeOutput, serializeOutput, decodeEncodedInput_output]
def fallbackInput : Input where
  variables := 3
  equations := [{ first := 0, second := 1, third := 2, rhs := false }]
  nonempty := by simp

def totalProducer (bits : List Bool) : List Bool :=
  match decodeInputBits bits with
  | some input => serializeOutput input
  | none => sharedInputBits fallbackInput
theorem fallbackRowsInjective : inputRowsInjective fallbackInput := by
  intro r
  fin_cases r
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [inputRow, fallbackInput] at h ⊢

theorem fallbackDegreeTen : inputDegreeTen fallbackInput := by
  intro v
  fin_cases v
  norm_num [inputDegreeTen, inputSupport, inputRow, fallbackInput]

theorem fallbackOverlapOne : inputOverlapOne fallbackInput := by
  intro r s hrs
  fin_cases r
  fin_cases s
  contradiction

def fallbackEncoded : ActualMZOuterSourceContract.Encoded3Lin where
  vars := 3
  rows := 1
  rows_pos := by norm_num
  source := {
    row := inputRow fallbackInput
    rhs := inputRhs fallbackInput
    row_injective := fallbackRowsInjective
  }
  degree_ten := fallbackDegreeTen
  overlap_one := fallbackOverlapOne

theorem decodeEncodedInput_fallback :
    decodeEncodedInput fallbackInput = some fallbackEncoded := by
  simp [decodeEncodedInput, fallbackEncoded, fallbackRowsInjective,
    fallbackDegreeTen, fallbackOverlapOne, inputRowsInjective,
    inputDegreeTen, inputOverlapOne]

theorem totalProducer_validInput (input : Input) :
    totalProducer (sharedInputBits input) = serializeOutput input := by
  simp [totalProducer, decodeInputBits_shared]

theorem totalProducer_decodes (bits : List Bool) :
    exists encoded, outerEncoding.decode (totalProducer bits) = some encoded := by
  unfold totalProducer
  cases h : decodeInputBits bits with
  | none =>
      exact ⟨fallbackEncoded, by
        simp [outerEncoding, decodeOutput, decodeEncodedInput_fallback,
          sharedInputBits, h]⟩
  | some input =>
      exact ⟨ActualNumberedOccurrenceProducer.encoded3Lin input, by
        simp [outerEncoding, decodeOutput, decodeEncodedInput_output,
          serializeOutput, h]⟩

theorem totalProducer_roundtrip (input : Input) :
    outerEncoding.decode (totalProducer (sharedInputBits input)) =
      some (ActualNumberedOccurrenceProducer.encoded3Lin input) := by
  rw [totalProducer_validInput]
  exact decodeOutput_serializeOutput input
end
end PvNP.RealizableHardness.ActualOccurrenceUnaryCodec