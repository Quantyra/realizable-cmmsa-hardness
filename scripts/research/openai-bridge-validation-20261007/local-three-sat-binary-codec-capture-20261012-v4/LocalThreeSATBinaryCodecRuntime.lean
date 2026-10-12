import LocalThreeSATBinaryCodec
import LocalThreeSATBinaryCodecSemantics
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Complexitylib.Classes.P.Cobham.Internal.Reverse

/-! Continuation lemmas for the total finite-state scanner. The body lemmas
    account for every successful unary-name scan and preserve the exact
    emitted bit prefix. -/
namespace LocalThreeSATBinaryCodecContinuationOffer

open Complexity.SAT
open LocalThreeSATBinaryCodecOffer

/-- Output contributed by a literal body of unary name length n, including
    its literal separator. -/
def bodyOutput (n : Nat) (tail : List Bool) : List Bool :=
  List.replicate (2 * n) true ++ [false] ++ tail

theorem replicate_double_succ (n : Nat) :
    List.replicate (2 * (n + 1)) true = [true, true] ++ List.replicate (2 * n) true := by
  have h : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [h]
  simp [List.replicate_succ]

theorem run_body0_tail (n : Nat) (tail : List Bool) :
    run .body0 (List.replicate (2 * n) true ++ [false, true] ++ tail) =
      (run .between1 tail).map (bodyOutput n) := by
  induction n with
  | zero => simp [run, pairStep, bodyOutput]
  | succ n ih =>
      rw [replicate_double_succ]
      simp only [List.append_assoc]
      simp [run, pairStep, ih, bodyOutput, Function.comp_def]

theorem run_body1_tail (n : Nat) (tail : List Bool) :
    run .body1 (List.replicate (2 * n) true ++ [false, true] ++ tail) =
      (run .between2 tail).map (bodyOutput n) := by
  induction n with
  | zero => simp [run, pairStep, bodyOutput]
  | succ n ih =>
      rw [replicate_double_succ]
      simp only [List.append_assoc]
      simp [run, pairStep, ih, bodyOutput, Function.comp_def]

theorem run_body2_tail (n : Nat) (tail : List Bool) :
    run .body2 (List.replicate (2 * n) true ++ [false, true] ++ tail) =
      (run .awaitClause tail).map (bodyOutput n) := by
  induction n with
  | zero => simp [run, pairStep, bodyOutput]
  | succ n ih =>
      rw [replicate_double_succ]
      simp only [List.append_assoc]
      simp [run, pairStep, ih, bodyOutput, Function.comp_def]

/-- A first literal emits its clause marker, sign, unary sparse-name digits,
    and literal terminator. -/
theorem run_first_literal_tail (sign : Bool) (n : Nat) (tail : List Bool) :
    run .between0
      ([sign, sign] ++ List.replicate (2 * n) true ++ [false, true] ++ tail) =
      (run .between1 tail).map
        (fun suffix => [true, sign] ++ List.replicate (2 * n) true ++ [false] ++ suffix) := by
  cases sign <;> simp [run, pairStep, run_body0_tail, bodyOutput, List.append_assoc]

/-- Later literals omit the one-per-clause marker. -/
theorem run_later_literal1_tail (sign : Bool) (n : Nat) (tail : List Bool) :
    run .between1
      ([sign, sign] ++ List.replicate (2 * n) true ++ [false, true] ++ tail) =
      (run .between2 tail).map
        (fun suffix => [sign] ++ List.replicate (2 * n) true ++ [false] ++ suffix) := by
  cases sign <;> simp [run, pairStep, run_body1_tail, bodyOutput, List.append_assoc]

theorem run_later_literal2_tail (sign : Bool) (n : Nat) (tail : List Bool) :
    run .between2
      ([sign, sign] ++ List.replicate (2 * n) true ++ [false, true] ++ tail) =
      (run .awaitClause tail).map
        (fun suffix => [sign] ++ List.replicate (2 * n) true ++ [false] ++ suffix) := by
  cases sign <;> simp [run, pairStep, run_body2_tail, bodyOutput, List.append_assoc]

/-- The doubled raw literal and its 01 separator. -/
def encodedLiteralChunk (l : Lit) : List Bool :=
  [l.sign, l.sign] ++ List.replicate (2 * l.var) true ++ [false, true]

theorem run_await_clause_tail (tail : List Bool) :
    run .awaitClause ([true, false] ++ tail) = run .between0 tail := by
  simp [run, pairStep]

/-- A complete three-literal clause followed by its 10 clause separator
    returns to the formula-boundary state and emits exactly `emitClause`. -/
theorem run_three_clause_tail (a b c : Lit) (tail : List Bool) :
    run .between0
      (encodedLiteralChunk a ++ encodedLiteralChunk b ++ encodedLiteralChunk c ++
        [true, false] ++ tail) =
      (run .between0 tail).map
        (fun suffix => emitClause [a, b, c] ++ suffix) := by
  unfold encodedLiteralChunk
  rw [run_first_literal_tail, run_later_literal1_tail,
    run_later_literal2_tail, run_await_clause_tail]
  simp [emitClause, emitLaterLit, bodyOutput, List.append_assoc,
    Option.map_map, Function.comp_def]
theorem run_clause_encode_tail (c : Clause) (hc : c.length = 3)
    (tail : List Bool) :
    run .between0 (c.encode ++ [true, false] ++ tail) =
      (run .between0 tail).map (fun suffix => emitClause c ++ suffix) := by
  cases c with
  | nil => simp at hc
  | cons a rest =>
    cases rest with
    | nil => simp at hc
    | cons b rest =>
      cases rest with
      | nil => simp at hc
      | cons c rest =>
        have hnil : rest = [] := by simp at hc; omega
        subst rest
        have hword :
            Clause.encode [a, b, c] ++ [true, false] ++ tail =
              encodedLiteralChunk a ++ encodedLiteralChunk b ++
                encodedLiteralChunk c ++ [true, false] ++ tail := by
          rw [Clause.encode_cons' a [b, c], Clause.encode_cons' b [c],
            Clause.encode_cons' c []]
          simp [encodedLiteralChunk, List.append_assoc]
        rw [hword]
        exact run_three_clause_tail a b c tail

theorem run_formula_encode (phi : CNF) (h3 : phi.Is3CNF) :
    run .between0 phi.encode = some (emitFormula phi) := by
  induction phi with
  | nil => rfl
  | cons c cs ih =>
    have hshape := (CNF.is3CNF_cons).mp h3
    rw [CNF.encode_cons]
    rw [run_clause_encode_tail c hshape.1 cs.encode]
    rw [ih hshape.2]
    simp [emitFormula, List.append_assoc]
theorem convert_eq_decodedOutput_of_decode (w : List Bool) (phi : CNF)
    (hdecode : CNF.decode3? w = some phi) :
    convert w = LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput w := by
  obtain ⟨hw, h3⟩ := CNF.decode3?_sound hdecode
  subst w
  simp [LocalThreeSATBinaryCodecOffer.convert, run_formula_encode phi h3,
    LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput, hdecode]
/-- Inversion for successful scans in the first literal body. Every successful
    body is a run of doubled unary-name bits, followed by 01 and a successful
    continuation from `between1`. -/
theorem run_body0_success (w : List Bool) (out : List Bool)
    (h : run .body0 w = some out) :
    ∃ n tail suffix,
      w = List.replicate (2 * n) true ++ [false, true] ++ tail ∧
      out = bodyOutput n suffix ∧ run .between1 tail = some suffix := by
  induction w using List.strong_induction_on generalizing out with
  | h w ih =>
    cases w with
    | nil => simp [run] at h
    | cons a xs =>
      cases xs with
      | nil => simp [run] at h
      | cons b rest =>
        cases a with
        | false =>
          cases b with
          | false => simp [run, pairStep] at h
          | true =>
            cases hnext : run .between1 rest with
            | none => simp [run, pairStep, hnext] at h
            | some suffix =>
              simp [run, pairStep, hnext] at h
              refine ⟨0, rest, suffix, ?_, ?_, hnext⟩
              · simp [bodyOutput, List.append_assoc]
              · simp [bodyOutput, List.append_assoc] at h
                exact h.symm
        | true =>
          cases b with
          | false => simp [run, pairStep] at h
          | true =>
            cases hnext : run .body0 rest with
            | none => simp [run, pairStep, hnext] at h
            | some suffix =>
              simp [run, pairStep, hnext] at h
              have hsmall : rest.length < (true :: true :: rest).length := by simp
              obtain ⟨n, tail, suffix', hw, hout, hstate⟩ :=
                ih rest hsmall suffix hnext
              refine ⟨n + 1, tail, suffix', ?_, ?_, hstate⟩
              · simpa [replicate_double_succ, List.append_assoc] using
                  congrArg (fun z => true :: true :: z) hw
              · simp [bodyOutput, replicate_double_succ, List.append_assoc,
                  hout, h]

/-- Inversion for successful scans in the first literal body. Every successful
    body is a run of doubled unary-name bits, followed by 01 and a successful
    continuation from `between1`. -/
theorem run_body1_success (w : List Bool) (out : List Bool)
    (h : run .body1 w = some out) :
    ∃ n tail suffix,
      w = List.replicate (2 * n) true ++ [false, true] ++ tail ∧
      out = bodyOutput n suffix ∧ run .between2 tail = some suffix := by
  induction w using List.strong_induction_on generalizing out with
  | h w ih =>
    cases w with
    | nil => simp [run] at h
    | cons a xs =>
      cases xs with
      | nil => simp [run] at h
      | cons b rest =>
        cases a with
        | false =>
          cases b with
          | false => simp [run, pairStep] at h
          | true =>
            cases hnext : run .between2 rest with
            | none => simp [run, pairStep, hnext] at h
            | some suffix =>
              simp [run, pairStep, hnext] at h
              refine ⟨0, rest, suffix, ?_, ?_, hnext⟩
              · simp [bodyOutput, List.append_assoc]
              · simp [bodyOutput, List.append_assoc] at h
                exact h.symm
        | true =>
          cases b with
          | false => simp [run, pairStep] at h
          | true =>
            cases hnext : run .body1 rest with
            | none => simp [run, pairStep, hnext] at h
            | some suffix =>
              simp [run, pairStep, hnext] at h
              have hsmall : rest.length < (true :: true :: rest).length := by simp
              obtain ⟨n, tail, suffix', hw, hout, hstate⟩ :=
                ih rest hsmall suffix hnext
              refine ⟨n + 1, tail, suffix', ?_, ?_, hstate⟩
              · simpa [replicate_double_succ, List.append_assoc] using
                  congrArg (fun z => true :: true :: z) hw
              · simp [bodyOutput, replicate_double_succ, List.append_assoc,
                  hout, h]

/-- Inversion for successful scans in the first literal body. Every successful
    body is a run of doubled unary-name bits, followed by 01 and a successful
    continuation from `between1`. -/
theorem run_body2_success (w : List Bool) (out : List Bool)
    (h : run .body2 w = some out) :
    ∃ n tail suffix,
      w = List.replicate (2 * n) true ++ [false, true] ++ tail ∧
      out = bodyOutput n suffix ∧ run .awaitClause tail = some suffix := by
  induction w using List.strong_induction_on generalizing out with
  | h w ih =>
    cases w with
    | nil => simp [run] at h
    | cons a xs =>
      cases xs with
      | nil => simp [run] at h
      | cons b rest =>
        cases a with
        | false =>
          cases b with
          | false => simp [run, pairStep] at h
          | true =>
            cases hnext : run .awaitClause rest with
            | none => simp [run, pairStep, hnext] at h
            | some suffix =>
              simp [run, pairStep, hnext] at h
              refine ⟨0, rest, suffix, ?_, ?_, hnext⟩
              · simp [bodyOutput, List.append_assoc]
              · simp [bodyOutput, List.append_assoc] at h
                exact h.symm
        | true =>
          cases b with
          | false => simp [run, pairStep] at h
          | true =>
            cases hnext : run .body2 rest with
            | none => simp [run, pairStep, hnext] at h
            | some suffix =>
              simp [run, pairStep, hnext] at h
              have hsmall : rest.length < (true :: true :: rest).length := by simp
              obtain ⟨n, tail, suffix', hw, hout, hstate⟩ :=
                ih rest hsmall suffix hnext
              refine ⟨n + 1, tail, suffix', ?_, ?_, hstate⟩
              · simpa [replicate_double_succ, List.append_assoc] using
                  congrArg (fun z => true :: true :: z) hw
              · simp [bodyOutput, replicate_double_succ, List.append_assoc,
                  hout, h]
/-- A successful between0 scan begins with one literal and continues from
    between1. -/
theorem run_between0_literal_success (w out : List Bool)
    (h : run .between0 w = some out) (hne : w ≠ []) :
    ∃ l tail suffix,
      w = encodedLiteralChunk l ++ tail ∧
      out = (true :: emitLaterLit l) ++ suffix ∧
      run .between1 tail = some suffix := by
  cases w with
  | nil => simp at hne
  | cons a xs =>
    cases xs with
    | nil => simp at hne
    | cons b rest =>
      cases a with
      | false =>
        cases b with
        | false =>
          cases hbody : run .body0 rest with
          | none => simp [run, pairStep, hbody] at h
          | some bout =>
            simp [run, pairStep, hbody] at h
            obtain ⟨n, tail, suffix, hw, ho, hs⟩ :=
              run_body0_success rest bout hbody
            refine ⟨⟨false, n⟩, tail, suffix, ?_, ?_, hs⟩
            · simp [encodedLiteralChunk, hw, List.append_assoc]
            · simp [emitLaterLit, bodyOutput, List.append_assoc, ho, h]
        | true => simp [run, pairStep] at h
      | true =>
        cases b with
        | false => simp [run, pairStep] at h
        | true =>
          cases hbody : run .body0 rest with
          | none => simp [run, pairStep, hbody] at h
          | some bout =>
            simp [run, pairStep, hbody] at h
            obtain ⟨n, tail, suffix, hw, ho, hs⟩ :=
              run_body0_success rest bout hbody
            refine ⟨⟨true, n⟩, tail, suffix, ?_, ?_, hs⟩
            · simp [encodedLiteralChunk, hw, List.append_assoc]
            · simp [emitLaterLit, bodyOutput, List.append_assoc, ho, h]

/-- A successful between1 scan begins with one literal and continues from
    between2. -/
theorem run_between1_literal_success (w out : List Bool)
    (h : run .between1 w = some out) :
    ∃ l tail suffix,
      w = encodedLiteralChunk l ++ tail ∧
      out = emitLaterLit l ++ suffix ∧
      run .between2 tail = some suffix := by
  cases w with
  | nil => simp [run] at h
  | cons a xs =>
    cases xs with
    | nil => simp [run] at h
    | cons b rest =>
      cases a with
      | false =>
        cases b with
        | false =>
          cases hbody : run .body1 rest with
          | none => simp [run, pairStep, hbody] at h
          | some bout =>
            simp [run, pairStep, hbody] at h
            obtain ⟨n, tail, suffix, hw, ho, hs⟩ :=
              run_body1_success rest bout hbody
            refine ⟨⟨false, n⟩, tail, suffix, ?_, ?_, hs⟩
            · simp [encodedLiteralChunk, hw, List.append_assoc]
            · simp [emitLaterLit, bodyOutput, List.append_assoc, ho, h]
        | true => simp [run, pairStep] at h
      | true =>
        cases b with
        | false => simp [run, pairStep] at h
        | true =>
          cases hbody : run .body1 rest with
          | none => simp [run, pairStep, hbody] at h
          | some bout =>
            simp [run, pairStep, hbody] at h
            obtain ⟨n, tail, suffix, hw, ho, hs⟩ :=
              run_body1_success rest bout hbody
            refine ⟨⟨true, n⟩, tail, suffix, ?_, ?_, hs⟩
            · simp [encodedLiteralChunk, hw, List.append_assoc]
            · simp [emitLaterLit, bodyOutput, List.append_assoc, ho, h]

/-- A successful between2 scan begins with one literal and continues from
    awaitClause. -/
theorem run_between2_literal_success (w out : List Bool)
    (h : run .between2 w = some out) :
    ∃ l tail suffix,
      w = encodedLiteralChunk l ++ tail ∧
      out = emitLaterLit l ++ suffix ∧
      run .awaitClause tail = some suffix := by
  cases w with
  | nil => simp [run] at h
  | cons a xs =>
    cases xs with
    | nil => simp [run] at h
    | cons b rest =>
      cases a with
      | false =>
        cases b with
        | false =>
          cases hbody : run .body2 rest with
          | none => simp [run, pairStep, hbody] at h
          | some bout =>
            simp [run, pairStep, hbody] at h
            obtain ⟨n, tail, suffix, hw, ho, hs⟩ :=
              run_body2_success rest bout hbody
            refine ⟨⟨false, n⟩, tail, suffix, ?_, ?_, hs⟩
            · simp [encodedLiteralChunk, hw, List.append_assoc]
            · simp [emitLaterLit, bodyOutput, List.append_assoc, ho, h]
        | true => simp [run, pairStep] at h
      | true =>
        cases b with
        | false => simp [run, pairStep] at h
        | true =>
          cases hbody : run .body2 rest with
          | none => simp [run, pairStep, hbody] at h
          | some bout =>
            simp [run, pairStep, hbody] at h
            obtain ⟨n, tail, suffix, hw, ho, hs⟩ :=
              run_body2_success rest bout hbody
            refine ⟨⟨true, n⟩, tail, suffix, ?_, ?_, hs⟩
            · simp [encodedLiteralChunk, hw, List.append_assoc]
            · simp [emitLaterLit, bodyOutput, List.append_assoc, ho, h]
/-- The only successful await-clause token is 10; it emits nothing and
    restarts the formula scanner. -/
theorem run_await_success (w out : List Bool)
    (h : run .awaitClause w = some out) :
    ∃ tail, w = [true, false] ++ tail ∧ run .between0 tail = some out := by
  cases w with
  | nil => simp [run] at h
  | cons a xs =>
    cases xs with
    | nil => simp [run] at h
    | cons b rest =>
      cases a with
      | false => cases b <;> simp [run, pairStep] at h
      | true =>
        cases b with
        | false =>
          simp [run, pairStep] at h
          exact ⟨rest, rfl, h⟩
        | true => simp [run, pairStep] at h

/-- Every successful formula-boundary run consists of one exact-three clause
    and a shorter successful formula-boundary suffix. -/
theorem run_clause_success (w out : List Bool)
    (h : run .between0 w = some out) (hne : w ≠ []) :
    ∃ a b c tail suffix,
      w = encodedLiteralChunk a ++ encodedLiteralChunk b ++
        encodedLiteralChunk c ++ [true, false] ++ tail ∧
      run .between0 tail = some suffix := by
  obtain ⟨a, t1, s1, hw1, _, h1⟩ := run_between0_literal_success w out h hne
  obtain ⟨b, t2, s2, hw2, _, h2⟩ := run_between1_literal_success t1 s1 h1
  obtain ⟨c, t3, s3, hw3, _, h3⟩ := run_between2_literal_success t2 s2 h2
  obtain ⟨tail, hw4, h4⟩ := run_await_success t3 s3 h3
  refine ⟨a, b, c, tail, s3, ?_, h4⟩
  rw [hw1, hw2, hw3, hw4]
  simp [List.append_assoc]

/-- Scanner success reconstructs a concrete exact-three CNF encoding. This is
    the malformed-input rejection bridge to the authoritative decoder. -/
theorem run_between0_sound (w : List Bool) (out : List Bool)
    (h : run .between0 w = some out) :
    ∃ phi : CNF, w = phi.encode ∧ phi.Is3CNF := by
  induction w using List.strong_induction_on generalizing out with
  | h w ih =>
    cases w with
    | nil =>
      simp [run] at h
      refine ⟨[], ?_, CNF.is3CNF_nil⟩
      rfl
    | cons a xs =>
      obtain ⟨l1, l2, l3, tail, suffix, hw, htail⟩ := run_clause_success (a :: xs) out h (by simp)
      have hsmall : tail.length < (a :: xs).length := by
        rw [hw]
        simp
        omega
      obtain ⟨phi, hphi, h3⟩ := ih tail hsmall suffix htail
      refine ⟨[l1, l2, l3] :: phi, ?_, ?_⟩
      · rw [CNF.encode_cons]
        rw [show Clause.encode [l1, l2, l3] =
          encodedLiteralChunk l1 ++ encodedLiteralChunk l2 ++
            encodedLiteralChunk l3 by
            rw [Clause.encode_cons' l1 [l2, l3], Clause.encode_cons' l2 [l3],
              Clause.encode_cons' l3 []]
            simp [encodedLiteralChunk, List.append_assoc]]
        calc
          a :: xs = encodedLiteralChunk l1 ++ encodedLiteralChunk l2 ++
              encodedLiteralChunk l3 ++ [true, false] ++ tail := hw
          _ = encodedLiteralChunk l1 ++ encodedLiteralChunk l2 ++
              encodedLiteralChunk l3 ++ [true, false] ++ phi.encode := by
            exact congrArg
              (fun z => encodedLiteralChunk l1 ++ encodedLiteralChunk l2 ++
                encodedLiteralChunk l3 ++ [true, false] ++ z) hphi
      · exact (CNF.is3CNF_cons).mpr ⟨by simp, h3⟩
theorem run_none_of_decode3_none (w : List Bool)
    (hdecode : CNF.decode3? w = none) : run .between0 w = none := by
  cases hrun : run .between0 w with
  | none => rfl
  | some out =>
    obtain ⟨phi, hw, h3⟩ := run_between0_sound w out hrun
    rw [hw, CNF.decode3?_encode h3] at hdecode
    cases hdecode

theorem scannerMatchesDecoder : ∀ w : List Bool,
    convert w = LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput w := by
  intro w
  cases hdecode : CNF.decode3? w with
  | none =>
    have hrun := run_none_of_decode3_none w hdecode
    simp [convert, hrun, LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput,
      hdecode]
  | some phi =>
    exact convert_eq_decodedOutput_of_decode w phi hdecode

theorem localThreeSAT_iff_decodedConverter (w : List Bool) :
    w ∈ ThreeSAT.language ↔
      ∃ phi, CNF.decode3? w = some phi ∧
        convert w = emitFormula phi ∧ phi.Satisfiable := by
  rw [LocalThreeSATBinaryCodecSemanticsOffer.threeSAT_iff_decodedOutput]
  constructor
  · rintro ⟨phi, hdecode, hout, hsat⟩
    exact ⟨phi, hdecode, by rw [scannerMatchesDecoder, hout], hsat⟩
  · rintro ⟨phi, hdecode, hout, hsat⟩
    exact ⟨phi, hdecode, by rw [← scannerMatchesDecoder, hout], hsat⟩


/-! Concrete boundedRec implementation of the scanner. The accumulator is a
    fixed five-bit control code followed by the emitted payload. -/
private def sevenStates : List State :=
  [.between0, .between1, .between2, .body0, .body1, .body2, .awaitClause]

instance : Fintype State where
  elems := sevenStates.toFinset
  complete := by intro q; cases q <;> simp [sevenStates]

inductive MicroState where
  | ready (q : State)
  | half (q : State) (first : Bool)
  | invalid
  deriving DecidableEq, Fintype, Repr

/-- Seven ready states and their seven first-bit variants in each polarity,
    followed by one absorbing invalid state. -/
def microStates : List MicroState :=
  [.ready .between0, .ready .between1, .ready .between2,
   .ready .body0, .ready .body1, .ready .body2, .ready .awaitClause,
   .half .between0 false, .half .between1 false, .half .between2 false,
   .half .body0 false, .half .body1 false, .half .body2 false,
   .half .awaitClause false,
   .half .between0 true, .half .between1 true, .half .between2 true,
   .half .body0 true, .half .body1 true, .half .body2 true,
   .half .awaitClause true, .invalid]

def microCode (s : MicroState) : List Bool :=
  match s with
  | .ready .between0 => [false, false, false, false, false]
  | .ready .between1 => [false, false, false, false, true]
  | .ready .between2 => [false, false, false, true, false]
  | .ready .body0 => [false, false, false, true, true]
  | .ready .body1 => [false, false, true, false, false]
  | .ready .body2 => [false, false, true, false, true]
  | .ready .awaitClause => [false, false, true, true, false]
  | .half .between0 false => [false, true, false, false, false]
  | .half .between1 false => [false, true, false, false, true]
  | .half .between2 false => [false, true, false, true, false]
  | .half .body0 false => [false, true, false, true, true]
  | .half .body1 false => [false, true, true, false, false]
  | .half .body2 false => [false, true, true, false, true]
  | .half .awaitClause false => [false, true, true, true, false]
  | .half .between0 true => [true, false, false, false, false]
  | .half .between1 true => [true, false, false, false, true]
  | .half .between2 true => [true, false, false, true, false]
  | .half .body0 true => [true, false, false, true, true]
  | .half .body1 true => [true, false, true, false, false]
  | .half .body2 true => [true, false, true, false, true]
  | .half .awaitClause true => [true, false, true, true, false]
  | .invalid => [true, true, true, true, true]

theorem microCode_length (s : MicroState) : (microCode s).length = 5 := by
  cases s with
  | ready q => cases q <;> rfl
  | half q b => cases q <;> cases b <;> rfl
  | invalid => rfl

/-- The total one-bit transition. Invalid encodings remain invalid. -/
def microStep (s : MicroState) (bit : Bool) : MicroState × List Bool :=
  match s with
  | .ready q => (.half q bit, [])
  | .half q first =>
      match pairStep q first bit with
      | none => (.invalid, [])
      | some (q', emitted) => (.ready q', emitted)
  | .invalid => (.invalid, [])

/-- One algebra branch: update the fixed control prefix, retain the payload,
    and append at most two emitted bits. -/
def transitionBranch (bit : Bool) (s : MicroState)
    (v : Fin 1 → List Bool) : List Bool :=
  let t := microStep s bit
  microCode t.1 ++ (v 0).drop 5 ++ t.2

def invalidCode : List Bool := microCode .invalid
theorem microCode_injective : Function.Injective microCode := by
  intro s t h
  have hinj : ∀ a b : MicroState, microCode a = microCode b → a = b := by decide
  exact hinj s t h

theorem microState_mem (s : MicroState) : s ∈ microStates := by
  cases s with
  | ready q => cases q <;> simp [microStates]
  | half q bit => cases q <;> cases bit <;> simp [microStates]
  | invalid => simp [microStates]

def transitionTable (bit : Bool) :
    List (List Bool × ((Fin 1 → List Bool) → List Bool)) :=
  microStates.map (fun s => (microCode s, transitionBranch bit s))

def transitionFn (bit : Bool) (v : Fin 1 → List Bool) : List Bool :=
  (transitionTable bit).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0))
      (p.2 v) acc) invalidCode

/-- Dropping five bits and appending fixed words has a direct certificate. -/
theorem dropFiveFn_mem :
    Complexity.Cobham (fun v : Fin 1 → List Bool => (v 0).drop 5) := by
  exact Complexity.Cobham.dropFn
    (Complexity.Cobham.const (List.replicate 5 false))
    (Complexity.Cobham.proj (0 : Fin 1))

theorem transitionBranch_mem (bit : Bool) (s : MicroState) :
    Complexity.Cobham (transitionBranch bit s) := by
  unfold transitionBranch
  exact Complexity.Cobham.appendFn
    (Complexity.Cobham.const (microCode (microStep s bit).1))
    (Complexity.Cobham.appendFn dropFiveFn_mem
      (Complexity.Cobham.const (microStep s bit).2))

theorem transitionFn_value (bit : Bool) (s : MicroState) (payload : List Bool) :
    transitionFn bit (fun _ => microCode s ++ payload) =
      microCode (microStep s bit).1 ++ payload ++ (microStep s bit).2 := by
  let acc := microCode s ++ payload
  let vals := (transitionTable bit).map (fun p => (p.1, p.2 (fun _ => acc)))
  have hexists : ∃ p ∈ vals, p.1 <+: acc := by
    refine ⟨(microCode s, transitionBranch bit s (fun _ => acc)), ?_, ?_⟩
    · simp [vals, transitionTable, microState_mem s]
    · exact ⟨payload, by simp [acc, List.append_assoc]⟩
  have hall : ∀ q ∈ vals, q.1 <+: acc →
      q.2 = microCode (microStep s bit).1 ++ payload ++ (microStep s bit).2 := by
    intro q hq hprefix
    rcases List.mem_map.mp hq with ⟨p, hp, hqeq⟩
    rcases List.mem_map.mp hp with ⟨t, ht, hpeq⟩
    subst q
    subst p
    rcases hprefix with ⟨suffix, hcat⟩
    have hcode : microCode t = microCode s := by
      have htaken := congrArg (List.take 5) hcat
      simpa [microCode_length] using htaken
    have hst : t = s := microCode_injective hcode
    subst t
    simpa [transitionBranch, acc, List.drop_append, microCode_length,
      List.append_assoc]
  have hfold := Complexity.Cobham.foldr_table_eq acc invalidCode
    (microCode (microStep s bit).1 ++ payload ++ (microStep s bit).2) vals
    hexists hall
  unfold transitionFn
  simpa [vals, transitionTable, acc, List.foldr_map] using hfold
theorem transitionFn_mem (bit : Bool) : Complexity.Cobham (transitionFn bit) := by
  unfold transitionFn transitionTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 1))
    (Complexity.Cobham.const invalidCode)
  intro p hp
  rcases List.mem_map.mp hp with ⟨s, hs, rfl⟩
  exact transitionBranch_mem bit s
/-- At the end, only ready-between0 is accepted and receives the final false
    marker. Every other control state returns the empty NO word. -/
def finishBranch (s : MicroState) (v : Fin 1 → List Bool) : List Bool :=
  match s with
  | .ready .between0 => (v 0).drop 5 ++ [false]
  | _ => []

def finishTable : List (List Bool × ((Fin 1 → List Bool) → List Bool)) :=
  microStates.map (fun s => (microCode s, finishBranch s))

def finishFn (v : Fin 1 → List Bool) : List Bool :=
  finishTable.foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finishBranch_mem (s : MicroState) :
    Complexity.Cobham (finishBranch s) := by
  cases s with
  | ready q =>
    cases q with
    | between0 =>
      simp [finishBranch]
      exact Complexity.Cobham.appendFn dropFiveFn_mem
        (Complexity.Cobham.const [false])
    | between1 => exact Complexity.Cobham.empty
    | between2 => exact Complexity.Cobham.empty
    | body0 => exact Complexity.Cobham.empty
    | body1 => exact Complexity.Cobham.empty
    | body2 => exact Complexity.Cobham.empty
    | awaitClause => exact Complexity.Cobham.empty
  | half q b => exact Complexity.Cobham.empty
  | invalid => exact Complexity.Cobham.empty

theorem finishFn_mem : Complexity.Cobham finishFn := by
  unfold finishFn finishTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 1))
    (Complexity.Cobham.const [])
  intro p hp
  rcases List.mem_map.mp hp with ⟨s, hs, rfl⟩
  exact finishBranch_mem s

/-- Lookup is exact because all control codes have width five and are
    pairwise distinct. -/
theorem finishFn_value (s : MicroState) (payload : List Bool) :
    finishFn (fun _ => microCode s ++ payload) =
      match s with
      | .ready .between0 => payload ++ [false]
      | _ => [] := by
  let acc := microCode s ++ payload
  let vals := finishTable.map (fun p => (p.1, p.2 (fun _ => acc)))
  have hexists : ∃ p ∈ vals, p.1 <+: acc := by
    refine ⟨(microCode s, finishBranch s (fun _ => acc)), ?_, ?_⟩
    · simp [vals, finishTable, microState_mem s]
    · exact ⟨payload, by simp [acc, List.append_assoc]⟩
  have hall : ∀ q ∈ vals, q.1 <+: acc →
      q.2 = (match s with
        | .ready .between0 => payload ++ [false]
        | _ => []) := by
    intro q hq hprefix
    rcases List.mem_map.mp hq with ⟨p, hp, hqeq⟩
    rcases List.mem_map.mp hp with ⟨t, ht, hpeq⟩
    subst q
    subst p
    rcases hprefix with ⟨suffix, hcat⟩
    have hcode : microCode t = microCode s := by
      have htaken := congrArg (List.take 5) hcat
      simpa [microCode_length] using htaken
    have hst : t = s := microCode_injective hcode
    subst t
    simp [finishTable, finishBranch, acc, List.drop_append,
      microCode_length]
  have hfold := Complexity.Cobham.foldr_table_eq acc []
    (match s with | .ready .between0 => payload ++ [false] | _ => []) vals
    hexists hall
  unfold finishFn
  simpa [vals, finishTable, acc, List.foldr_map] using hfold

def microAccStep (acc : MicroState × List Bool) (bit : Bool) :
    MicroState × List Bool :=
  let t := microStep acc.1 bit
  (t.1, acc.2 ++ t.2)

def microFold (acc : MicroState × List Bool) (bits : List Bool) :
    MicroState × List Bool := bits.foldl microAccStep acc

def microFoldFrom (q : State) (bits : List Bool) : MicroState × List Bool :=
  microFold (.ready q, []) bits
theorem microFold_pair (q : State) (a b : Bool) :
    microFold (.ready q, []) [a, b] =
      match pairStep q a b with
      | none => (.invalid, [])
      | some (q', emitted) => (.ready q', emitted) := by
  rfl

theorem microStep_output_length (s : MicroState) (bit : Bool) :
    (microStep s bit).2.length ≤ 2 := by
  cases s with
  | ready q => simp [microStep]
  | half q first => cases q <;> cases first <;> cases bit <;>
      simp [microStep, pairStep] <;> omega
  | invalid => simp [microStep]

theorem microFold_payload_length (acc : MicroState × List Bool) (bits : List Bool) :
    (microFold acc bits).2.length ≤ acc.2.length + 2 * bits.length := by
  induction bits generalizing acc with
  | nil => simp [microFold]
  | cons bit bits ih =>
    simp only [microFold, List.foldl_cons]
    have ht := microStep_output_length acc.1 bit
    have htail := ih (microAccStep acc bit)
    simp only [microAccStep] at htail
    simp only [Prod.snd] at htail
    simp only [List.length_append] at htail
    omega

theorem microFold_append (acc : MicroState × List Bool) (left right : List Bool) :
    microFold acc (left ++ right) = microFold (microFold acc left) right := by
  simp [microFold, List.foldl_append]

theorem microFold_payload_decomp (s : MicroState) (payload bits : List Bool) :
    microFold (s, payload) bits =
      ((microFold (s, []) bits).1,
        payload ++ (microFold (s, []) bits).2) := by
  induction bits generalizing s payload with
  | nil => simp [microFold]
  | cons bit bits ih =>
    simp only [microFold, List.foldl_cons]
    rw [ih]
    simp [microAccStep, List.append_assoc]

theorem microFold_append_payload (acc : MicroState × List Bool) (left right : List Bool) :
    microFold acc (left ++ right) =
      ((microFold ((microFold acc left).1, []) right).1,
        (microFold acc left).2 ++
          (microFold ((microFold acc left).1, []) right).2) := by
  rw [microFold_append]
  cases acc with
  | mk s payload => rw [microFold_payload_decomp s payload left,
      microFold_payload_decomp (microFold (s, payload) left).1
        (microFold (s, payload) left).2 right]

theorem run_success_implies_microFold (q : State) (w : List Bool) (out : List Bool)
    (h : run q w = some out) :
    ∃ q', microFold (.ready q, []) w = (.ready q', out) := by
  induction w using List.strong_induction_on generalizing q out with
  | h w ih =>
    cases w with
    | nil =>
      simp [run] at h
      exact ⟨q, by simp [microFold]⟩
    | cons a xs =>
      cases xs with
      | nil => simp [run] at h
      | cons b rest =>
        cases hpair : pairStep q a b with
        | none => simp [run, hpair] at h
        | some pair =>
          rcases pair with ⟨q', emitted⟩
          cases htail : run q' rest with
          | none => simp [run, hpair, htail] at h
          | some suffix =>
            have hout : out = emitted ++ suffix := by
              simpa [run, hpair, htail] using h
            have hsmall : rest.length < (a :: b :: rest).length := by simp
            obtain ⟨q'', hfold⟩ := ih rest hsmall q' suffix htail
            refine ⟨q'', ?_⟩
            rw [show a :: b :: rest = [a, b] ++ rest by rfl,
              microFold_append, microFold_pair, hpair,
              microFold_payload_decomp q' emitted rest, hfold]
            simp [hout]

theorem run_success_implies_machineFold (q : State) (w : List Bool) (out : List Bool)
    (h : run q w = some out) :
    ∃ payload, microFold (.ready q, []) w = (.ready .between0, payload) ∧
      out = payload ++ [false] := by
  induction w using List.strong_induction_on generalizing q out with
  | h w ih =>
    cases w with
    | nil =>
      cases q <;> simp [run, microFold] at h ⊢
    | cons a xs =>
      cases xs with
      | nil => simp [run] at h
      | cons b rest =>
        cases hpair : pairStep q a b with
        | none => simp [run, hpair] at h
        | some pair =>
          rcases pair with ⟨q', emitted⟩
          cases htail : run q' rest with
          | none => simp [run, hpair, htail] at h
          | some suffix =>
            have hout0 : out = emitted ++ suffix := by
              simpa [run, hpair, htail] using h
            have hsmall : rest.length < (a :: b :: rest).length := by simp
            obtain ⟨payload, hfold, hout⟩ := ih rest hsmall q' suffix htail
            have hfoldWhole :
                microFold (.ready q, []) (a :: b :: rest) =
                  (.ready .between0, emitted ++ payload) := by
              rw [show a :: b :: rest = [a, b] ++ rest by rfl,
                microFold_append, microFold_pair, hpair,
                microFold_payload_decomp q' emitted rest, hfold]
            refine ⟨emitted ++ payload, hfoldWhole, ?_⟩
            rw [hout0, hout]
            simp [List.append_assoc]
theorem microFold_invalid_absorbs (bits : List Bool) :
    microFold (.invalid, []) bits = (.invalid, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [microFold, List.foldl_cons, microAccStep,
      microStep, ih]

theorem machineFold_implies_run (q : State) (w : List Bool) (payload : List Bool)
    (h : microFold (.ready q, []) w = (.ready .between0, payload)) :
    run q w = some (payload ++ [false]) := by
  induction w using List.strong_induction_on generalizing q payload with
  | h w ih =>
    cases w with
    | nil => cases q <;> simp [run, microFold] at h ⊢
    | cons a xs =>
      cases xs with
      | nil => simp [microFold, List.foldl_cons, microAccStep, microStep] at h
      | cons b rest =>
        have hfold := h
        rw [show a :: b :: rest = [a, b] ++ rest by rfl,
          microFold_append, microFold_pair] at hfold
        cases hpair : pairStep q a b with
        | none =>
          rw [hpair, microFold_invalid_absorbs] at hfold
          cases hfold
        | some pair =>
          rcases pair with ⟨q', emitted⟩
          rw [hpair, microFold_payload_decomp q' emitted rest] at hfold
          cases htail : microFold (.ready q', []) rest with
          | mk state tailPayload =>
            rw [htail] at hfold
            rcases Prod.mk.inj hfold with ⟨hstate, hpayload⟩
            cases state with
            | ready q'' =>
              have hq : q'' = .between0 := by cases q'' <;> simp at hstate
              subst q''
              have hsmall : rest.length < (a :: b :: rest).length := by simp
              have hrun := ih rest hsmall q' tailPayload htail
              have hprefix : payload = emitted ++ tailPayload := by simpa using hpayload
              simpa [run, hpair, hrun, hprefix, List.append_assoc]
            | half q'' bit => simp at hstate
            | invalid => simp at hstate
def initialAccumulator : MicroState × List Bool := (.ready .between0, [])

def scanRec (r : List Bool) : List Bool :=
  Complexity.recNotation
    (fun _ : Fin 0 → List Bool => microCode initialAccumulator.1)
    (fun w : Fin 2 → List Bool => transitionFn false (fun _ => w 1))
    (fun w : Fin 2 → List Bool => transitionFn true (fun _ => w 1))
    r (fun i => Fin.elim0 i)

theorem scanRec_cons (bit : Bool) (r : List Bool) :
    scanRec (bit :: r) = transitionFn bit (fun _ => scanRec r) := by
  cases bit <;> rfl

theorem scanRec_eq_microFold (r : List Bool) :
    scanRec r = microCode (microFold initialAccumulator r.reverse).1 ++
      (microFold initialAccumulator r.reverse).2 := by
  induction r with
  | nil => rfl
  | cons bit r ih =>
    rw [scanRec_cons, ih, List.reverse_cons, microFold_append]
    cases h : microFold initialAccumulator r.reverse with
    | mk s payload =>
      rw [transitionFn_value, h]
      cases bit <;> simp [microFold, microAccStep, microStep, h,
        List.append_assoc]

theorem scanRec_length (r : List Bool) : scanRec r |>.length ≤ 5 + 2 * r.length := by
  rw [scanRec_eq_microFold]
  have hp := microFold_payload_length initialAccumulator r.reverse
  simp [initialAccumulator, microCode_length] at hp
  simp only [List.length_append, microCode_length]
  have hr : r.reverse.length = r.length := List.length_reverse r
  omega

def scanRecFnRaw (v : Fin 1 → List Bool) : List Bool := scanRec (v 0)

/-- `recNotation` peels a list from its right end. Reversing the input at the
    wrapper restores the scanner's intended left-to-right bit order. -/
def scanRecFn (v : Fin 1 → List Bool) : List Bool :=
  scanRec (Complexity.reverse (v 0))

def scanBoundFn (v : Fin 1 → List Bool) : List Bool :=
  microCode initialAccumulator.1 ++ v 0 ++ v 0

theorem scanBoundFn_mem : Complexity.Cobham scanBoundFn := by
  unfold scanBoundFn
  exact Complexity.Cobham.appendFn
    (Complexity.Cobham.const (microCode initialAccumulator.1))
    (Complexity.Cobham.appendFn
      (Complexity.Cobham.proj (0 : Fin 1))
      (Complexity.Cobham.proj (0 : Fin 1)))

def scanStep0 (w : Fin 2 → List Bool) : List Bool :=
  transitionFn false (fun _ => w 1)

def scanStep1 (w : Fin 2 → List Bool) : List Bool :=
  transitionFn true (fun _ => w 1)

theorem scanRecFnRaw_mem : Complexity.Cobham scanRecFnRaw := by
  have hbase : Complexity.Cobham
      (fun _ : Fin 0 → List Bool => microCode initialAccumulator.1) :=
    Complexity.Cobham.const (microCode initialAccumulator.1)
  have h0 : Complexity.Cobham scanStep0 := by
    exact Complexity.Cobham.comp (transitionFn_mem false)
      (fun _ : Fin 1 => Complexity.Cobham.proj (1 : Fin 2))
  have h1 : Complexity.Cobham scanStep1 := by
    exact Complexity.Cobham.comp (transitionFn_mem true)
      (fun _ : Fin 1 => Complexity.Cobham.proj (1 : Fin 2))
  have hbound : ∀ x v,
      (Complexity.recNotation
        (fun _ : Fin 0 → List Bool => microCode initialAccumulator.1)
        scanStep0 scanStep1 x v).length ≤ (scanBoundFn (Fin.cons x v)).length := by
    intro x v
    have hlen := scanRec_length x
    simpa [scanRec, scanStep0, scanStep1, scanBoundFn,
      Complexity.recNotation, microCode_length, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hlen
  change Complexity.Cobham scanRecFnRaw
  unfold scanRecFnRaw
  exact (Complexity.Cobham.boundedRec hbase h0 h1 scanBoundFn_mem hbound).of_eq
    (fun v => rfl)

theorem scanRecFn_mem : Complexity.Cobham scanRecFn := by
  have hrev : Complexity.Cobham
      (fun v : Fin 1 → List Bool => Complexity.reverse (v 0)) := by
    have hfp : (fun x : List Bool => x.reverse) ∈ Complexity.FP :=
      Complexity.reverse_mem_FP
    have hcobham := Complexity.FP_subset_CobhamFP hfp
    exact hcobham
  unfold scanRecFn
  exact Complexity.Cobham.comp scanRecFnRaw_mem
    (fun _ => hrev)

/-- The concrete machine output after its accepting-state check. It returns
    the emitted payload with a false terminal marker exactly when the scan
    ends in the formula-boundary state; malformed and incomplete scans map
    to the empty word. -/
def machineOutput (v : Fin 1 → List Bool) : List Bool :=
  finishFn (fun _ => scanRecFn v)

theorem machineOutput_mem : Complexity.Cobham machineOutput := by
  unfold machineOutput
  exact Complexity.Cobham.comp finishFn_mem (fun _ => scanRecFn_mem)

theorem scanRecFn_state_payload (w : List Bool) :
    scanRecFn (fun _ => w) =
      microCode (microFold initialAccumulator w).1 ++
        (microFold initialAccumulator w).2 := by
  unfold scanRecFn
  rw [scanRec_eq_microFold]
  simp only [List.reverse_reverse]

theorem machineOutput_spec (w : List Bool) :
    machineOutput (fun _ => w) =
      if (microFold initialAccumulator w).1 = .ready .between0
      then (microFold initialAccumulator w).2 ++ [false] else [] := by
  unfold machineOutput
  rw [scanRecFn_state_payload]
  cases h : microFold initialAccumulator w with
  | mk s payload =>
    rw [finishFn_value]
    cases s with
    | ready q => cases q <;> simp [h]
    | half q b => simp [h]
    | invalid => simp [h]
theorem machineOutput_eq_convert (w : List Bool) :
    machineOutput (fun _ => w) = convert w := by
  cases hrun : run .between0 w with
  | none =>
    have hnot : (microFold initialAccumulator w).1 ≠ .ready .between0 := by
      intro hstate
      cases hfold : microFold initialAccumulator w with
      | mk state payload =>
        have hstate' : state = .ready .between0 := by simpa [hfold] using hstate
        have hfold' : microFold initialAccumulator w = (.ready .between0, payload) := by
          simp [hfold, hstate']
        have hsome := machineFold_implies_run .between0 w payload (by simpa [initialAccumulator] using hfold')
        rw [hrun] at hsome
        cases hsome
    rw [machineOutput_spec]
    simp [convert, hrun, hnot]
  | some out =>
    obtain ⟨payload, hfold, hout⟩ :=
      run_success_implies_machineFold .between0 w out hrun
    rw [machineOutput_spec]
    simp [convert, hrun, initialAccumulator, hfold, hout]
theorem convert_mem_FP : (fun w : List Bool => convert w) ∈ Complexity.FP := by
  have hcb : Complexity.Cobham
      (fun v : Fin 1 → List Bool => convert (v 0)) := by
    exact machineOutput_mem.of_eq (fun v => by
      rw [machineOutput_eq_convert (v 0)])
  exact Complexity.CobhamFP_subset_FP hcb
end LocalThreeSATBinaryCodecContinuationOffer
