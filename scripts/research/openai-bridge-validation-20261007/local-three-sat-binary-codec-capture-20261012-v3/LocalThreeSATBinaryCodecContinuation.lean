import LocalThreeSATBinaryCodec
import LocalThreeSATBinaryCodecSemantics

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
    (h : run .between0 w = some out) :
    ∃ l tail suffix,
      w = encodedLiteralChunk l ++ tail ∧
      out = (true :: emitLaterLit l) ++ suffix ∧
      run .between1 tail = some suffix := by
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
    (h : run .between0 w = some out) :
    ∃ a b c tail suffix,
      w = encodedLiteralChunk a ++ encodedLiteralChunk b ++
        encodedLiteralChunk c ++ [true, false] ++ tail ∧
      run .between0 tail = some suffix := by
  obtain ⟨a, t1, s1, hw1, _, h1⟩ := run_between0_literal_success w out h
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
      obtain ⟨l1, l2, l3, tail, suffix, hw, htail⟩ := run_clause_success (a :: xs) out h
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
    exact LocalThreeSATBinaryCodecSemanticsOffer.convert_eq_decodedOutput_of_decode w phi hdecode

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

end LocalThreeSATBinaryCodecContinuationOffer
