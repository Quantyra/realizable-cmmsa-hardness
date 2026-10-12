import LocalThreeSATBinaryCodecRuntime
import OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas

/-! Transport the local exact-3SAT codec to the pinned upstream binary SAT parser.
    The theorem uses the actual upstream BinaryLanguage declarations; it does
    not introduce a replacement parser or a runtime assumption. -/
namespace LocalThreeSATBinaryCodecUpstreamOffer

open _root_.Complexity.SAT
open _root_.LocalThreeSATBinaryCodecOffer
open OAI.UniqueGamesTheorem.BinaryEncoding
open OAI.UniqueGamesTheorem.BinaryLanguage
open OAI.UniqueGamesTheorem.BinaryNameMachine
open OAI.UniqueGamesTheorem.BinaryParsing

/-- The sparse upstream name assigned to local unary name n. Its canonical
    little-endian binary digits are exactly n true digits. -/
def sparseName (n : Nat) : Nat :=
  BinaryEncoding.bitsValue (List.replicate n true)

theorem canonical_replicate_true (n : Nat) :
    BinaryNameMachine.canonical (List.replicate n true) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => decide
      | succ n =>
          simpa [List.replicate_succ,
            BinaryParsing.canonical_cons_cons] using ih

theorem sparseName_bits (n : Nat) :
    (sparseName n).bits = List.replicate n true := by
  exact (BinaryParsing.canonical_iff (List.replicate n true)).mp
    (canonical_replicate_true n)

theorem sparseName_injective : Function.Injective sparseName := by
  intro a b hab
  have hbits := congrArg Nat.bits hab
  rw [sparseName_bits, sparseName_bits] at hbits
  have hlen : a = b := by simpa using congrArg List.length hbits
  exact hlen

def sparseAssignment (alpha : List Bool) : Nat -> Bool := by
  classical
  exact fun x => if hx : Exists fun n => sparseName n = x
    then alpha.getD (Classical.choose hx) false else false

theorem sparseAssignment_at (alpha : List Bool) (n : Nat) :
    sparseAssignment alpha (sparseName n) = alpha.getD n false := by
  classical
  unfold sparseAssignment
  have hx : Exists fun k => sparseName k = sparseName n := ⟨n, rfl⟩
  rw [dif_pos hx]
  have hchoose : Classical.choose hx = n :=
    sparseName_injective (Classical.choose_spec hx)
  rw [hchoose]

def localLiteralToBinary (l : Lit) : BinaryFormula.Literal :=
  ⟨sparseName l.var, l.sign⟩

def localClauseToBinary (c : Clause) : BinaryFormula.Clause :=
  #v[localLiteralToBinary (c.getD 0 ⟨true, 0⟩),
     localLiteralToBinary (c.getD 1 ⟨true, 0⟩),
     localLiteralToBinary (c.getD 2 ⟨true, 0⟩)]

def localFormulaToBinary (phi : CNF) : BinaryFormula.Formula :=
  ⟨phi.map localClauseToBinary⟩

theorem clause_shape_of_mem (phi : CNF) (h3 : phi.Is3CNF)
    {c : Clause} (hc : c ∈ phi) : c.length = 3 := by
  induction phi with
  | nil => simp at hc
  | cons d ds ih =>
    have hshape := (CNF.is3CNF_cons).mp h3
    rcases List.mem_cons.mp hc with h | h
    · subst c
      exact hshape.1
    · exact ih hshape.2 h

theorem localClauseToBinary_correct (c : Clause) (hc : c.length = 3)
    (alpha : List Bool) (beta : Nat -> Bool)
    (hassign : forall l, l ∈ c -> beta (sparseName l.var) = alpha.getD l.var false) :
    BinaryFormula.Clause.eval (localClauseToBinary c) beta = Clause.eval alpha c := by
  cases c with
  | nil => simp at hc
  | cons a xs =>
    cases xs with
    | nil => simp at hc
    | cons b xs =>
      cases xs with
      | nil => simp at hc
      | cons d rest =>
        have hnil : rest = [] := by simp at hc; omega
        subst rest
        have ha := hassign a (by simp)
        have hb := hassign b (by simp)
        have hd := hassign d (by simp)
        simp [localClauseToBinary, localLiteralToBinary,
          BinaryFormula.Clause.eval, BinaryFormula.Literal.eval,
          Clause.eval, Lit.eval, ha, hb, hd]

theorem localFormulaToBinary_satisfiable (phi : CNF) (h3 : phi.Is3CNF) :
    phi.Satisfiable <-> (localFormulaToBinary phi).Satisfiable := by
  constructor
  · rintro ⟨alpha, halpha⟩
    refine ⟨sparseAssignment alpha, ?_⟩
    intro bc hbc
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbc
    have hcshape := clause_shape_of_mem phi h3 hc
    have heval : Clause.eval alpha c = true := by
      have hall : CNF.eval alpha phi = true := halpha
      have hall' : phi.all (Clause.eval alpha) = true := by simpa [CNF.eval] using hall
      exact (List.all_eq_true.mp hall') c hc
    rw [localClauseToBinary_correct c hcshape alpha (sparseAssignment alpha)]
    · exact heval
    · intro l hl
      exact sparseAssignment_at alpha l.var
  · rintro ⟨beta, hbeta⟩
    refine ⟨List.ofFn (fun i : Fin (phi.maxVar + 1) => beta (sparseName i.val)), ?_⟩
    have hall : phi.all (Clause.eval
        (List.ofFn (fun i : Fin (phi.maxVar + 1) => beta (sparseName i.val)))) = true := by
      apply List.all_eq_true.mpr
      intro c hc
      have hcshape := clause_shape_of_mem phi h3 hc
      have hmap : localClauseToBinary c ∈ (localFormulaToBinary phi).clauses :=
        List.mem_map.mpr ⟨c, hc, rfl⟩
      have hbin := hbeta (localClauseToBinary c) hmap
      rw [← localClauseToBinary_correct c hcshape
        (List.ofFn (fun i : Fin (phi.maxVar + 1) => beta (sparseName i.val))) beta]
      · exact hbin
      · intro l hl
        have hvar₁ := Clause.var_le_maxVar hl
        have hvar₂ := CNF.clause_maxVar_le_maxVar hc
        have hvar : l.var < phi.maxVar + 1 := by omega
        simp [List.getD_ofFn, hvar]
    simpa [CNF.eval] using hall
theorem sparseName_frame (n : Nat) :
    BinaryEncoding.nameBits (sparseName n) =
      List.replicate (2 * n) true ++ [false] := by
  simp [BinaryEncoding.nameBits, BinaryEncoding.frame, sparseName_bits,
    List.replicate_succ, List.append_assoc]

theorem literalBits_local (l : Lit) :
    BinaryEncoding.literalBits (localLiteralToBinary l) = emitLaterLit l := by
  simp [BinaryEncoding.literalBits, localLiteralToBinary,
    BinaryEncoding.nameBits, sparseName_frame, emitLaterLit,
    List.append_assoc]

theorem clauseBits_local (c : Clause) (hc : c.length = 3) :
    BinaryEncoding.clauseBits (localClauseToBinary c) = emitClause c := by
  cases c with
  | nil => simp at hc
  | cons a xs =>
    cases xs with
    | nil => simp at hc
    | cons b xs =>
      cases xs with
      | nil => simp at hc
      | cons d rest =>
        have hnil : rest = [] := by simp at hc; omega
        subst rest
        simp [BinaryEncoding.clauseBits, localClauseToBinary,
          localLiteralToBinary, literalBits_local, emitClause,
          emitLaterLit, List.append_assoc]

theorem emitFormula_eq_binaryFormulaBits (phi : CNF) (h3 : phi.Is3CNF) :
    emitFormula phi = BinaryEncoding.formulaBits (localFormulaToBinary phi) := by
  induction phi with
  | nil => rfl
  | cons c cs ih =>
    have hshape := (CNF.is3CNF_cons).mp h3
    simp only [emitFormula, List.flatMap_cons, BinaryEncoding.formulaBits,
      BinaryEncoding.clausesBits, localFormulaToBinary, List.map_cons]
    rw [clauseBits_local c hshape.1, ih hshape.2]
    simp [emitClause, List.append_assoc]

theorem decode_emitFormula (phi : CNF) (h3 : phi.Is3CNF) :
    BinaryEncoding.decodeFormula (emitFormula phi) =
      some (localFormulaToBinary phi) := by
  rw [emitFormula_eq_binaryFormulaBits phi h3]
  exact BinaryEncoding.decodeFormula_encoded (localFormulaToBinary phi)

theorem malformed_convert_empty (w : List Bool)
    (hdecode : CNF.decode3? w = none) : convert w = [] := by
  have hnormal := LocalThreeSATBinaryCodecContinuationOffer.scannerMatchesDecoder w
  rw [LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput_eq_nil_iff] at hnormal
  simpa [LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput, hdecode] using hnormal

theorem localThreeSAT_iff_binaryLanguage (w : List Bool) :
    w \in ThreeSAT.language <->
      BinaryLanguage.language (convert w) := by
  rw [ThreeSAT.mem_language_iff_decode3]
  constructor
  · rintro ⟨phi, hdecode, hsat⟩
    have h3 := (CNF.decode3?_sound hdecode).2
    rw [LocalThreeSATBinaryCodecContinuationOffer.convert_eq_decodedOutput_of_decode
      w phi hdecode]
    simp only [LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput,
      hdecode, Option.getD_some]
    unfold BinaryLanguage.language
    refine ⟨localFormulaToBinary phi, decode_emitFormula phi h3, ?_⟩
    exact (localFormulaToBinary_satisfiable phi h3).mp hsat
  · intro hbin
    cases hdecode : CNF.decode3? w with
    | none =>
      have hconvert := malformed_convert_empty w hdecode
      rw [hconvert] at hbin
      simp [BinaryLanguage.language, BinaryEncoding.decodeFormula] at hbin
    | some phi =>
      have h3 := (CNF.decode3?_sound hdecode).2
      have hconvert :=
        LocalThreeSATBinaryCodecContinuationOffer.convert_eq_decodedOutput_of_decode
          w phi hdecode
      simp only [hconvert, LocalThreeSATBinaryCodecSemanticsOffer.decodedOutput,
        hdecode, Option.getD_some] at hbin
      unfold BinaryLanguage.language at hbin
      rcases hbin with ⟨target, hparse, hsat⟩
      have hinput : emitFormula phi = BinaryEncoding.formulaBits target :=
        BinaryParsing.decodeFormula_sound _ _ hparse
      have htarget : target = localFormulaToBinary phi := by
        apply BinaryEncoding.formulaBits_injective
        rw [emitFormula_eq_binaryFormulaBits phi h3] at hinput
        exact hinput.symm
      subst target
      exact ⟨phi, hdecode, (localFormulaToBinary_satisfiable phi h3).mpr hsat⟩

end LocalThreeSATBinaryCodecUpstreamOffer
