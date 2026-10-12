import LocalThreeSATBinaryCodec
import Complexitylib.SAT.ThreeSAT

/-! Decoder normal form for the sparse-name target encoding. This source
    proves total all-input behavior relative to the authoritative local
    restricted decoder. Equality with the finite scanner is a separate lemma. -/
namespace LocalThreeSATBinaryCodecSemanticsOffer

open Complexity.SAT
open LocalThreeSATBinaryCodecOffer

def variableMassClause (c : Clause) : Nat :=
  c.foldr (fun l n => l.var + n) 0

def variableMass (phi : CNF) : Nat :=
  phi.foldr (fun c n => variableMassClause c + n) 0

/-- Total semantic normal form: malformed inputs map to `[]`; each decoded
    exact-three formula maps to its framed formula encoding. -/
def decodedOutput (w : List Bool) : List Bool :=
  match CNF.decode3? w with
  | none => []
  | some phi => emitFormula phi

theorem emitLaterLit_length (l : Lit) :
    (emitLaterLit l).length = 2 + 2 * l.var := by
  simp [emitLaterLit]
  omega

theorem flatMap_emitLaterLit_length (ls : Clause) :
    (ls.flatMap emitLaterLit).length =
      2 * ls.length + 2 * variableMassClause ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp [variableMassClause, emitLaterLit_length, ih]
      omega

theorem emitClause_length_exact3 (c : Clause) (hc : c.length = 3) :
    (emitClause c).length = 7 + 2 * variableMassClause c := by
  cases c with
  | nil => simp at hc
  | cons l ls =>
      have hls : ls.length = 2 := by simp at hc; omega
      simp [emitClause, emitLaterLit_length, flatMap_emitLaterLit_length,
        variableMassClause]
      omega

theorem emitFormula_length_exact3 (phi : CNF) (h3 : phi.Is3CNF) :
    (emitFormula phi).length = 1 + 7 * phi.length + 2 * variableMass phi := by
  induction phi with
  | nil => rfl
  | cons c cs ih =>
      have h3' := (CNF.is3CNF_cons).mp h3
      simp only [emitFormula, List.flatMap_cons, List.length_append,
        emitClause_length_exact3 c h3'.1, variableMass]
      rw [ih h3'.2]
      omega

theorem decodedOutput_eq_on_encoding (phi : CNF) (h3 : phi.Is3CNF) :
    decodedOutput phi.encode = emitFormula phi := by
  simp [decodedOutput, CNF.decode3?_encode h3]

theorem decodedOutput_empty : decodedOutput [] = [false] := by
  have h3 : ([] : CNF).Is3CNF := CNF.is3CNF_nil
  simp [decodedOutput, CNF.decode3?_encode h3, emitFormula]

theorem emitFormula_ne_nil (phi : CNF) : emitFormula phi ≠ [] := by
  simp [emitFormula]

theorem decodedOutput_eq_nil_iff (w : List Bool) :
    decodedOutput w = [] ↔ CNF.decode3? w = none := by
  cases h : CNF.decode3? w with
  | none => simp [decodedOutput, h]
  | some phi =>
      simp only [decodedOutput, h]
      constructor
      · intro heq
        exact (emitFormula_ne_nil phi) heq
      · intro hnone
        cases hnone

/-- The exact local language has a decoder witness precisely when its
    semantic output is the framed encoding of a satisfiable decoded formula. -/
theorem threeSAT_iff_decodedOutput (w : List Bool) :
    w ∈ ThreeSAT.language ↔
      ∃ phi, CNF.decode3? w = some phi ∧
        decodedOutput w = emitFormula phi ∧ phi.Satisfiable := by
  rw [ThreeSAT.mem_language_iff_decode3]
  constructor
  · rintro ⟨phi, hdecode, hsat⟩
    exact ⟨phi, hdecode, by simp [decodedOutput, hdecode], hsat⟩
  · rintro ⟨phi, hdecode, _hout, hsat⟩
    exact ⟨phi, hdecode, hsat⟩

/-- The captured pair scanner is intended to implement the normal form above.
    This predicate is kept explicit until the all-input equivalence is proved. -/
def scannerMatchesDecoder : Prop :=
  ∀ w, convert w = decodedOutput w

end LocalThreeSATBinaryCodecSemanticsOffer
