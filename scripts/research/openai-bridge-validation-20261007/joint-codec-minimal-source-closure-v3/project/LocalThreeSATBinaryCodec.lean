import Complexitylib.SAT.Encoding

/-! Total two-bit scanner core for the local exact-three-CNF token language.
    Invalid streams have no result; `convert` maps every such stream to `[]`. -/
namespace LocalThreeSATBinaryCodecOffer

open Complexity.SAT

inductive State where
  | between0 | between1 | between2
  | body0 | body1 | body2
  | awaitClause
  deriving DecidableEq, BEq, Repr

/-- Consume one complete input pair. The emitted list is at most two bits. -/
def pairStep : State -> Bool -> Bool -> Option (Prod State (List Bool))
  | .between0, a, b =>
      if a == b then some (.body0, [true, b]) else none
  | .between1, a, b =>
      if a == b then some (.body1, [b]) else none
  | .between2, a, b =>
      if a == b then some (.body2, [b]) else none
  | .body0, true, true => some (.body0, [true, true])
  | .body0, false, true => some (.between1, [false])
  | .body1, true, true => some (.body1, [true, true])
  | .body1, false, true => some (.between2, [false])
  | .body2, true, true => some (.body2, [true, true])
  | .body2, false, true => some (.awaitClause, [false])
  | .awaitClause, true, false => some (.between0, [])
  | _, _, _ => none

def run (q : State) : List Bool -> Option (List Bool)
  | [] => if q == .between0 then some [false] else none
  | [_] => none
  | a :: b :: rest =>
      match pairStep q a b with
      | none => none
      | some (q', emitted) =>
          match run q' rest with
          | none => none
          | some suffix => some (emitted ++ suffix)
termination_by xs => xs.length

/-- Total converter. Malformed or incomplete token streams map to `[]`. -/
def convert (w : List Bool) : List Bool := (run .between0 w).getD []

/-- The valid empty local formula maps to the target empty-formula encoding. -/
@[simp] theorem convert_empty : convert [] = [false] := by
  rfl

/-- Framed output for a literal after its clause's first literal. The variable
    n is represented by n framed true digits; no exponent or sparse integer is
    constructed. -/
def emitLaterLit (l : Lit) : List Bool :=
  [l.sign] ++ List.replicate (2 * l.var) true ++ [false]

/-- A clause begins with its true marker and then emits its first literal. -/
def emitClause : Clause -> List Bool
  | [] => []
  | l :: ls => true :: (emitLaterLit l ++ ls.flatMap emitLaterLit)

/-- Clause separators have no payload; the final false bit is the total-language
    terminator, including for the valid empty formula. -/
def emitFormula (phi : CNF) : List Bool := phi.flatMap emitClause ++ [false]

@[simp] theorem emitFormula_nil : emitFormula ([] : CNF) = [false] := rfl
@[simp] theorem emitClause_nil : emitClause ([] : Clause) = [] := rfl

end LocalThreeSATBinaryCodecOffer