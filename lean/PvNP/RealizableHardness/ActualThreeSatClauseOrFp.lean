import PvNP.RealizableHardness.ActualThreeSatLitVarFp
import PvNP.RealizableHardness.CMMSAEncoding
import Complexitylib.Classes.PCP.Internal.CoinEnum
import Complexitylib.Classes.PCP.Internal.StripTrailing

/-!
Thin `Function.comp` surface for the clause-0 3-OR formula tree.

`clauseOrEnc` is in `Complexity.FP`.  It does **not** import the
selected-map / `encodeInput` stack.  Digit encoding is the same Cobham
`recFoldClamp` used by `encodeDigitsFn`, copied here so this module stays
thin.

Not a packed `encodeData` Yes/No instance, not `No σ_L γ_L` on unsat,
not `if-sat`.  Does not inhabit `hSrcCmmsa`.  Checking-transducer
`mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatClauseOrFp

open Complexity
open ActualThreeSatLitVarFp
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

private def encFalse (z : List Bool) : List Bool :=
  [true, false] ++ pairSnd (pairFst z)

private def encTrue (z : List Bool) : List Bool :=
  [true, true, false, false] ++ pairSnd (pairFst z)

private theorem encFalse_mem_FP : encFalse ∈ Complexity.FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ Complexity.FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) h

private theorem encTrue_mem_FP : encTrue ∈ Complexity.FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ Complexity.FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (constFn_mem_FP [true, true, false, false]) h

def encodeDigits : List Bool → List Bool
  | [] => [false]
  | false :: t => [true, false] ++ encodeDigits t
  | true :: t => [true, true, false, false] ++ encodeDigits t

theorem encodeDigits_eq (bs : List Bool) :
    encodeDigits bs = CMMSACodec.Tree.encode (digitTree bs) := by
  induction bs with
  | nil => simp [encodeDigits, digitTree, CMMSACodec.Tree.encode]
  | cons b t ih =>
      cases b <;> simp [encodeDigits, digitTree, CMMSACodec.Tree.encode, ih]

private theorem encodeDigits_length (bs : List Bool) :
    (encodeDigits bs).length ≤ 4 * bs.length + 1 := by
  rw [encodeDigits_eq]
  simpa using digitTree_length bs

private theorem recFold_encodeDigits (W : List Bool) :
    ∀ bs : List Bool,
      Cobham.recFold encFalse encTrue [false] W bs = encodeDigits bs := by
  intro bs
  induction bs with
  | nil => simp [Cobham.recFold, encodeDigits]
  | cons b t ih =>
      cases b <;> simp [Cobham.recFold, encFalse, encTrue, encodeDigits, ih]

private theorem recFoldClamp_encodeDigits (bound : Nat) (W : List Bool) :
    ∀ bs : List Bool, 4 * bs.length + 1 ≤ bound →
      Cobham.recFoldClamp encFalse encTrue bound [false] W bs =
        encodeDigits bs := by
  intro bs hb
  have hle : ∀ t : List Bool, t.length ≤ bs.length →
      (Cobham.recFold encFalse encTrue [false] W t).length ≤ bound := by
    intro t ht
    rw [recFold_encodeDigits]
    have := encodeDigits_length t
    omega
  rw [Cobham.recFoldClamp_eq_recFold bs hle, recFold_encodeDigits]

def encodeDigitsFn (z : List Bool) : List Bool :=
  Cobham.recFoldClamp encFalse encTrue (4 * z.length + 1) [false] [] z

theorem encodeDigitsFn_eq (z : List Bool) :
    encodeDigitsFn z = encodeDigits z :=
  recFoldClamp_encodeDigits _ _ z (Nat.le_refl _)

private theorem encodeDigits_mem_FP :
    (fun z : List Bool => encodeDigits z) ∈ Complexity.FP := by
  have hE : (fun _ : List Bool => ([false] : List Bool)) ∈ Complexity.FP :=
    constFn_mem_FP [false]
  have hpoly := Cobham.recFoldClamp_mem_FP encFalse_mem_FP encTrue_mem_FP hE
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 1)
  have harg : (fun z : List Bool => pair [] z) ∈ Complexity.FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) id_mem_FP
  have hcomp := mem_FP_comp harg hpoly
  refine mem_FP_of_eq hcomp fun z => ?_
  change Cobham.recFoldClamp encFalse encTrue
      ((Polynomial.C 4 * Polynomial.X + Polynomial.C 1 : Polynomial Nat).eval
        (pair [] z).length)
      [false] (pairFst (pair [] z)) (pairSnd (pair [] z)) =
    encodeDigits z
  simp only [pairFst_pair, pairSnd_pair, pair_length, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  refine recFoldClamp_encodeDigits _ _ z ?_
  omega

theorem encodeDigitsFn_mem_FP : encodeDigitsFn ∈ Complexity.FP :=
  mem_FP_of_eq encodeDigits_mem_FP fun z => (encodeDigitsFn_eq z).symm

def unaryBitsFn (z : List Bool) : List Bool :=
  stripFn (pair [] (coinStr (z.length + 1) z.length))

theorem unaryBitsFn_mem_FP : unaryBitsFn ∈ Complexity.FP := by
  have hwidth : (fun z : List Bool => List.replicate (z.length + 1) true) ∈
      Complexity.FP :=
    mem_FP_comp unaryLength_mem_FP (Cobham.cons_mem_FP true)
  have hval : (fun z : List Bool => List.replicate z.length true) ∈
      Complexity.FP := unaryLength_mem_FP
  have hcoin := coinStr_mem_FP (t := fun z => z.length + 1)
    (c := fun z => z.length) hwidth hval
  have hpair : (fun z : List Bool =>
      pair [] (coinStr (z.length + 1) z.length)) ∈ Complexity.FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) hcoin
  exact mem_FP_comp hpair stripFn_mem_FP

def prependVarTag : List Bool → List Bool :=
  fun z => [true, false] ++ z

theorem prependVarTag_mem_FP : prependVarTag ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP [true, false]) id_mem_FP

/-- `Tree.encode` of `.var` whose index is the unary value of the tape. -/
def varTreeEnc : List Bool → List Bool :=
  prependVarTag ∘ encodeDigitsFn ∘ unaryBitsFn

theorem varTreeEnc_mem_FP : varTreeEnc ∈ Complexity.FP :=
  mem_FP_comp
    (mem_FP_comp unaryBitsFn_mem_FP encodeDigitsFn_mem_FP)
    prependVarTag_mem_FP

def clauseVarTreeFn (j p : Nat) : List Bool → List Bool :=
  varTreeEnc ∘ clauseLitVarFn j p

theorem clauseVarTreeFn_mem_FP (j p : Nat) :
    clauseVarTreeFn j p ∈ Complexity.FP :=
  mem_FP_comp (clauseLitVarFn_mem_FP j p) varTreeEnc_mem_FP

def orTreeEnc (p q : List Bool) : List Bool :=
  [true, true, false, true, false, false, true] ++ p ++ q

private theorem orTreeEncFn_mem_FP {p q : List Bool → List Bool}
    (hp : p ∈ Complexity.FP) (hq : q ∈ Complexity.FP) :
    (fun z => orTreeEnc (p z) (q z)) ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP
      (constFn_mem_FP [true, true, false, true, false, false, true]) hp)
    hq

/-- 3-OR of the three variable indices of clause 0. -/
def clauseOrEnc (z : List Bool) : List Bool :=
  orTreeEnc
    (orTreeEnc (clauseVarTreeFn 0 0 z) (clauseVarTreeFn 0 1 z))
    (clauseVarTreeFn 0 2 z)

theorem clauseOrEnc_mem_FP : clauseOrEnc ∈ Complexity.FP :=
  orTreeEncFn_mem_FP
    (orTreeEncFn_mem_FP (clauseVarTreeFn_mem_FP 0 0) (clauseVarTreeFn_mem_FP 0 1))
    (clauseVarTreeFn_mem_FP 0 2)

theorem clauseOrEnc_ne_id : clauseOrEnc [] ≠ [] := by
  intro hz
  have hlen := congrArg List.length hz
  simp [clauseOrEnc, orTreeEnc] at hlen

end
end PvNP.RealizableHardness.ActualThreeSatClauseOrFp
