import PvNP.RealizableHardness.ActualThreeSatToEncodeInput
import PvNP.RealizableHardness.ActualThreeSatCmmsaReduce
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import Complexitylib.Classes.PCP.Internal.CoinEnum
import Complexitylib.Classes.PCP.Internal.StripTrailing
import Complexitylib.Classes.PCP.Internal.CNFSegment
import Complexitylib.Classes.PCP.Internal.CNFTokens

/-!
FP 3SAT-dependent clause-formula encoder.

`unaryBitsFn` turns a unary counter into `Nat.bits`.  `varTreeEnc` wraps
that as `Tree.encode` of a `.var` formula.  `clauseOrEnc` is the 3-OR of
the three variable indices of clause 0, read by complexitylib `litVarFn`.

`unaryBitsFn` and `varTreeEnc` are in `Complexity.FP`.  `clauseOrEnc` is
the 3SAT-dependent 3-OR tree (clause 0 via `litVarFn`); its `mem_FP` is
in the thin `ActualThreeSatLitVarFp` surface via `slotVar`.  Not a packed
`encodeData` instance, not `No σ_L γ_L` on unsat, not identity, not
`if-sat`.  Does not inhabit `hSrcCmmsa`.  Checking-transducer `mem_FP`
is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCompileFp

open Complexity
open Complexity.SAT
open ActualThreeSatToEncodeInput
open ActualThreeSatCmmsaReduce
open ActualThreeSatGraphYes
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Unary `1^v` to little-endian `v.bits`, via a width-`v+1` counter. -/
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

theorem unaryBitsFn_eq (v : Nat) :
    unaryBitsFn (List.replicate v true) = v.bits := by
  have hlt : v < 2 ^ (v + 1) :=
    lt_trans (Nat.lt_succ_self v) (Nat.lt_two_pow_self (n := v + 1))
  unfold unaryBitsFn
  simp only [List.length_replicate]
  rw [stripFn_eq, pairSnd_pair, coinStr_eq hlt, stripTrailing_eq_bits,
    binValLE_bitsOfLenLE _ _ hlt]

/-- `Tree.encode` of `.var` whose index is the unary value of `z`. -/
def varTreeEnc (z : List Bool) : List Bool :=
  [true, false] ++ encodeDigitsFn (unaryBitsFn z)

theorem varTreeEnc_mem_FP : varTreeEnc ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP (constFn_mem_FP [true, false])
    (mem_FP_comp unaryBitsFn_mem_FP encodeDigitsFn_mem_FP)

theorem varTreeEnc_eq (v : Nat) :
    varTreeEnc (List.replicate v true) =
      CMMSACodec.Tree.encode
        (formulaTree (Formula.var (⟨v, Nat.lt_succ_self v⟩ : Fin (v + 1)))) := by
  unfold varTreeEnc formulaTree natTree
  rw [unaryBitsFn_eq, encodeDigitsFn_eq, encodeDigits_eq]
  simp [CMMSACodec.Tree.encode]

/-- `Tree.encode` of `.or p q` from the encodings of `p` and `q`. -/
def orTreeEnc (p q : List Bool) : List Bool :=
  [true, true, false, true, false, false, true] ++ p ++ q

private theorem orTreeEnc_eq_encode {N : Nat} (p q : Formula (Fin N)) :
    orTreeEnc (CMMSACodec.Tree.encode (formulaTree p))
      (CMMSACodec.Tree.encode (formulaTree q)) =
      CMMSACodec.Tree.encode (formulaTree (.or p q)) := by
  simp [orTreeEnc, formulaTree, CMMSACodec.Tree.encode]

def litArgFn (j p : Nat) (z : List Bool) : List Bool :=
  pair (pair (List.replicate j true) (List.replicate p true)) z

theorem litArgFn_mem_FP (j p : Nat) : litArgFn j p ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP
    (constFn_mem_FP (pair (List.replicate j true) (List.replicate p true)))
    id_mem_FP

def clauseLitVarFn (j p : Nat) (z : List Bool) : List Bool :=
  litVarFn (litArgFn j p z)

def clauseVarTreeFn (j p : Nat) (z : List Bool) : List Bool :=
  varTreeEnc (clauseLitVarFn j p z)

/-- 3-OR of the three variable indices of clause 0.  Sign/polarity is not
applied; this matches `satUnit` (all-positive `x₀`).  `mem_FP` of this
map is the thin `slotVar` extractor, not this eta form. -/
def clauseOrEnc (z : List Bool) : List Bool :=
  orTreeEnc
    (orTreeEnc (clauseVarTreeFn 0 0 z) (clauseVarTreeFn 0 1 z))
    (clauseVarTreeFn 0 2 z)

theorem clauseLitVarFn_satUnit (p : Nat) (hp : p < 3) :
    clauseLitVarFn 0 p satUnit.encode = ([] : List Bool) := by
  have hj : 0 < satUnit.length := satUnit_len
  have hlen : (satUnit[0]'hj).length = 3 :=
    satUnit_is3 (satUnit[0]'hj) (List.get_mem _ _)
  have hp' : p < (satUnit[0]'hj).length := by omega
  unfold clauseLitVarFn litArgFn
  rw [litVarFn_encode satUnit hj hp']
  have hvar : ((satUnit[0]'hj)[p]'hp').var = 0 := by
    revert hp'
    simp [satUnit]
    intro hp'
    match p with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  simp [hvar]

private theorem varTreeEnc_zero :
    varTreeEnc [] =
      CMMSACodec.Tree.encode
        (formulaTree (Formula.var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1))) :=
  varTreeEnc_eq 0

theorem clauseOrEnc_satUnit :
    clauseOrEnc satUnit.encode =
      CMMSACodec.Tree.encode
        (formulaTree
          (or3 (Formula.var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1))
            (Formula.var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1))
            (Formula.var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)))) := by
  unfold clauseOrEnc clauseVarTreeFn
  rw [clauseLitVarFn_satUnit 0 (by decide), clauseLitVarFn_satUnit 1 (by decide),
    clauseLitVarFn_satUnit 2 (by decide)]
  rw [varTreeEnc_zero]
  simp only [or3]
  rw [orTreeEnc_eq_encode, orTreeEnc_eq_encode]

theorem clauseOrEnc_ne_id : clauseOrEnc [] ≠ [] := by
  intro hz
  have hlen := congrArg List.length hz
  simp [clauseOrEnc, orTreeEnc] at hlen

end
end PvNP.RealizableHardness.ActualThreeSatCompileFp
