import PvNP.RealizableHardness.ActualThreeSatGrassmannRes
import PvNP.RealizableHardness.ActualThreeSatClauseOrFp

/-!
Uniform `Complexity.FP` encoder of the m-ary Grassmann `compileRes`
layout (`k = 1`, alphabet `ROf L`, `paramN L` vertices).  The formula
list is one restriction star plus the clause-0 3SAT-dependent 3-OR
(`clauseOrEnc`), so 3SAT data is in the tree.  Not XOR-star, not
`if-sat`.

The restriction star is satisfied by monochromatic label-0, so the
decoded instance is `Yes 0` whenever the 3-OR is also true on that
1-hot (e.g. the 3-OR mentions only label-0 coordinates).  This is not
a `No` map and does not inhabit `hSrcCmmsa`.  Checking-transducer
`mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGrassmannResFp

open Complexity
open ActualThreeSatGrassmannRes
open ActualThreeSatClauseOrFp
open ActualHeadlineParameters
open ActualBitRestriction
open ActualCompactStarCompile
open ActualRestrictCompile
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def resWeightRat (L : Nat) : Rat :=
  (1 : Rat) / ((paramN L * ROf L : Nat) : Rat)

def resBudgetRat (L : Nat) : Rat :=
  (1 : Rat) / (ROf L : Rat)

def resWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (paramN L * ROf L) (ratTree (resWeightRat L))))

def resBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree (resBudgetRat L))

def resFormulaTree {L : Nat} (hh : 0 < resH L) : CMMSACodec.Tree :=
  formulaTree
    (compileRes (resK_le hh) (paramCenter L) (paramLeaf L))

def resFormulaEnc {L : Nat} (hh : 0 < resH L) : List Bool :=
  CMMSACodec.Tree.encode (resFormulaTree hh)

/-- Two-formula list: Grassmann restriction star, then clause-0 3-OR. -/
def resFormsEnc {L : Nat} (hh : 0 < resH L) (z : List Bool) : List Bool :=
  true :: resFormulaEnc hh ++ (true :: clauseOrEnc z ++ [false])

theorem resFormsEnc_mem_FP {L : Nat} (hh : 0 < resH L) :
    resFormsEnc (L := L) hh ∈ Complexity.FP := by
  have htail : (fun z : List Bool => true :: clauseOrEnc z ++ [false]) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP
      (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
      (constFn_mem_FP [false])
  exact Cobham.appendFn_mem_FP
    (constFn_mem_FP (true :: resFormulaEnc hh)) htail

/-- Uniform Grassmann-restriction encoder with 3SAT data in the second
formula. -/
def resEncFn {L : Nat} (hh : 0 < resH L) (z : List Bool) : List Bool :=
  true :: resWeightsEnc L ++ true :: resFormsEnc hh z ++ resBudgetEnc L

theorem resEncFn_mem_FP {L : Nat} (hh : 0 < resH L) :
    resEncFn (L := L) hh ∈ Complexity.FP := by
  have hforms : (fun z => true :: resFormsEnc hh z) ∈ Complexity.FP :=
    mem_FP_comp (resFormsEnc_mem_FP hh) (Cobham.cons_mem_FP true)
  have hleft : (fun z => true :: resWeightsEnc L ++ true :: resFormsEnc hh z) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: resWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (resBudgetEnc L))

theorem resEncFn_ne_id {L : Nat} (hh : 0 < resH L) :
    resEncFn (L := L) hh [] ≠ [] := by
  simp [resEncFn, resWeightsEnc, CMMSACodec.Tree.encode]

end
end PvNP.RealizableHardness.ActualThreeSatGrassmannResFp
