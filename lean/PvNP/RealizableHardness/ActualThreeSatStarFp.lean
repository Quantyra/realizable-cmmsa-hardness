import PvNP.RealizableHardness.ActualThreeSatCompileDataFp
import PvNP.RealizableHardness.ActualHeadlineParameters
import PvNP.RealizableHardness.ActualCompactStarCompile

/-!
Grassmann-alphabet `encodeData` layout of a 1-clause polarity-OR at
alphabet `ROf L`, as a `List Bool → List Bool` in `Complexity.FP`.

`starEncFn L` writes `dataTree` of `2 * ROf L` copies of weight
`1/(2 * ROf L)`, the clause-0 3-OR formula from `clauseOrEnc`, and
budget `1/ROf L`.  That is the `starData` / `paramStarData` layout of a
1-variable 1-clause 3CNF (`unit3` / `satUnit`) at manuscript alphabet
`ROf L`.  3SAT data is in the formula tree, not a trailing remainder.

Not `No σ_L γ_L` on unsat (polarity-OR / live label 0 is cheap).  Not
`if-sat`.  Does not inhabit `hSrcCmmsa`.  Does not import the
selected-map / `encodeInput` stack.  Checking-transducer `mem_FP` is
not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarFp

open Complexity
open ActualThreeSatCompileDataFp
open ActualThreeSatClauseOrFp
open ActualHeadlineParameters
open ActualCompactStarCompile
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def grassDen (L : Nat) : Nat := 2 * ROf L

def grassWeightRat (L : Nat) : Rat :=
  (1 : Rat) / (grassDen L : Rat)

def grassBudgetRat (L : Nat) : Rat :=
  (1 : Rat) / (ROf L : Rat)

def grassWeightEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree (grassWeightRat L))

def grassBudgetEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode (ratTree (grassBudgetRat L))

/-- `Tree.encode` of `listTree` of `2 * ROf L` copies of weight `1/(2 ROf L)`. -/
def grassWeightsEnc (L : Nat) : List Bool :=
  CMMSACodec.Tree.encode
    (listTree (List.replicate (grassDen L) (ratTree (grassWeightRat L))))

theorem grassWeightsEnc_eq (L : Nat) :
    grassWeightsEnc L =
      CMMSACodec.Tree.encode
        (listTree (List.replicate (grassDen L) (ratTree (grassWeightRat L)))) :=
  rfl

/-- `encodeData` of the Grassmann 2-polarity, 1-formula, budget-`1/ROf`
`paramStarData` layout of a 1-clause 3CNF. -/
def starEncFn (L : Nat) (z : List Bool) : List Bool :=
  true :: grassWeightsEnc L ++ true :: formulasListEnc z ++ grassBudgetEnc L

theorem starEncFn_mem_FP (L : Nat) : starEncFn L ∈ Complexity.FP := by
  have hforms : (fun z => true :: formulasListEnc z) ∈ Complexity.FP :=
    mem_FP_comp formulasListEnc_mem_FP (Cobham.cons_mem_FP true)
  have hleft : (fun z => true :: grassWeightsEnc L ++ true :: formulasListEnc z) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: grassWeightsEnc L)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP (grassBudgetEnc L))

theorem starEncFn_eq_dataTree (L : Nat) (z : List Bool) (t : CMMSACodec.Tree)
    (ht : clauseOrEnc z = CMMSACodec.Tree.encode t) :
    starEncFn L z =
      CMMSACodec.Tree.encode
        (.node (listTree (List.replicate (grassDen L) (ratTree (grassWeightRat L))))
          (.node (listTree [t]) (ratTree (grassBudgetRat L)))) := by
  rw [starEncFn, grassWeightsEnc_eq, formulasListEnc_eq z t ht, grassBudgetEnc]
  simp [CMMSACodec.Tree.encode]

theorem starEncFn_ne_id (L : Nat) : starEncFn L [] ≠ [] := by
  simp [starEncFn]

end
end PvNP.RealizableHardness.ActualThreeSatStarFp
