import PvNP.RealizableHardness.ActualThreeSatClauseOrFp

/-!
Thin `encodeData` layout of `compileData` (2 polarities, one clause-0
formula) as a `List Bool → List Bool` in `Complexity.FP`.

`encodeCompileFn` writes `dataTree` of two weight-`1/2` coordinates, the
clause-0 3-OR formula from `clauseOrEnc`, and budget `1`.  That is the
`indexedData` / `compileData` layout of a 1-clause 1-variable 3CNF
(`satUnit`).  3SAT data is in the formula tree, not a trailing remainder.

Not `No σ_L γ_L` on unsat (polarity-OR / 2-live-label).  Not `if-sat`.
Does not inhabit `hSrcCmmsa`.  Does not import the selected-map /
`encodeInput` stack.  Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCompileDataFp

open Complexity
open ActualThreeSatClauseOrFp
open CMMSACodec hiding Tree
open CMMSAEncoding
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def halfRatEnc : List Bool :=
  CMMSACodec.Tree.encode (ratTree ((1 : Rat) / 2))

def oneRatEnc : List Bool :=
  CMMSACodec.Tree.encode (ratTree 1)

/-- `Tree.encode` of `listTree [ratTree (1/2), ratTree (1/2)]`. -/
def twoHalvesEnc : List Bool :=
  true :: halfRatEnc ++ true :: halfRatEnc ++ [false]

theorem twoHalvesEnc_eq :
    twoHalvesEnc =
      CMMSACodec.Tree.encode
        (listTree [ratTree ((1 : Rat) / 2), ratTree ((1 : Rat) / 2)]) := by
  simp [twoHalvesEnc, halfRatEnc, listTree, CMMSACodec.Tree.encode]

/-- `Tree.encode` of `listTree` of the single clause-0 3-OR. -/
def formulasListEnc (z : List Bool) : List Bool :=
  true :: clauseOrEnc z ++ [false]

theorem formulasListEnc_mem_FP : formulasListEnc ∈ Complexity.FP :=
  Cobham.appendFn_mem_FP
    (mem_FP_comp clauseOrEnc_mem_FP (Cobham.cons_mem_FP true))
    (constFn_mem_FP [false])

theorem formulasListEnc_eq (z : List Bool) (t : CMMSACodec.Tree)
    (ht : clauseOrEnc z = CMMSACodec.Tree.encode t) :
    formulasListEnc z = CMMSACodec.Tree.encode (listTree [t]) := by
  simp [formulasListEnc, listTree, CMMSACodec.Tree.encode, ht]

/-- `encodeData` of the 2-weight, 1-formula, budget-1 `compileData` layout. -/
def encodeCompileFn (z : List Bool) : List Bool :=
  true :: twoHalvesEnc ++ true :: formulasListEnc z ++ oneRatEnc

theorem encodeCompileFn_mem_FP : encodeCompileFn ∈ Complexity.FP := by
  have hforms : (fun z => true :: formulasListEnc z) ∈ Complexity.FP :=
    mem_FP_comp formulasListEnc_mem_FP (Cobham.cons_mem_FP true)
  have hleft : (fun z => true :: twoHalvesEnc ++ true :: formulasListEnc z) ∈
      Complexity.FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: twoHalvesEnc)) hforms
  exact Cobham.appendFn_mem_FP hleft (constFn_mem_FP oneRatEnc)

theorem encodeCompileFn_eq_dataTree (z : List Bool) (t : CMMSACodec.Tree)
    (ht : clauseOrEnc z = CMMSACodec.Tree.encode t) :
    encodeCompileFn z =
      CMMSACodec.Tree.encode
        (.node (listTree [ratTree ((1 : Rat) / 2), ratTree ((1 : Rat) / 2)])
          (.node (listTree [t]) (ratTree 1))) := by
  rw [encodeCompileFn, twoHalvesEnc_eq, formulasListEnc_eq z t ht, oneRatEnc]
  simp [CMMSACodec.Tree.encode]

theorem encodeCompileFn_ne_id : encodeCompileFn [] ≠ [] := by
  simp [encodeCompileFn]

end
end PvNP.RealizableHardness.ActualThreeSatCompileDataFp
