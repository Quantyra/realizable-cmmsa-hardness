import Complexitylib.Classes.PCP.Internal.CNFMaxVar

/-!
Thin Cobham surface for a 3SAT-clause literal variable, using the already
certified `slotVar ∈ FP` (complexitylib), not a fresh `mem_FP_comp` of
`litVarFn_mem_FP`.

`slotVar` reads the variable of slot `i = 3j+p` (clause `j`, position `p`).
That is the same extractor as `litVarFn` on `pair (pair 1^j 1^p) z`.

Does not pack `encodeData`, prove `Yes 0` / `No σ_L γ_L`, or inhabit
`hSrcCmmsa`.  Checking-transducer `mem_FP` is not rebuilt.
-/
namespace PvNP.RealizableHardness.ActualThreeSatLitVarFp

open Complexity
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

def slotArgFn (j p : Nat) (z : List Bool) : List Bool :=
  pair z (List.replicate (3 * j + p) true)

theorem slotArgFn_mem_FP (j p : Nat) : slotArgFn j p ∈ Complexity.FP :=
  Cobham.pairFn_mem_FP id_mem_FP
    (constFn_mem_FP (List.replicate (3 * j + p) true))

/-- Variable of clause `j`, position `p`, as unary `1^v`.
Defined as `slotVar ∘ slotArgFn` so `mem_FP_comp` matches without eta. -/
def clauseLitVarFn (j p : Nat) : List Bool → List Bool :=
  slotVar ∘ slotArgFn j p

theorem clauseLitVarFn_mem_FP (j p : Nat) :
    clauseLitVarFn j p ∈ Complexity.FP :=
  mem_FP_comp (slotArgFn_mem_FP j p) slotVar_mem_FP

end
end PvNP.RealizableHardness.ActualThreeSatLitVarFp
