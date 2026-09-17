import PvNP.RealizableHardness.ExecutablePortRotation
/-! SOURCE ONLY: no profile, example or machine evaluation has been run. -/
open PvNP.RealizableHardness ExecutablePortRotation

#print axioms fitLevel_bound
#print axioms externalOutput_mem_FP
#print axioms shiftedOutput_mem_FP
#print axioms rotationFn_mem_FP
#print axioms ifEqLen_unary
#print axioms shiftedOutput_input
#print axioms rotationFn_on_input
#print axioms rotationFn_invalid_vertex
#print axioms rotationFn_invalid_index
#print axioms rotationFn_invalid_label
#print axioms rotationFn_zero_size
#print axioms external_agrees
#print axioms rotate_value
#print axioms rotate_symm_value
#print axioms rotationFn_agrees

set_option pp.fullNames true in
#check rotationFn_mem_FP
set_option pp.fullNames true in
#check rotationFn_agrees

example (v j i : Nat) : rotationFn (input 0 v j i) = [] := rotationFn_zero_size v j i
example (n v j : Nat) : rotationFn (input n v j 3) = [] :=
  rotationFn_invalid_label n v j 3 (by omega)
example (n v i : Nat) : rotationFn (input n v FixedPortCycleFamily.degree i) = [] :=
  rotationFn_invalid_index n v FixedPortCycleFamily.degree i (le_refl _)
example (n j i : Nat) : rotationFn (input n n j i) = [] :=
  rotationFn_invalid_vertex n n j i (le_refl _)
example : rotationFn ∈ Complexity.FP := rotationFn_mem_FP
example (n : Nat) : Complexity.algBase.fitLevel Complexity.one_lt_algBase_deg n ≤ 2*n := by
  simpa [levelBound] using fitLevel_bound n
example (n : Nat) (v : Fin n) (j : Fin (FixedPortCycleFamily.predecessor + 1)) :
    rotationFn (input n v.val j.val 0) =
      output (FixedPortCycleFamily.baseRotation n (v,j)).1.val
        (FixedPortCycleFamily.baseRotation n (v,j)).2.val 0 := by
  simpa [PortCycleReplacement.rotation] using rotationFn_agrees n v j (0 : Fin 3)
