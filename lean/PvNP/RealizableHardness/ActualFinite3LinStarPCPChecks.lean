import PvNP.RealizableHardness.ActualFinite3LinStarPCP

/-!
Checks for Finite3LinSource star-PCP compilation.
Tiny examples first; axiom prints after. Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualFinite3LinStarPCPChecks

open PvNP.RealizableHardness.ActualFinite3LinStarPCP
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness
open Finite3LinSource

#check unsatPair
#check unsatPair_unsat
#check rowFormula
#check rowFormula_leaves
#check linStarData_valid
#check hn_zeta_threshold
#check finite3LinStarEncodeFn_mem_FP
#check Finite3LinSource.ofActual

example : alph 2 = 16 := rfl

example : Formula.leaves (rowFormula (by decide : 0 < 2) 0) = 48 :=
  rowFormula_leaves (by decide : 0 < 2) 0

example (x : Fin 3 → ZMod 2) : 0 < unsatPair.violations x :=
  unsatPair_unsat x

#print axioms unsatPair_unsat
#print axioms rowFormula_leaves
#print axioms linStarData_valid
#print axioms hn_zeta_threshold
#print axioms finite3LinStarEncodeFn_mem_FP

end PvNP.RealizableHardness.ActualFinite3LinStarPCPChecks
