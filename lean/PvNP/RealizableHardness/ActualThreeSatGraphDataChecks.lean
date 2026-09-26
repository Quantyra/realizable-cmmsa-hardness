import PvNP.RealizableHardness.ActualThreeSatGraphData

/-!
Checks for the 3SAT-dependent `toGraph` CMMSA packing.
Tiny examples first; axiom prints after.

Packed formulas depend on the source 3CNF.  Satisfiable 3CNF has a proper
`toGraph` labeling; unsatisfiable 3CNF has none.  This is not a
tautology-row encoder, not identity, and not LeafFold/`unsatCnf`.  It
does not inhabit `hSrcCmmsa` and does not assert `No sigma_L gamma_L` or
unconditional Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGraphDataChecks

open PvNP.RealizableHardness.ActualThreeSatGraphData
open PvNP.RealizableHardness.ActualHeadlineParameters
open Complexity.SAT
open Complexity.ThreeSATCSP
open CMMSACodec hiding Tree

#check encode3
#check decode3
#check decode3_encode3
#check graphFormulas
#check graphData
#check graphData_valid
#check paramGraphData
#check paramGraphData_valid
#check honestBits
#check honestBits_coord
#check toGraph_satisfies_vertexLabel
#check packed_formula_count
#check threeSatToGraphBits
#check threeSatToGraphBits_decode
#check threeSatToGraphBits_ne_id
#check graph_unsat_of_unsat

example : alph8 = 8 := rfl

example (a : Fin 3 → Bool) : decode3 (encode3 a) = a :=
  decode3_encode3 a

example {L : Nat} (h : 256 ≤ mOf L) : 128 ≤ L :=
  one_twenty_eight_le_L h

#print axioms decode3_encode3
#print axioms graphData_valid
#print axioms paramGraphData_valid
#print axioms toGraph_satisfies_vertexLabel
#print axioms packed_formula_count
#print axioms threeSatToGraphBits_decode
#print axioms threeSatToGraphBits_ne_id
#print axioms graph_unsat_of_unsat

end PvNP.RealizableHardness.ActualThreeSatGraphDataChecks
