import PvNP.RealizableHardness.PortCycleReplacement
/-! Uncompiled author checks. No kernel or axiom acceptance is claimed. -/
open PvNP.RealizableHardness.PortCycleReplacement

#print axioms rotation_involutive
#print axioms graph_degree
#print axioms graph_order
#print axioms cut_decomposition
#print axioms constant_of_adjacent
#print axioms minority_le_cycle
#print axioms discrepancy_le_cycles
#print axioms smallSide_transport
#print axioms external_transport
#print axioms cut_expansion
#print axioms table_length

set_option pp.fullNames true in
#check cut_expansion

example : distance true false = 1 := by norm_num [distance]
example : distance true true = 0 := by norm_num [distance]
example (b : Bool) : minority (fun _ : Fin 1 => b) = 0 := minority_constant b
example (b : Bool) : minority (fun _ : Fin 2 => b) = 0 := minority_constant b
example (s : Fin 1 → Bool) : cycle s = 0 := by
  simp [cycle, finRotate_one, distance]
example : rotation (n := 1) (d := 0) id (((0,0),1)) = (((0,0),2)) := by
  simp [rotation, finRotate_one]
example : rotation (n := 1) (d := 0) id (((0,0),2)) = (((0,0),1)) := by
  simp [rotation, finRotate_one]
example (R : Port 2 1 → Port 2 1) (hR : Function.Involutive R) :
    (graph R hR).deg = 3 := graph_degree R hR
example (R : Port 2 1 → Port 2 1) (hR : Function.Involutive R) :
    (graph R hR).order = 4 := by simpa using graph_order R hR
example (R : Port 0 2 → Port 0 2) : (table R).length = 0 := by simp
example (R : Port 2 1 → Port 2 1) : (table R).length = 12 := by simp
