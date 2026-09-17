import PvNP.RealizableHardness.ActualOccurrenceCounts

namespace PvNP.RealizableHardness.ActualOccurrenceCountsChecks
open ActualOccurrenceCounts ActualOccurrenceAllocation ActualOccurrenceAllocation.Instance
open scoped BigOperators

#print axioms cloudIndices_nodup
#print axioms cloud_rows_eq_map
#print axioms gadgetIndices_nodup
#print axioms rowIndices_nodup
#print axioms mem_rowIndices
#print axioms rowIndices_toFinset
#print axioms rows_eq_map
#print axioms rowPair_injective
#print axioms rows_nodup
#print axioms rows_length
#print axioms rows_length_ge
#print axioms edge_count_bound
#print axioms rows_length_le
#print axioms rows_length_pos
#print axioms badRow_tag
#print axioms taggedCloud_violations
#print axioms violations_eq_original_add_clouds
#print axioms violations_eq_filter_length
#print axioms violations_eq_index_sum
#print axioms zero_violations
#print axioms unused_cloud_violations

#check rows_eq_map
#check rows_length
#check violations_eq_original_add_clouds
#check violations_eq_index_sum

example {N m : Nat} (I : Instance N m) : I.rows.Nodup := I.rows_nodup
example {N m : Nat} (I : Instance N m) : I.rows.length = m + 4 * I.edgeCount := I.rows_length
example {N m : Nat} (I : Instance N m) : m ≤ I.rows.length := I.rows_length_ge
example {N m : Nat} (I : Instance N m) :
    I.rows.length ≤ (1 + 18 * FixedPortCycleFamily.degree) * m := I.rows_length_le
example {N m : Nat} (I : Instance N m) (hm : 0 < m) : 0 < I.rows.length := I.rows_length_pos hm
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar → ZMod 2) :
    I.violations x = (I.rows.filter (I.badRow x)).length := I.violations_eq_filter_length x
example {N : Nat} (I : Instance N 0) (x : I.GlobalVar → ZMod 2) : I.violations x = 0 :=
  I.zero_violations x
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar → ZMod 2)
    (v : Fin N) (h : I.size v = 0) :
    ActualEqualityCloud.rowsViolations (I.restrictCloud x v) = 0 := I.unused_cloud_violations x v h

end PvNP.RealizableHardness.ActualOccurrenceCountsChecks
