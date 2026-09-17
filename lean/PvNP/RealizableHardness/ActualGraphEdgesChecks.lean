import PvNP.RealizableHardness.ActualGraphEdges

namespace PvNP.RealizableHardness.ActualGraphEdgesChecks
open ActualGraphEdges

#print axioms reverse_reverse
#print axioms reverse_injective
#print axioms rank_injective
#print axioms rep_nonloop
#print axioms rep_reverse_excluded
#print axioms exactly_one
#print axioms canonical_rep
#print axioms canonical_reverse
#print axioms rep_orbit_unique
#print axioms dartList_nodup
#print axioms dartList_eq_table_sources
#print axioms edge_terminals_distinct
#print axioms loop_never_crosses
#print axioms representativeList_nodup
#print axioms representativeList_toFinset
#print axioms representativeList_length
#print axioms representative_count_bound
#print axioms canonical_crossing
#print axioms orient_canonical
#print axioms crossing_card_eq_outgoing
#print axioms outgoing_eq_actual_darts
#print axioms crossing_card_eq_cut
#print axioms crossing_expansion
#print axioms zero_representatives
#print axioms zero_list

#check dartList_eq_table_sources
#check rep_orbit_unique
#check crossing_card_eq_cut

example : representativeList 0 = [] := zero_list
example : representatives 0 = ∅ := zero_representatives
example {n : Nat} (e : Edge n) : e.val.1 ≠ (reverse e.val).1 := edge_terminals_distinct e
example {n : Nat} (d : Dart n) (h : d.1 = (reverse d).1) : ¬ IsRep d :=
  fun hr => rep_nonloop hr h
example {n : Nat} (d : Dart n) (h : Nonloop d) :
    IsRep d ∨ IsRep (reverse d) := (exactly_one h).1
example {n : Nat} {a b : Dart n} (ha : IsRep a) (hb : IsRep b)
    (h : a ≠ b) : a ≠ reverse b := fun he => h (rep_orbit_unique ha hb (Or.inr he))
example (n : Nat) : 2 * (representatives n).card ≤ 3 * n * FixedPortCycleFamily.degree :=
  representative_count_bound n
example (n : Nat) (S : Vertex n → Bool) :
    ((crossing n S).card : Real) = FixedPortCycleFamily.cut n S := crossing_card_eq_cut n S

end PvNP.RealizableHardness.ActualGraphEdgesChecks
