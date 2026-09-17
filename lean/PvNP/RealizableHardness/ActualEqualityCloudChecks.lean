import PvNP.RealizableHardness.ActualEqualityCloud

namespace PvNP.RealizableHardness.ActualEqualityCloudChecks
open ActualGraphEdges ActualEqualityCloud

#print axioms embedFn_injective
#print axioms internal_identity
#print axioms internal_not_port
#print axioms mem_edgeList
#print axioms edgeList_nodup
#print axioms edgeList_toFinset
#print axioms edgeList_length
#print axioms localRows_eq
#print axioms row_mem_rows
#print axioms row_injective
#print axioms support_eq
#print axioms support_card
#print axioms local_terminal_unique
#print axioms shared_implies_terminals
#print axioms shared_member_terminal
#print axioms cross_copy_intersection
#print axioms pair_intersection
#print axioms support_injective
#print axioms extension_ports
#print axioms extension_pullback
#print axioms localViolations_eq
#print axioms local_lower
#print axioms extension_attains
#print axioms extension_total
#print axioms localRows_violations
#print axioms rowsViolations_eq_total
#print axioms total_eq_filter_length
#print axioms extension_rows
#print axioms rows_lower
#print axioms exact_minimum
#print axioms rows_zero

#check extension_pullback
#check cross_copy_intersection
#check extension_total
#check extension_rows
#check exact_minimum

example : rows 0 = [] := rows_zero
example {n : Nat} (e : Edge n) (i : Fin 5) (p : Vertex n) :
    (Sum.inr (e,i) : GlobalVar n) ≠ Sum.inl p := internal_not_port e i p
example {n : Nat} (e f : Edge n) (h : e ≠ f) (i j : Fin 5) :
    (Sum.inr (e,i) : GlobalVar n) ≠ Sum.inr (f,j) :=
  fun he => h ((internal_identity e f i j).mp he).1
/-- Even copies with the same endpoints retain the cross-copy bound. -/
example {n : Nat} (e f : Edge n) (h : e ≠ f)
    (_ : e.val.1 = f.val.1) (_ : (reverse e.val).1 = (reverse f.val).1)
    (r s : EqualityGadget.Row) :
    (support (e,r) ∩ support (f,s)).card ≤ 1 := cross_copy_intersection e f h r s
example {n : Nat} (x : Vertex n → ZMod 2) (e : Edge n) :
    extension x ∘ embedding e = EqualityGadget.extension (x e.val.1) (x (reverse e.val).1) :=
  extension_pullback x e
example {n : Nat} (x : Vertex n → ZMod 2) (e : Edge n) :
    localViolations (extension x) e = EqualityGadget.mismatch (x e.val.1) (x (reverse e.val).1) :=
  extension_attains x e
example {n : Nat} (q : RowId n) : (support q).card = 3 := support_card q
example {n : Nat} (e : Edge n) (r : EqualityGadget.Row) :
    (row (e,r), rhs (e,r)) ∈ rows n := row_mem_rows e r
example {n : Nat} (x : GlobalVar n → ZMod 2) :
    totalViolations x = ((rows n).filter (badRow x)).length := total_eq_filter_length x

end PvNP.RealizableHardness.ActualEqualityCloudChecks
