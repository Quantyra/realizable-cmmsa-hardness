import PvNP.RealizableHardness.ActualOccurrenceCounts

/-! Source-only explicit completeness extension for the actual whole-instance rows.
This proves exact preservation of violation counts, not source hardness or runtime. -/
namespace PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance
open scoped BigOperators
set_option autoImplicit false
noncomputable section
variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)

def sourceBadRow (y : Fin N → ZMod 2) (r : Fin m) : Bool :=
  decide (¬ (y (I.vars r 0) + y (I.vars r 1) + y (I.vars r 2) = I.rhs r))

/-- The original ordered source equation occurrences, with their stored right-hand sides. -/
def sourceViolations (y : Fin N → ZMod 2) : Nat :=
  (List.finRange m).countP (I.sourceBadRow y)

/-- Constant owner values on every cloud port; internals use the actual cloud extension. -/
def sourceExtension (y : Fin N → ZMod 2) : I.GlobalVar → ZMod 2
  | ⟨v,q⟩ => ActualEqualityCloud.extension (fun _ => y v) q

theorem sourceExtension_port (y : Fin N → ZMod 2) (v : Fin N)
    (p : ActualGraphEdges.Vertex (I.size v)) :
    I.sourceExtension y ⟨v, Sum.inl p⟩ = y v := rfl

theorem sourceExtension_anchor (y : Fin N → ZMod 2) (o : ActualOccurrenceAllocation.Slot m) :
    I.sourceExtension y (I.anchor o) = y (I.owner o) := rfl

theorem sourceExtension_original_value (y : Fin N → ZMod 2) (r : Fin m) (i : Fin 3) :
    I.sourceExtension y (I.originalRow r i) = y (I.vars r i) := rfl

theorem sourceExtension_original_bad (y : Fin N → ZMod 2) (r : Fin m) :
    I.badRow (I.sourceExtension y) (I.originalRow r, I.rhs r) = I.sourceBadRow y r := by
  simp only [badRow, sourceBadRow, I.sourceExtension_original_value]
  rfl

theorem sourceExtension_original_violations (y : Fin N → ZMod 2) :
    I.originalViolations (I.sourceExtension y) = I.sourceViolations y := by
  unfold originalViolations originalRows sourceViolations
  rw [List.ofFn_eq_map, List.countP_map]
  apply congrArg (fun p => (List.finRange m).countP p)
  funext r
  exact I.sourceExtension_original_bad y r

/-- The single global function restricts to the intended extension in every cloud. -/
theorem sourceExtension_restrict (y : Fin N → ZMod 2) (v : Fin N) :
    I.restrictCloud (I.sourceExtension y) v =
      ActualEqualityCloud.extension (fun _ : ActualGraphEdges.Vertex (I.size v) => y v) := rfl

theorem sourceExtension_cloud_zero (y : Fin N → ZMod 2) (v : Fin N) :
    ActualEqualityCloud.rowsViolations (I.restrictCloud (I.sourceExtension y) v) = 0 := by
  rw [I.sourceExtension_restrict, ActualEqualityCloud.rowsViolations_eq_total,
    ActualEqualityCloud.extension_total]
  simp [EqualityGadget.mismatch]

theorem sourceExtension_tagged_cloud_zero (y : Fin N → ZMod 2) (v : Fin N) :
    ((ActualEqualityCloud.rows (I.size v)).map (I.tagRow v)).countP
      (I.badRow (I.sourceExtension y)) = 0 := by
  rw [I.taggedCloud_violations, I.sourceExtension_cloud_zero]

/-- Exact whole-instance count on the actual generated output, for every source assignment. -/
theorem sourceExtension_violations (y : Fin N → ZMod 2) :
    I.violations (I.sourceExtension y) = I.sourceViolations y := by
  rw [I.violations_eq_original_add_clouds, I.sourceExtension_original_violations]
  simp_rw [I.sourceExtension_cloud_zero]
  simp

theorem sourceExtension_filter_length (y : Fin N → ZMod 2) :
    (I.rows.filter (I.badRow (I.sourceExtension y))).length =
      ((List.finRange m).filter (I.sourceBadRow y)).length := by
  rw [← I.violations_eq_filter_length, I.sourceExtension_violations]
  exact List.countP_eq_length_filter

theorem sourceExtension_satisfied (y : Fin N → ZMod 2) (h : I.sourceViolations y = 0) :
    I.violations (I.sourceExtension y) = 0 := by rw [I.sourceExtension_violations, h]

theorem sourceExtension_count_bound (y : Fin N → ZMod 2) (k : Nat)
    (h : I.sourceViolations y ≤ k) : I.violations (I.sourceExtension y) ≤ k := by
  rw [I.sourceExtension_violations]
  exact h

theorem sourceViolations_zero (J : ActualOccurrenceAllocation.Instance N 0)
    (y : Fin N → ZMod 2) : J.sourceViolations y = 0 := by
  simp [sourceViolations]

theorem sourceExtension_empty (J : ActualOccurrenceAllocation.Instance N 0)
    (y : Fin N → ZMod 2) : J.violations (J.sourceExtension y) = 0 := by
  rw [J.sourceExtension_violations, J.sourceViolations_zero]

end
end PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance
