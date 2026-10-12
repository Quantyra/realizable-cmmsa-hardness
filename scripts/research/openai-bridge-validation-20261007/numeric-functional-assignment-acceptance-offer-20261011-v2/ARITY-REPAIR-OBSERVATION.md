# Arity repair observation

Source basis: captured `numeric-functional-assignment-acceptance-capture-v1/ActualFunctionalAssignmentAcceptance.lean`, SHA256 `52106CF7B184E2A25F2729D840758CC42C3D148B9C4BA44005D45AB536C65340`. V1 is immutable and was not edited.

V2 changes only positional arguments at local call sites. The file section binder declares `{J : Nat}` implicit. The local functions and lemmas `retainedUnit`, `retainedUnitIn`, `retainedAssignment`, `actualRetainedToVisible`, `retainedSupport_property`, `retainedVector_eq_sum_units`, and `retained_functional_eval_eq_sum` therefore do not accept J positionally. V2 removes that argument from their call sites. The imported functions `retainedVariables` and `actualRetained_map_visible` still take J explicitly, and those calls are unchanged. There are no blanket replacements and no proof or statement changes.

The captured v1 diagnostic did not compile the source; this defect was found by static declaration-arity inspection. No native Lean diagnostic is available for v1 or v2. The original module source and all captured files remain preserved; v2 is a separate candidate, not a repair to the immutable capture.

V1 source SHA256: `52106CF7B184E2A25F2729D840758CC42C3D148B9C4BA44005D45AB536C65340`.