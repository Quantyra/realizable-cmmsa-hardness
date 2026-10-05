Authored patch below. It is uncompiled; I did not edit files, run Lean/Lake/elan, use GCP, or mutate Git. **Ready for Sol application and GCP capture; this is not an acceptance claim.** If later certified, this is helper increment 2; the three-helper threshold remains uncrossed. The accepted helper count remains 1.

```diff
--- a/lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean
+++ b/lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean
@@
 open PvNP.RealizableHardness.BinaryMatrixFourier
 open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
+open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
+open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
 
 noncomputable section
 set_option autoImplicit false
@@
   rw [hfilter]
   rfl
 
+/-- The A9 ambient quotient map is the composite of output-coordinate transport
+and the nested-domain quotient equivalence. -/
+theorem a8_w6_domain_quotient_square
+    {d i : Nat}
+    (A : Submodule F (V d))
+    (A0 : A9AmbientA0 (V d) A i) :
+    let u := (domainBasis A0.1).equivFun
+    let C0 := A.map A0.1.mkQ
+    let C := C0.map u.toLinearMap
+    let hC : C.map u.symm.toLinearMap = C0 := by
+      dsimp only [C]
+      rw [← Submodule.map_comp]
+      simp only [LinearEquiv.symm_comp, Submodule.map_id]
+    let eD :=
+      (Submodule.Quotient.equiv C C0 u.symm hC).trans
+        (nestedDomainEquiv A0.1 A A0.2.1)
+    eD.toLinearMap.comp (C.mkQ.comp u.toLinearMap) =
+      a9AmbientQuotientMap A A0 := by
+  dsimp only
+  apply LinearMap.ext
+  intro x
+  rcases A0.1.mkQ_surjective x with ⟨v, rfl⟩
+  change
+    (Submodule.quotientQuotientEquivQuotient A0.1 A A0.2.1)
+      ((A.map A0.1.mkQ).mkQ
+        ((domainBasis A0.1).equivFun.symm
+          ((domainBasis A0.1).equivFun (A0.1.mkQ v)))) =
+      A.mkQ v
+  rw [LinearEquiv.symm_apply_apply]
+  exact
+    Submodule.quotientQuotientEquivQuotientAux_mk_mk
+      A0.1 A A0.2.1 v
+
 /-- The complete normalized mean is transported by the nested carrier equivalence. -/
 theorem a8_carrier_coordinate_nested_mean {n d : Nat}
@@
--- a/lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransportChecks.lean
+++ b/lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransportChecks.lean
@@
 #check a8_output_coordinate_eq
 #print axioms a8_output_coordinate_eq
+#check a8_w6_domain_quotient_square
+#print axioms a8_w6_domain_quotient_square
 #check a8_output_pair_component_nested_mean
 #print axioms a8_output_pair_component_nested_mean
```