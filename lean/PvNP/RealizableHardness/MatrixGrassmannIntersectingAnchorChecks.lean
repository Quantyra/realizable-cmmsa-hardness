import PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchor

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.MatrixGrassmannIntersectingAnchor
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

#check independent_concatenate_iff_intersection
#check span_concatenate_iff_intersection
#check internalHomFibreEquiv
#check card_homFibre
#check card_homFibre_GL
#check sum_hom_rankArrays
#check homogeneous_lift_density_le

#print axioms independent_concatenate_iff_intersection
#print axioms span_concatenate_iff_intersection
#print axioms card_homFibre
#print axioms homFibre_product_eq_GL
#print axioms card_homFibre_GL
#print axioms sum_hom_rankArrays
#print axioms sum_homLiftTest
#print axioms card_homRankArray
#print axioms homogeneous_lift_density_le

example (z : ℕ) :
    (∏ i ∈ Finset.range 0, (2^(z+0)-2^(z+i))) = 1 := by simp

example (k : ℕ) :
    (∏ i ∈ Finset.range k, (2^(0+k)-2^(0+i))) =
      Nat.card (GL (Fin k) (ZMod 2)) := by
  simpa using homFibre_product_eq_GL 0 k

end
