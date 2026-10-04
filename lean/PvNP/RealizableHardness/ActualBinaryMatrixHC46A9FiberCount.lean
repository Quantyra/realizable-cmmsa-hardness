import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph

/-!
An explicit fixed-final graph-datum census for the A9 interface.

This packages the exact cardinality already supported by the graph parameterization
with rank preservation for every datum. It does not identify these abstract graph
data with the manuscript's actual predecessor fiber over a final `(A,B,Y)`.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A9FiberCount

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

abbrev F := ZMod 2

/-- For fixed final carrier spaces of dimensions `a` and `b` and a fixed
rank-`k` space, the A9 graph parameters have the exact manuscript count, and
each project-then-lift map has rank `k`. This is the abstract graph census;
the actual manuscript-fiber equivalence is a separate obligation. -/
theorem a9_fixed_final_graph_census
    {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B] [AddCommGroup S] [Module F S] [Module.Free F S]
    [Module.Finite F S] [Fintype S]
    (i j k a b : Nat)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    Fintype.card (A9InitialDatum A B S i j) =
        w6Gaussian a i * 2 ^ (k * (a - i)) *
          (w6Gaussian b j * 2 ^ (k * (b - j))) ∧
      ∀ d : A9InitialDatum A B S i j,
        Module.finrank F (LinearMap.range (a9InitialMap d)) = k := by
  constructor
  · exact a9_initial_datum_card i j k a b hA hB hS
  · intro d
    rw [a9InitialMap_rank d, hS]

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A9FiberCount
