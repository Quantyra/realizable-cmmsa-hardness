import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace PvNP.RealizableHardness.ActualFiniteScalarSumReindex

open scoped BigOperators

/-- Reindex a finite scalar sum by an equivalence, keeping the summand as one
opaque scalar function. This avoids unfolding dependent fibers in callers. -/
theorem sum_equiv_scalar {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] (e : α ≃ β) (F : β → M) :
    (∑ x : α, F (e x)) = ∑ y : β, F y := by
  apply Fintype.sum_equiv e
  intro x
  rfl

end PvNP.RealizableHardness.ActualFiniteScalarSumReindex
