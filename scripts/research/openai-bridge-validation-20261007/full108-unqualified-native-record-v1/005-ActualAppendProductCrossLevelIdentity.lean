import PvNP.RealizableHardness.ActualFiniteFrameProductDuality
import PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality

/-! Exact same-function real cross-level Gram identity for the original
unconditional append. This successor candidate has not been compiled.
It does not establish G/Phi, adjointness, complex generality, source witnesses
or runtime. The two imported native results remain immutable. -/

namespace PvNP.RealizableHardness.ActualAppendProductCrossLevelIdentity

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFiniteFrameProductDuality
open PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality

set_option autoImplicit false
noncomputable section

/-- The manuscript's exact same-function cross-level identity: equal ranks
have the product eigenvalue times the original energy, and distinct ranks
have zero Gram entry. Each matrix carrier uses its own normalized mean.
The rank guard is needed for the product formula on the diagonal; no guard
on the other rank is needed for off-diagonal orthogonality. -/
theorem append_rank_cross_level_gram_eq_product {n c s i j : Nat}
    (hi : i ≤ c + s) (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M *
        appendAverage (rankProjection j F) M) =
      if i = j then
        (∏ k : Fin s, (((2 : Real) ^ (c + s - i) - (2 : Real) ^ k.val) /
          ((2 : Real) ^ (c + s) - (2 : Real) ^ k.val))) *
          uniformMean (fun W : BinaryMatrix n (c + s) =>
            (rankProjection i F W) ^ 2)
      else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simpa only [pow_two] using
      (append_rank_projection_energy_eq_product hi F basisInv)
  · rw [if_neg hij]
    exact uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero hij F

end
end PvNP.RealizableHardness.ActualAppendProductCrossLevelIdentity
