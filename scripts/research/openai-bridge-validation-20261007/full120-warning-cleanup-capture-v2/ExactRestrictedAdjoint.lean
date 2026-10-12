import PvNP.RealizableHardness.ExactAppendBlockIdentity

/-! Candidate exact restricted-adjoint translation. The invariant input is
only the first functional K, as in the manuscript. -/

namespace PvNP.RealizableHardness.ExactRestrictedAdjoint

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ExactAppendOperatorContracts
open PvNP.RealizableHardness.ExactAppendBlockIdentity
open PvNP.RealizableHardness.RectangularGLRowCompletion

set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite

abbrev FirstBlock {n c s : Nat} (W : BinaryMatrix n (c + s)) :
    BinaryMatrix n c := fun i j => W i (Fin.castAdd s j)

@[simp] theorem firstBlock_append {n c s : Nat}
    (M : BinaryMatrix n c) (B : BinaryMatrix n s) :
    FirstBlock (appendBinaryMatrix M B) = M := by
  ext i j
  simp [FirstBlock]

@[simp] theorem firstBlock_mul {n c s : Nat}
    (W : BinaryMatrix n (c + s)) (U : BinaryMatrix (c + s) (c + s)) :
    FirstBlock (W * U) = W * FirstColumns U := by
  ext i j
  simp [FirstBlock, FirstColumns, Matrix.mul_apply]

/-- Right multiplication by an explicitly paired-invertible matrix is a
permutation of the complete matrix carrier. -/
def rightMulEquiv {n d : Nat} (p : InversePair d) :
    BinaryMatrix n d ≃ BinaryMatrix n d where
  toFun W := W * p.1.1
  invFun W := W * p.1.2
  left_inv W := by simp [Matrix.mul_assoc, p.2.1]
  right_inv W := by simp [Matrix.mul_assoc, p.2.2]

/-- Averaging `K(W) H(first-c-columns(W))` is unchanged by a fixed paired
right action, using only right invariance of K. -/
theorem prefix_weight_sum_right_action {n c s : Nat}
    (K : BinaryMatrix n (c + s) → Real)
    (hK : RightInvariant K)
    (H : BinaryMatrix n c → Real) (p : InversePair (c + s)) :
    (∑ W : BinaryMatrix n (c + s), K W * H (FirstBlock W)) =
      ∑ W : BinaryMatrix n (c + s),
        K W * H (W * FirstColumns p.1.1) := by
  let e := rightMulEquiv (n := n) p
  have hreindex := (Equiv.sum_comp e
    (fun W : BinaryMatrix n (c + s) => K W * H (FirstBlock W))).symm
  calc
    (∑ W : BinaryMatrix n (c + s), K W * H (FirstBlock W)) =
        ∑ W : BinaryMatrix n (c + s),
          K (W * p.1.1) * H (FirstBlock (W * p.1.1)) := by
            simpa [e, rightMulEquiv] using hreindex
    _ = ∑ W : BinaryMatrix n (c + s),
          K W * H (W * FirstColumns p.1.1) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [hK W p.1.1 p.1.2 p.2.1 p.2.2, firstBlock_mul]

/-- The actual append product bijection turns the fixed-base nested average
into a uniform mean over every full n-by-(c+s) matrix. -/
theorem append_weighted_product_mean {n c s : Nat}
    (K : BinaryMatrix n (c + s) → Real)
    (H : BinaryMatrix n c → Real) :
    BinaryMatrixFourier.uniformMean (fun M : BinaryMatrix n c =>
      appendAverage K M * H M) =
      (∑ W : BinaryMatrix n (c + s), K W * H (FirstBlock W)) /
        (Fintype.card (BinaryMatrix n (c + s)) : Real) := by
  classical
  let e := ActualFixedFunctionalAppendOperator.appendBinaryMatrixEquiv n c s
  let g := fun M : BinaryMatrix n c => fun B : BinaryMatrix n s =>
    K (appendBinaryMatrix M B) * H M
  have hproduct := normalized_product_mean_first g
  have hinner (M : BinaryMatrix n c) :
      (∑ B : BinaryMatrix n s,
        K (appendBinaryMatrix M B) * H M) /
          (Fintype.card (BinaryMatrix n s) : Real) =
        appendAverage K M * H M := by
    unfold appendAverage BinaryMatrixFourier.uniformMean
    rw [← Finset.sum_mul]
    ring
  have hpair :
      (∑ p : BinaryMatrix n c × BinaryMatrix n s,
        g p.1 p.2) /
          (Fintype.card (BinaryMatrix n c × BinaryMatrix n s) : Real) =
        BinaryMatrixFourier.uniformMean (fun M : BinaryMatrix n c =>
          appendAverage K M * H M) := by
    rw [hproduct]
    unfold BinaryMatrixFourier.uniformMean
    apply congrArg (fun z : Real => z /
      (Fintype.card (BinaryMatrix n c) : Real))
    apply Finset.sum_congr rfl
    intro M hM
    exact hinner M
  have hsum :
      (∑ p : BinaryMatrix n c × BinaryMatrix n s, g p.1 p.2) =
        ∑ W : BinaryMatrix n (c + s), K W * H (FirstBlock W) := by
    calc
      (∑ p : BinaryMatrix n c × BinaryMatrix n s, g p.1 p.2) =
          ∑ p : BinaryMatrix n c × BinaryMatrix n s,
            K (e p) * H (FirstBlock (e p)) := by
              apply Finset.sum_congr rfl
              intro p _
              change K (appendBinaryMatrix p.1 p.2) * H p.1 =
                K (appendBinaryMatrix p.1 p.2) *
                  H (FirstBlock (appendBinaryMatrix p.1 p.2))
              rw [firstBlock_append]
      _ = _ := Equiv.sum_comp e (fun W : BinaryMatrix n (c + s) =>
        K W * H (FirstBlock W))
  have hcard := Fintype.card_congr e
  rw [hsum, hcard] at hpair
  exact hpair.symm

/-- Averaging a fixed GL right action and using the first-column marginal
turns the first-c-coordinate statistic into the exact G operator, with K
invariant as the sole restriction. -/
theorem weighted_prefix_mean_eq_gAverage {n c s : Nat}
    (K : BinaryMatrix n (c + s) → Real) (hK : RightInvariant K)
    (H : BinaryMatrix n c → Real) :
    BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
      K W * H (FirstBlock W)) =
    BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
      K W * gAverage H W) := by
  classical
  have hInversePair : Nonempty (InversePair (c + s)) := ⟨⟨(1, 1), by simp⟩⟩
  have hBinaryMatrix : Nonempty (BinaryMatrix n (c + s)) := ⟨0⟩
  let gAction := fun p : InversePair (c + s) => fun W : BinaryMatrix n (c + s) =>
    K W * H (W * FirstColumns p.1.1)
  have hfixed (p : InversePair (c + s)) :
      (∑ W : BinaryMatrix n (c + s),
        K W * H (FirstBlock W)) =
        ∑ W : BinaryMatrix n (c + s), gAction p W := by
    simpa [gAction] using prefix_weight_sum_right_action K hK H p
  have hdouble :
      (∑ p : InversePair (c + s),
        ∑ W : BinaryMatrix n (c + s), gAction p W) =
        (Fintype.card (InversePair (c + s)) : Real) *
          (∑ W : BinaryMatrix n (c + s),
            K W * H (FirstBlock W)) := by
    calc
      _ = ∑ p : InversePair (c + s),
          ∑ W : BinaryMatrix n (c + s), K W * H (FirstBlock W) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact (hfixed p).symm
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hprod := @normalized_product_mean
    (InversePair (c + s)) (BinaryMatrix n (c + s))
    inferInstance inferInstance hInversePair hBinaryMatrix gAction
  have hPairMean :
      (∑ p : InversePair (c + s) × BinaryMatrix n (c + s),
        gAction p.1 p.2) /
          (Fintype.card (InversePair (c + s) × BinaryMatrix n (c + s)) : Real) =
        BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
          K W * H (FirstBlock W)) := by
    have hsum :
        (∑ p : InversePair (c + s) × BinaryMatrix n (c + s),
          gAction p.1 p.2) =
          (Fintype.card (InversePair (c + s)) : Real) *
            (∑ W : BinaryMatrix n (c + s),
              K W * H (FirstBlock W)) := by
      rw [Fintype.sum_prod_type]
      exact hdouble
    have hcard : (Fintype.card (InversePair (c + s)) : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (InversePair (c + s)) ≠ 0)
    rw [hsum, Fintype.card_prod, Nat.cast_mul]
    unfold BinaryMatrixFourier.uniformMean
    exact mul_div_mul_left _ _ hcard
  have hcol (W : BinaryMatrix n (c + s)) :
      (∑ p : InversePair (c + s),
        H (W * FirstColumns p.1.1)) /
          (Fintype.card (InversePair (c + s)) : Real) =
        gAverage H W := by
    have h := first_columns_uniform_mean (c := c) (s := s)
      (fun R : BinaryMatrix (c + s) c => H (W * R))
    simpa [gAverage] using h
  have hnested :
      (∑ W : BinaryMatrix n (c + s),
        (∑ p : InversePair (c + s), gAction p W) /
          (Fintype.card (InversePair (c + s)) : Real)) /
        (Fintype.card (BinaryMatrix n (c + s)) : Real) =
      BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
        K W * gAverage H W) := by
    unfold BinaryMatrixFourier.uniformMean
    apply congrArg (fun z : Real => z /
      (Fintype.card (BinaryMatrix n (c + s)) : Real))
    apply Finset.sum_congr rfl
    intro W hW
    change (∑ p : InversePair (c + s),
        K W * H (W * FirstColumns p.1.1)) /
        (Fintype.card (InversePair (c + s)) : Real) = _
    calc
      _ = K W * ((∑ p : InversePair (c + s),
          H (W * FirstColumns p.1.1)) /
            (Fintype.card (InversePair (c + s)) : Real)) := by
              rw [← Finset.mul_sum]
              ring
      _ = K W * gAverage H W := by rw [hcol W]
  calc
    BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
        K W * H (FirstBlock W)) =
      (∑ p : InversePair (c + s) × BinaryMatrix n (c + s),
        gAction p.1 p.2) /
        (Fintype.card (InversePair (c + s) × BinaryMatrix n (c + s)) : Real) :=
          hPairMean.symm
    _ = (∑ W : BinaryMatrix n (c + s),
        (∑ p : InversePair (c + s), gAction p W) /
          (Fintype.card (InversePair (c + s)) : Real)) /
        (Fintype.card (BinaryMatrix n (c + s)) : Real) := hprod
    _ = BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
        K W * gAverage H W) := hnested

/-- Exact manuscript restricted adjoint for invariant first argument K and
arbitrary base statistic H. No invariance assumption is imposed on H. -/
theorem restricted_adjoint_exact {n c s : Nat}
    (K : BinaryMatrix n (c + s) → Real) (H : BinaryMatrix n c → Real)
    (hK : RightInvariant K) :
    BinaryMatrixFourier.uniformMean (fun M : BinaryMatrix n c =>
      appendAverage K M * H M) =
    BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
      K W * gAverage H W) := by
  calc
    BinaryMatrixFourier.uniformMean (fun M : BinaryMatrix n c =>
        appendAverage K M * H M) =
      BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
        K W * H (FirstBlock W)) := append_weighted_product_mean K H
    _ = BinaryMatrixFourier.uniformMean (fun W : BinaryMatrix n (c + s) =>
        K W * gAverage H W) := weighted_prefix_mean_eq_gAverage K hK H

end
end PvNP.RealizableHardness.ExactRestrictedAdjoint
