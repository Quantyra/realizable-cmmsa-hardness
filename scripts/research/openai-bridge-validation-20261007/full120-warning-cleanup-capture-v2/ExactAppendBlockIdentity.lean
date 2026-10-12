import PvNP.RealizableHardness.ExactAppendOperatorContracts
import PvNP.RealizableHardness.RectangularGLSelectedRows

/-! Exact pointwise append/block algebra for the unrestricted append matrix.
This source is an uncompiled candidate. It uses the pinned castAdd/natAdd
column APIs and keeps every input matrix arbitrary. -/

namespace PvNP.RealizableHardness.ExactAppendBlockIdentity

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ExactAppendOperatorContracts
open PvNP.RealizableHardness.RectangularGLRowCompletion
open PvNP.RealizableHardness.RectangularGLSelectedRows

set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite

abbrev FirstColumns {c s : Nat} (U : BinaryMatrix (c + s) (c + s)) :
    BinaryMatrix (c + s) c :=
  fun i j => U i (Fin.castAdd s j)

abbrev LastColumns {c s : Nat} (U : BinaryMatrix (c + s) (c + s)) :
    BinaryMatrix (c + s) s :=
  fun i j => U i (Fin.natAdd c j)

abbrev FirstRows {c s : Nat} (V : BinaryMatrix (c + s) (c + s)) :
    BinaryMatrix c (c + s) :=
  fun i j => V (Fin.castAdd s i) j

abbrev LastRows {c s : Nat} (V : BinaryMatrix (c + s) (c + s)) :
    BinaryMatrix s (c + s) :=
  fun i j => V (Fin.natAdd c i) j

/-- The direct first-column restriction used by the block algebra is the same
matrix carried by the established transpose-prefix GL map. -/
theorem firstColumns_eq_columnPrefixMap {c s : Nat}
    (p : InversePair (c + s)) :
    FirstColumns p.1.1 =
      (RectangularGLRowCompletion.columnPrefixMap p).1 := by
  ext i j
  simp [FirstColumns,
    RectangularGLRowCompletion.columnPrefixMap,
    RectangularGLRowCompletion.rowColumnFrameEquiv,
    RectangularGLRowCompletion.rowPrefixMap,
    RectangularGLRowCompletion.inversePairTranspose,
    RectangularGLRowCompletion.canonicalPrefixMatrix,
    RectangularGLRowCompletion.canonicalPrefixMap,
    Matrix.transpose_mul, Matrix.mul_apply, LinearMap.toMatrix', Pi.single_apply]

/-- The direct bottom-row restriction is the selected-row map on the stored
inverse coordinate of the paired GL carrier. -/
theorem bottomInverseRowsMap_val {c s : Nat}
    (p : InversePair (c + s)) :
    (RectangularGLSelectedRows.bottomInverseRowsMap p).1 =
      LastRows p.1.2 := by
  ext i j
  simp [RectangularGLSelectedRows.bottomInverseRowsMap,
    RectangularGLSelectedRows.selectedRowsMap,
    RectangularGLSelectedRows.bottomRowsMatrix,
    RectangularGLSelectedRows.bottomRowsMap,
    RectangularGLSelectedRows.inversePairSwap,
    LastRows, Matrix.mul_apply, LinearMap.toMatrix', Pi.single_apply]

/-- The first-column GL marginal stated for the direct block-restriction
matrix consumed by the pointwise append identity. -/
theorem first_columns_uniform_mean {c s : Nat}
    (g : BinaryMatrix (c + s) c → Real) :
    (∑ p : InversePair (c + s), g (FirstColumns p.1.1)) /
        (Fintype.card (InversePair (c + s)) : Real) =
      (∑ R : {R : BinaryMatrix (c + s) c //
        Function.Injective (Matrix.toLin' R)}, g R.1) /
        (Fintype.card {R : BinaryMatrix (c + s) c //
          Function.Injective (Matrix.toLin' R)} : Real) := by
  classical
  have hcolumn :=
    RectangularGLRowCompletion.column_prefix_uniform_mean
      (c := c) (s := s)
      (fun R : {R : BinaryMatrix (c + s) c //
        Function.Injective (Matrix.toLin' R)} => g R.1)
  have hmap :
      (∑ p : InversePair (c + s),
        g (FirstColumns p.1.1)) =
        ∑ p : InversePair (c + s),
          g ((RectangularGLRowCompletion.columnPrefixMap p).1) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [firstColumns_eq_columnPrefixMap]
  simpa only [hmap] using hcolumn

/-- The inverse-bottom-row GL marginal stated for the direct matrix block
consumed by the pointwise append identity. -/
theorem last_rows_inverse_uniform_mean {c s : Nat}
    (g : BinaryMatrix s (c + s) → Real) :
    (∑ p : InversePair (c + s), g (LastRows p.1.2)) /
        (Fintype.card (InversePair (c + s)) : Real) =
      (∑ C : ExactAppendOperatorContracts.FullRowFrame s (c + s), g C.1) /
        (Fintype.card (ExactAppendOperatorContracts.FullRowFrame s (c + s)) : Real) := by
  classical
  have hbottom := RectangularGLSelectedRows.bottom_inverse_rows_uniform_mean
    (fun C : ExactAppendOperatorContracts.FullRowFrame s (c + s) => g C.1)
  have hmap :
      (∑ p : InversePair (c + s),
        g (LastRows p.1.2)) =
        ∑ p : InversePair (c + s),
          g ((RectangularGLSelectedRows.bottomInverseRowsMap p).1) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [bottomInverseRowsMap_val]
  simpa only [hmap] using hbottom

/-- Split square multiplication into the exact first-c and last-s blocks.
The zero-width cases are included by `finSumFinEquiv`. -/
theorem square_mul_block_split {c s : Nat}
    (U V : BinaryMatrix (c + s) (c + s)) :
    U * V = FirstColumns U * FirstRows V + LastColumns U * LastRows V := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, FirstColumns, FirstRows,
    LastColumns, LastRows]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp [finSumFinEquiv]

/-- Right-multiplication of the actual append matrix splits into the same
ordered row blocks. -/
theorem append_mul_right_block_split {n c s : Nat}
    (X : BinaryMatrix n c) (B : BinaryMatrix n s)
    (V : BinaryMatrix (c + s) (c + s)) :
    appendBinaryMatrix X B * V = X * FirstRows V + B * LastRows V := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, FirstRows, LastRows]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp [finSumFinEquiv]

/-- For each paired inverse U,V, the exact matrix identity behind G(TF)=Phi.
No rank or nonzero assumption is placed on M or B. -/
theorem append_inverse_block_identity {n c s : Nat}
    (M : BinaryMatrix n (c + s)) (B : BinaryMatrix n s)
    (p : InversePair (c + s)) :
    appendBinaryMatrix (M * FirstColumns p.1.1) B * p.1.2 =
      M + (B - M * LastColumns p.1.1) * LastRows p.1.2 := by
  let U := p.1.1
  let V := p.1.2
  let R := FirstColumns U
  let S := LastColumns U
  let A := FirstRows V
  let C := LastRows V
  have hblock : R * A + S * C = 1 := by
    have h := square_mul_block_split U V
    simpa [U, V, R, S, A, C] using h.symm.trans p.2.1
  have hM : M = M * (R * A) + M * (S * C) := by
    calc
      M = M * (1 : BinaryMatrix (c + s) (c + s)) := by simp
      _ = M * (R * A + S * C) := by rw [hblock]
      _ = M * (R * A) + M * (S * C) := Matrix.mul_add _ _ _
  calc
    appendBinaryMatrix (M * R) B * V = (M * R) * A + B * C :=
      append_mul_right_block_split (M * R) B V
    _ = M * (R * A) + B * C := by rw [Matrix.mul_assoc]
    _ = (M * (R * A) + M * (S * C)) + (B * C - M * (S * C)) := by
      abel
    _ = M + (B * C - M * (S * C)) := by rw [← hM]
    _ = M + (B - M * S) * C := by
      rw [Matrix.sub_mul, Matrix.mul_assoc]
  
/-- Invariance is applied to the same full matrix and the stored paired
inverse. The conclusion is pointwise in unrestricted B. -/
theorem invariant_append_block_identity {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Real) (hF : RightInvariant F)
    (M : BinaryMatrix n (c + s)) (B : BinaryMatrix n s)
    (p : InversePair (c + s)) :
    F (M + (B - M * LastColumns p.1.1) * LastRows p.1.2) =
      F (appendBinaryMatrix (M * FirstColumns p.1.1) B) := by
  have h := append_inverse_block_identity M B p
  rw [← h]
  exact hF (appendBinaryMatrix (M * FirstColumns p.1.1) B)
    p.1.2 p.1.1 p.2.2 p.2.1

/-- Translation by a fixed matrix is a bijection of the entire unrestricted
append carrier. -/
def appendTranslationEquiv {n s : Nat} (T : BinaryMatrix n s) :
    BinaryMatrix n s ≃ BinaryMatrix n s where
  toFun B := B - T
  invFun B := B + T
  left_inv B := sub_add_cancel B T
  right_inv B := add_sub_cancel_right B T

/-- For each fixed paired inverse, the append average equals the independent
unrestricted-B conditional Phi average at the bottom rows of its inverse.
This is the exact uniform-sum reindex, not a rank-conditioned replacement. -/
theorem fixed_pair_append_mean_eq_phi_condition {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Real) (hF : RightInvariant F)
    (M : BinaryMatrix n (c + s)) (p : InversePair (c + s)) :
    appendAverage F (M * FirstColumns p.1.1) =
      BinaryMatrixFourier.uniformMean (fun B : BinaryMatrix n s =>
        F (M + B * LastRows p.1.2)) := by
  classical
  let T := M * LastColumns p.1.1
  let C := LastRows p.1.2
  have hpoint (B : BinaryMatrix n s) :
      F (appendBinaryMatrix (M * FirstColumns p.1.1) B) =
        F (M + (B - T) * C) := by
    simpa [T, C] using
      (invariant_append_block_identity F hF M B p).symm
  have hsumPoint :
      (∑ B : BinaryMatrix n s,
        F (appendBinaryMatrix (M * FirstColumns p.1.1) B)) =
        ∑ B : BinaryMatrix n s, F (M + (B - T) * C) := by
    apply Finset.sum_congr rfl
    intro B hB
    exact hpoint B
  have hsumShift :
      (∑ B : BinaryMatrix n s, F (M + (B - T) * C)) =
        ∑ B : BinaryMatrix n s, F (M + B * C) := by
    exact Equiv.sum_comp (appendTranslationEquiv T)
      (fun B => F (M + B * C))
  unfold appendAverage BinaryMatrixFourier.uniformMean
  rw [hsumPoint, hsumShift]

/-- Independent product carriers factor their exact normalized finite mean.
This is the normalization step used for the actual (B,C) Phi carrier. -/
theorem normalized_product_mean {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (g : A → B → Real) :
    (∑ p : A × B, g p.1 p.2) / (Fintype.card (A × B) : Real) =
      (∑ b : B, (∑ a : A, g a b) / (Fintype.card A : Real)) /
        (Fintype.card B : Real) := by
  classical
  have hsum : (∑ p : A × B, g p.1 p.2) =
      ∑ b : B, ∑ a : A, g a b := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hsumDiv :
      (∑ b : B, (∑ a : A, g a b) / (Fintype.card A : Real)) =
        (∑ b : B, ∑ a : A, g a b) / (Fintype.card A : Real) := by
    rw [Finset.sum_div]
  rw [hsum, Fintype.card_prod, Nat.cast_mul, hsumDiv, div_div]

/-- The same normalized product law with the opposite nesting order. -/
theorem normalized_product_mean_first {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (g : A → B → Real) :
    (∑ p : A × B, g p.1 p.2) / (Fintype.card (A × B) : Real) =
      (∑ a : A, (∑ b : B, g a b) / (Fintype.card B : Real)) /
        (Fintype.card A : Real) := by
  classical
  let e : A × B ≃ B × A := Equiv.prodComm A B
  have hsum :
      (∑ p : A × B, g p.1 p.2) =
        ∑ q : B × A, g q.2 q.1 := by
    exact (Equiv.sum_comp e.symm (fun p => g p.1 p.2)).symm
  have hcard := Fintype.card_congr e
  have h := normalized_product_mean (fun b a => g a b)
  simpa [e, hsum, hcard] using h

/-- The contract-level Phi is exactly the outer full-row-frame mean of the
unrestricted-B conditional mean, with the same independent product carrier. -/
theorem phiAverage_eq_rowConditionalMean {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Real) (M : BinaryMatrix n (c + s)) :
    phiAverage (s := s) F M =
      (∑ C : ExactAppendOperatorContracts.FullRowFrame s (c + s),
        BinaryMatrixFourier.uniformMean (fun B : BinaryMatrix n s =>
          F (M + B * C.1))) /
        (Fintype.card (ExactAppendOperatorContracts.FullRowFrame s (c + s)) : Real) := by
  classical
  have hframe : Nonempty (ExactAppendOperatorContracts.FullRowFrame s (c + s)) :=
    ⟨⟨bottomRowsMatrix c s, bottomRowsMap_surjective c s⟩⟩
  unfold phiAverage BinaryMatrixFourier.uniformMean
  simpa [BinaryMatrixFourier.uniformMean] using
    (@normalized_product_mean
      (BinaryMatrix n s) (ExactAppendOperatorContracts.FullRowFrame s (c + s))
      inferInstance inferInstance inferInstance hframe
      (fun B : BinaryMatrix n s => fun C : ExactAppendOperatorContracts.FullRowFrame s (c + s) =>
        F (M + B * C.1)))

/-- Candidate exact G(TF)=Phi(F) theorem on the actual finite frame carriers.
The proof averages the pointwise unrestricted-B translation over paired GL
matrices and then uses the independently proved first-column and inverse-
bottom-row marginals. No independence of those two GL marginals is assumed. -/
theorem g_append_eq_phi {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Real) (hF : RightInvariant F)
    (M : BinaryMatrix n (c + s)) :
    gAverage (fun X : BinaryMatrix n c => appendAverage F X) M =
      phiAverage (s := s) F M := by
  classical
  let gColumn :
      {R : BinaryMatrix (c + s) c //
        Function.Injective (Matrix.toLin' R)} → Real :=
    fun R => appendAverage F (M * R.1)
  let gRow : ExactAppendOperatorContracts.FullRowFrame s (c + s) → Real := fun C =>
    BinaryMatrixFourier.uniformMean (fun B : BinaryMatrix n s =>
      F (M + B * C.1))
  have hcolumn :=
    RectangularGLRowCompletion.column_prefix_uniform_mean
      (c := c) (s := s) gColumn
  have hcolumnMap :
      (∑ p : InversePair (c + s),
        appendAverage F (M * FirstColumns p.1.1)) =
        ∑ p : InversePair (c + s),
          appendAverage F
            (M * (RectangularGLRowCompletion.columnPrefixMap p).1) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [firstColumns_eq_columnPrefixMap]
  have hleft :
      gAverage (fun X : BinaryMatrix n c => appendAverage F X) M =
        (∑ p : InversePair (c + s),
          appendAverage F (M * FirstColumns p.1.1)) /
          (Fintype.card (InversePair (c + s)) : Real) := by
    unfold gAverage
    calc
      (∑ R : {R : BinaryMatrix (c + s) c //
          Function.Injective (Matrix.toLin' R)},
          appendAverage F (M * R.1)) /
            (Fintype.card {R : BinaryMatrix (c + s) c //
              Function.Injective (Matrix.toLin' R)} : Real) =
          (∑ p : InversePair (c + s),
            appendAverage F
              (M * (RectangularGLRowCompletion.columnPrefixMap p).1)) /
            (Fintype.card (InversePair (c + s)) : Real) := hcolumn.symm
      _ = _ := by rw [hcolumnMap]
  have hconditional :
      (∑ p : InversePair (c + s),
        appendAverage F (M * FirstColumns p.1.1)) /
          (Fintype.card (InversePair (c + s)) : Real) =
      (∑ p : InversePair (c + s), gRow
        (RectangularGLSelectedRows.bottomInverseRowsMap p)) /
          (Fintype.card (InversePair (c + s)) : Real) := by
    apply congrArg (fun z : Real =>
      z / (Fintype.card (InversePair (c + s)) : Real))
    apply Finset.sum_congr rfl
    intro p hp
    simpa [gRow, bottomInverseRowsMap_val] using
      (fixed_pair_append_mean_eq_phi_condition F hF M p)
  have hbottom :=
    RectangularGLSelectedRows.bottom_inverse_rows_uniform_mean gRow
  have hphi := phiAverage_eq_rowConditionalMean F M
  calc
    gAverage (fun X : BinaryMatrix n c => appendAverage F X) M =
        (∑ p : InversePair (c + s),
          appendAverage F (M * FirstColumns p.1.1)) /
          (Fintype.card (InversePair (c + s)) : Real) := hleft
    _ = (∑ p : InversePair (c + s), gRow
          (RectangularGLSelectedRows.bottomInverseRowsMap p)) /
          (Fintype.card (InversePair (c + s)) : Real) := hconditional
    _ = (∑ C : ExactAppendOperatorContracts.FullRowFrame s (c + s), gRow C) /
          (Fintype.card (ExactAppendOperatorContracts.FullRowFrame s (c + s)) : Real) := by
          simpa [gRow] using hbottom
    _ = phiAverage (s := s) F M := hphi.symm

end
end PvNP.RealizableHardness.ExactAppendBlockIdentity
