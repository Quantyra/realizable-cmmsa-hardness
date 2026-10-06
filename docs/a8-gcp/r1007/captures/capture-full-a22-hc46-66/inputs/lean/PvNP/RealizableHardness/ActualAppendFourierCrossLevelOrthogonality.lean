import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

/-! Exact Fourier orthogonality after the actual appended-column average.
The proof is for the fixed append experiment: one uniform base matrix and
independent uniform appended columns. -/

namespace PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

set_option autoImplicit false
noncomputable section

/-- Appending zero-frequency columns embeds a base frequency without changing
its rank. -/
def appendZeroFrequency {n c s : Nat} (Y : BinaryMatrix n c) :
    BinaryMatrix n (c + s) :=
  appendBinaryMatrix Y 0

@[simp] theorem appendBinaryMatrix_apply_castAdd {n c s : Nat}
    (Y : BinaryMatrix n c) (Z : BinaryMatrix n s)
    (i : Fin n) (j : Fin c) :
    appendBinaryMatrix Y Z i (Fin.castAdd s j) = Y i j := by
  change Sum.elim
      ((ActualFixedFunctionalBinaryMatrixMoment.coordinateArrayBinaryMatrixEquiv n c).symm Y)
      ((ActualFixedFunctionalBinaryMatrixMoment.coordinateArrayBinaryMatrixEquiv n s).symm Z)
      (finSumFinEquiv.symm (Fin.castAdd s j)) i = Y i j
  rw [finSumFinEquiv_symm_apply_castAdd]
  change (ActualFixedFunctionalBinaryMatrixMoment.coordinateArrayBinaryMatrixEquiv n c).symm Y j i = Y i j
  rfl

@[simp] theorem appendBinaryMatrix_apply_natAdd {n c s : Nat}
    (Y : BinaryMatrix n c) (Z : BinaryMatrix n s)
    (i : Fin n) (j : Fin s) :
    appendBinaryMatrix Y Z i (Fin.natAdd c j) = Z i j := by
  change Sum.elim
      ((ActualFixedFunctionalBinaryMatrixMoment.coordinateArrayBinaryMatrixEquiv n c).symm Y)
      ((ActualFixedFunctionalBinaryMatrixMoment.coordinateArrayBinaryMatrixEquiv n s).symm Z)
      (finSumFinEquiv.symm (Fin.natAdd c j)) i = Z i j
  rw [finSumFinEquiv_symm_apply_natAdd]
  change (ActualFixedFunctionalBinaryMatrixMoment.coordinateArrayBinaryMatrixEquiv n s).symm Z j i = Z i j
  rfl

/-- Characters factor across the accepted ordered base/append matrix
equivalence. -/
theorem pairing_appendBinaryMatrix {n c s : Nat}
    (Y : BinaryMatrix n c) (Z : BinaryMatrix n s)
    (M : BinaryMatrix n c) (B : BinaryMatrix n s) :
    BinaryMatrixFourier.pairing (appendBinaryMatrix Y Z)
        (appendBinaryMatrix M B) =
      BinaryMatrixFourier.pairing Y M + BinaryMatrixFourier.pairing Z B := by
  classical
  unfold BinaryMatrixFourier.pairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp

theorem character_appendBinaryMatrix {n c s : Nat}
    (Y : BinaryMatrix n c) (Z : BinaryMatrix n s)
    (M : BinaryMatrix n c) (B : BinaryMatrix n s) :
    BinaryMatrixFourier.character (appendBinaryMatrix Y Z)
        (appendBinaryMatrix M B) =
      BinaryMatrixFourier.character Y M *
        BinaryMatrixFourier.character Z B := by
  classical
  change (if BinaryMatrixFourier.pairing (appendBinaryMatrix Y Z)
      (appendBinaryMatrix M B) = 0 then 1 else -1) =
      (if BinaryMatrixFourier.pairing Y M = 0 then 1 else -1) *
      (if BinaryMatrixFourier.pairing Z B = 0 then 1 else -1)
  rw [pairing_appendBinaryMatrix]
  have h := BinaryMatrixFourier.bitSign_add
    (BinaryMatrixFourier.pairing Y M) (BinaryMatrixFourier.pairing Z B)
  change (if BinaryMatrixFourier.pairing Y M + BinaryMatrixFourier.pairing Z B = 0
      then (1 : Real) else -1) =
    (if BinaryMatrixFourier.pairing Y M = 0 then (1 : Real) else -1) *
      (if BinaryMatrixFourier.pairing Z B = 0 then (1 : Real) else -1) at h
  exact h

/-- Averaging a full character over appended columns kills it exactly when
its appended frequency block is nonzero. -/
theorem appendAverage_character {n c s : Nat}
    (Z : BinaryMatrix n (c + s)) (M : BinaryMatrix n c) :
    appendAverage (BinaryMatrixFourier.character Z) M =
      if ((appendBinaryMatrixEquiv n c s).symm Z).2 = 0 then
        BinaryMatrixFourier.character ((appendBinaryMatrixEquiv n c s).symm Z).1 M
      else 0 := by
  classical
  let Y := ((appendBinaryMatrixEquiv n c s).symm Z).1
  let W := ((appendBinaryMatrixEquiv n c s).symm Z).2
  have hp : (appendBinaryMatrixEquiv n c s).symm Z = (Y, W) := by
    simp [Y, W]
  have hz : appendBinaryMatrix Y W = Z := by
    change (appendBinaryMatrixEquiv n c s) ((appendBinaryMatrixEquiv n c s).symm Z) = Z
    exact (appendBinaryMatrixEquiv n c s).apply_symm_apply Z
  have hpoint (B : BinaryMatrix n s) :
      BinaryMatrixFourier.character Z (appendBinaryMatrix M B) =
        BinaryMatrixFourier.character Y M * BinaryMatrixFourier.character W B := by
    rw [← hz]
    exact character_appendBinaryMatrix Y W M B
  have hmeanW :
      uniformMean (BinaryMatrixFourier.character W) =
        if W = 0 then 1 else 0 := by
    have hc0 (B : BinaryMatrix n s) :
        BinaryMatrixFourier.character (0 : BinaryMatrix n s) B = 1 := by
      simp [BinaryMatrixFourier.character, BinaryMatrixFourier.pairing]
    simpa only [hc0, mul_one] using
      BinaryMatrixFourier.character_orthogonality W 0
  have hfactor :
      uniformMean (fun B : BinaryMatrix n s =>
        BinaryMatrixFourier.character Y M * BinaryMatrixFourier.character W B) =
      BinaryMatrixFourier.character Y M *
        uniformMean (BinaryMatrixFourier.character W) := by
    unfold uniformMean
    calc
      (∑ B : BinaryMatrix n s,
          BinaryMatrixFourier.character Y M * BinaryMatrixFourier.character W B) /
          (Fintype.card (BinaryMatrix n s) : Real) =
        (BinaryMatrixFourier.character Y M *
          ∑ B : BinaryMatrix n s, BinaryMatrixFourier.character W B) /
            (Fintype.card (BinaryMatrix n s) : Real) := by
              rw [← Finset.mul_sum]
      _ = BinaryMatrixFourier.character Y M *
          ((∑ B : BinaryMatrix n s, BinaryMatrixFourier.character W B) /
            (Fintype.card (BinaryMatrix n s) : Real)) := by ring
  unfold appendAverage
  change uniformMean (fun B : BinaryMatrix n s =>
    BinaryMatrixFourier.character Z (appendBinaryMatrix M B)) =
      if W = 0 then BinaryMatrixFourier.character Y M else 0
  rw [show (fun B : BinaryMatrix n s =>
      BinaryMatrixFourier.character Z (appendBinaryMatrix M B)) =
      (fun B => BinaryMatrixFourier.character Y M *
        BinaryMatrixFourier.character W B) from by
          funext B
          exact hpoint B]
  rw [hfactor, hmeanW]
  by_cases hW : W = 0 <;> simp [hW]

/-- Distinct full-matrix frequencies remain orthogonal after the actual
append-column averaging operator. -/
theorem appendAverage_character_mul_eq_zero {n c s : Nat}
    (Z Z' : BinaryMatrix n (c + s))
    (hrank : Z.rank ≠ Z'.rank) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (BinaryMatrixFourier.character Z) M *
        appendAverage (BinaryMatrixFourier.character Z') M) = 0 := by
  classical
  let e := appendBinaryMatrixEquiv n c s
  let Y := (e.symm Z).1
  let W := (e.symm Z).2
  let Y' := (e.symm Z').1
  let W' := (e.symm Z').2
  have hZ : appendBinaryMatrix Y W = Z := by
    change e (e.symm Z) = Z
    exact e.apply_symm_apply Z
  have hZ' : appendBinaryMatrix Y' W' = Z' := by
    change e (e.symm Z') = Z'
    exact e.apply_symm_apply Z'
  have hOp (M : BinaryMatrix n c) : appendAverage (BinaryMatrixFourier.character Z) M =
      if W = 0 then BinaryMatrixFourier.character Y M else 0 := by
    simpa [e, Y, W] using appendAverage_character Z M
  have hOp' (M : BinaryMatrix n c) : appendAverage (BinaryMatrixFourier.character Z') M =
      if W' = 0 then BinaryMatrixFourier.character Y' M else 0 := by
    simpa [e, Y', W'] using appendAverage_character Z' M
  simp_rw [hOp, hOp']
  by_cases hW : W = 0 <;> by_cases hW' : W' = 0
  · have hY : Y ≠ Y' := by
      intro h
      apply hrank
      have hEq : Z = Z' := by
        calc
          Z = appendBinaryMatrix Y W := hZ.symm
          _ = appendBinaryMatrix Y' W' := by simp [hW, hW', h]
          _ = Z' := hZ'
      exact congrArg (fun A : BinaryMatrix n (c + s) => A.rank) hEq
    have horth := BinaryMatrixFourier.character_orthogonality Y Y'
    simp only [hW, hW', ite_true]
    simpa [hY] using horth
  all_goals simp [hW, hW', uniformMean]

/-- Averaging a finite Fourier sum commutes with the actual uniform
append-column average. -/
theorem uniformMean_sum {n d : Nat} {α : Type*} [Fintype α]
    (s : Finset α) (f : α → BinaryMatrix n d → Real) :
    uniformMean (fun M => ∑ a ∈ s, f a M) =
      ∑ a ∈ s, uniformMean (f a) := by
  classical
  unfold uniformMean
  rw [Finset.sum_comm]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]

theorem uniformMean_const_mul {n d : Nat} (a : Real)
    (f : BinaryMatrix n d → Real) :
    uniformMean (fun M => a * f M) = a * uniformMean f := by
  classical
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

/-- The exact finite-frequency expansion of one actual appended projection. -/
theorem appendAverage_rankProjection_sum {n c s i : Nat}
    (F : BinaryMatrix n (c + s) → Real) (M : BinaryMatrix n c) :
    appendAverage (rankProjection i F) M =
      ∑ Z ∈ (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
        (fun Z => Z.rank = i),
        fourierCoeff F Z * appendAverage (BinaryMatrixFourier.character Z) M := by
  classical
  unfold appendAverage
  unfold rankProjection
  rw [uniformMean_sum]
  apply Finset.sum_congr rfl
  intro Z hZ
  rw [uniformMean_const_mul]


/-- The actual append-column expectation preserves orthogonality between two
distinct total Fourier ranks.  The same fixed function `F` is used at every
appended draw, and all averages are unconditional. -/
theorem uniformMean_appendAverage_rankProjection_mul_rankProjection_eq_zero
    {n c s i j : Nat} (hij : i ≠ j)
    (F : BinaryMatrix n (c + s) → Real) :
    uniformMean (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M *
        appendAverage (rankProjection j F) M) = 0 := by
  classical
  let si := (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
    (fun Z => Z.rank = i)
  let sj := (Finset.univ : Finset (BinaryMatrix n (c + s))).filter
    (fun Z => Z.rank = j)
  have hpoint (M : BinaryMatrix n c) :
      (∑ Z ∈ si, fourierCoeff F Z * appendAverage (BinaryMatrixFourier.character Z) M) *
      (∑ Z ∈ sj, fourierCoeff F Z * appendAverage (BinaryMatrixFourier.character Z) M) =
      ∑ Z ∈ si, ∑ Z' ∈ sj,
        (fourierCoeff F Z * fourierCoeff F Z') *
          (appendAverage (BinaryMatrixFourier.character Z) M *
            appendAverage (BinaryMatrixFourier.character Z') M) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro Z hZ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Z' hZ'
    ring
  rw [show (fun M : BinaryMatrix n c =>
      appendAverage (rankProjection i F) M * appendAverage (rankProjection j F) M) =
      (fun M => ∑ Z ∈ si, ∑ Z' ∈ sj,
        (fourierCoeff F Z * fourierCoeff F Z') *
          (appendAverage (BinaryMatrixFourier.character Z) M *
            appendAverage (BinaryMatrixFourier.character Z') M)) from by
              funext M
              rw [appendAverage_rankProjection_sum (i := i) F M,
                appendAverage_rankProjection_sum (i := j) F M]
              exact hpoint M]
  rw [uniformMean_sum]
  apply Finset.sum_eq_zero
  intro Z hZ
  rw [uniformMean_sum]
  apply Finset.sum_eq_zero
  intro Z' hZ'
  have hz : Z.rank = i := (Finset.mem_filter.mp hZ).2
  have hz' : Z'.rank = j := (Finset.mem_filter.mp hZ').2
  have hne : Z.rank ≠ Z'.rank := by
    rw [hz, hz']
    exact hij
  rw [uniformMean_const_mul]
  rw [appendAverage_character_mul_eq_zero Z Z' hne]
  simp

end
end PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
