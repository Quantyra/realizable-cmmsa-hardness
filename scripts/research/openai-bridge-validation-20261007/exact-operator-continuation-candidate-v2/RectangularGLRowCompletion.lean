import PvNP.RealizableHardness.BinaryMatrixRightOrbit
import PvNP.RealizableHardness.RectangularFrameFiberAverage
import PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
Concrete rectangular completion step for full-row-rank binary matrices.

This uses the reviewed same-range right-orbit theorem to complete an arbitrary
surjective c-by-(c+s) matrix to a square invertible matrix.  It includes the
zero-row and zero-complement cases.  It does not yet supply the transpose
bridge needed to turn this into the manuscript's full-column-prefix marginal,
nor does it certify the enclosing G/Phi operator identity.
-/
namespace PvNP.RealizableHardness.RectangularGLRowCompletion

open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixRightOrbit

set_option autoImplicit false
noncomputable section

def canonicalPrefixMap (c s : Nat) :
    (Fin (c + s) → ZMod 2) →ₗ[ZMod 2] (Fin c → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd s)

def canonicalPrefixMatrix (c s : Nat) : BinaryMatrix c (c + s) :=
  LinearMap.toMatrix' (canonicalPrefixMap c s)

/-- An explicit square matrix and its two-sided inverse. This is used instead
of hiding the GL carrier behind a determinant predicate. -/
abbrev InversePair (d : Nat) :=
  {p : BinaryMatrix d d × BinaryMatrix d d //
    p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}

/-- The paired-matrix carrier is exactly Mathlib's finite general linear
group, represented by the matrix and its two-sided inverse. -/
def inversePairEquivGL (d : Nat) : InversePair d ≃
    Matrix.GeneralLinearGroup (Fin d) (ZMod 2) where
  toFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  invFun U := ⟨(U.val, U.inv), ⟨U.val_inv, U.inv_val⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv U := by
    apply Units.ext
    rfl

/-- A fibre of the actual row-prefix map on paired-inverse square matrices. -/
abbrev PrefixFiber (c s : Nat) (X : BinaryMatrix c (c + s)) :=
  {p : InversePair (c + s) // canonicalPrefixMatrix c s * p.1.1 = X}

/-- The actual finite carrier of full-row-rank rectangular binary matrices. -/
abbrev FullRowFrame (c d : Nat) :=
  {M : BinaryMatrix c d // Function.Surjective (Matrix.toLin' M)}

private theorem canonicalPrefixMap_surjective (c s : Nat) :
    Function.Surjective (canonicalPrefixMap c s) := by
  unfold canonicalPrefixMap
  apply LinearMap.funLeft_surjective_of_injective
  intro i j h
  exact Fin.ext (by simpa using congrArg Fin.val h)

/-- The canonical row-prefix map on explicit paired-inverse matrices. -/
def rowPrefixMap (c s : Nat) :
    InversePair (c + s) → FullRowFrame c (c + s) := fun p =>
  ⟨canonicalPrefixMatrix c s * p.1.1, by
    have hP : Function.Surjective (Matrix.toLin' (canonicalPrefixMatrix c s)) := by
      change Function.Surjective
        (Matrix.toLin' (LinearMap.toMatrix' (canonicalPrefixMap c s)))
      rw [Matrix.toLin'_toMatrix']
      exact canonicalPrefixMap_surjective c s
    have hU : Function.Surjective (Matrix.toLin' p.1.1) := by
      intro x
      refine ⟨Matrix.toLin' p.1.2 x, ?_⟩
      have hUV : (Matrix.toLin' p.1.1).comp (Matrix.toLin' p.1.2) =
          LinearMap.id := by
        rw [← Matrix.toLin'_mul, p.2.1, Matrix.toLin'_one]
      exact congrArg (fun f => f x) hUV
    change Function.Surjective (Matrix.toLin' (canonicalPrefixMatrix c s * p.1.1))
    rw [Matrix.toLin'_mul]
    exact hP.comp hU⟩

/-- Every full-row-rank c-by-(c+s) binary matrix is the first c rows of a
square invertible matrix, with both inverse laws retained as explicit matrix
equalities.  No positive-width assumption occurs, so c = 0 and s = 0 are
covered by the same proof. -/
theorem exists_square_completion {c s : Nat}
    (M : BinaryMatrix c (c + s))
    (hM : Function.Surjective (Matrix.toLin' M)) :
    ∃ U V : BinaryMatrix (c + s) (c + s),
      U * V = 1 ∧ V * U = 1 ∧ canonicalPrefixMatrix c s * U = M := by
  classical
  let P := canonicalPrefixMatrix c s
  have hP : Function.Surjective (Matrix.toLin' P) := by
    change Function.Surjective
      (Matrix.toLin' (LinearMap.toMatrix' (canonicalPrefixMap c s)))
    rw [Matrix.toLin'_toMatrix']
    exact canonicalPrefixMap_surjective c s
  have hRange : LinearMap.range (Matrix.toLin' M) =
      LinearMap.range (Matrix.toLin' P) := by
    rw [LinearMap.range_eq_top.mpr hM, LinearMap.range_eq_top.mpr hP]
  obtain ⟨U, V, hUV, hVU, hPU⟩ :=
    same_range_matrix_right_orbit M P hRange
  exact ⟨U, V, hUV, hVU, by simpa [P] using hPU⟩

/-- The row-prefix map is onto the complete full-row-frame subtype. -/
theorem rowPrefixMap_surjective (c s : Nat) :
    Function.Surjective (rowPrefixMap c s) := by
  intro X
  obtain ⟨U, V, hUV, hVU, hPU⟩ := exists_square_completion X.1 X.2
  refine ⟨⟨(U, V), ⟨hUV, hVU⟩⟩, ?_⟩
  apply Subtype.ext
  exact hPU

/-- The subtype equality in the full-row codomain carries exactly the same
information as equality of the underlying prefix matrix. -/
def rowPrefixFiberEquiv {c s : Nat} (X : FullRowFrame c (c + s)) :
    RectangularFrameFiberAverage.Fiber (rowPrefixMap c s) X ≃
      PrefixFiber c s X.1 where
  toFun w := ⟨w.1, by
    have h := congrArg Subtype.val w.2
    simpa [rowPrefixMap] using h⟩
  invFun w := ⟨w.1, by
    apply Subtype.ext
    exact w.2⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- Exact normalized row-prefix marginal: the inverse-pair carrier is uniform,
and the image is uniform over every full-row-rank rectangular matrix. The
proof uses equal fibres from explicit transitivity and does not count a fibre
product formula. -/
theorem row_prefix_uniform_mean {c s : Nat}
    (g : FullRowFrame c (c + s) → Real) :
    (∑ p : InversePair (c + s), g (rowPrefixMap c s p)) /
        (Fintype.card (InversePair (c + s)) : Real) =
      (∑ X : FullRowFrame c (c + s), g X) /
        (Fintype.card (FullRowFrame c (c + s)) : Real) := by
  classical
  letI : Fintype (InversePair (c + s)) := Fintype.ofFinite _
  letI : Fintype (FullRowFrame c (c + s)) := Fintype.ofFinite _
  let f := rowPrefixMap c s
  let X₀ : FullRowFrame c (c + s) :=
    ⟨canonicalPrefixMatrix c s, by
      change Function.Surjective
        (Matrix.toLin' (LinearMap.toMatrix' (canonicalPrefixMap c s)))
      rw [Matrix.toLin'_toMatrix']
      exact canonicalPrefixMap_surjective c s⟩
  letI : Nonempty (FullRowFrame c (c + s)) := ⟨X₀⟩
  let k := Fintype.card (RectangularFrameFiberAverage.Fiber f X₀)
  have hf : Function.Surjective f := rowPrefixMap_surjective c s
  have hbase : Nonempty (RectangularFrameFiberAverage.Fiber f X₀) := by
    obtain ⟨p, hp⟩ := hf X₀
    exact ⟨⟨p, hp⟩⟩
  have hk : 0 < k := by
    change 0 < Fintype.card (RectangularFrameFiberAverage.Fiber f X₀)
    exact Fintype.card_pos_iff.mpr hbase
  have hcard : ∀ X : FullRowFrame c (c + s),
      Fintype.card (RectangularFrameFiberAverage.Fiber f X) = k := by
    intro X
    have hXX₀ : PrefixFiber c s X.1 ≃ PrefixFiber c s X₀.1 :=
      prefix_fiber_equiv X.1 X₀.1 X.2 X₀.2
    have hfiber := (rowPrefixFiberEquiv X).trans
      (hXX₀.trans (rowPrefixFiberEquiv X₀).symm)
    simpa [k, f] using Fintype.card_congr hfiber
  simpa [f] using
    (RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers
      f k hk hcard g)

/-- Injective column maps become surjective row maps after transpose. The
proof uses Mathlib's exact `mulVec_injective_iff` and the project row-frame
equivalence, preserving the c=0 case. -/
theorem transpose_of_injective_is_surjective {d c : Nat}
    (M : BinaryMatrix d c)
    (hM : Function.Injective (Matrix.toLin' M)) :
    Function.Surjective (Matrix.toLin' M.transpose) := by
  classical
  have hmul : Function.Injective M.mulVec := by
    intro x y hxy
    apply hM
    simpa [Matrix.toLin'_apply'] using hxy
  have hcols : LinearIndependent (ZMod 2) M.col :=
    Matrix.mulVec_injective_iff.mp hmul
  have hrows : LinearIndependent (ZMod 2) M.transpose.row := by
    simpa [Matrix.row_transpose] using hcols
  have hsurj :=
    ActualFiniteBinarySurjectionCounting.matrix_surjective_iff_rows_independent
      M.transpose
  have hmulSurj : Function.Surjective M.transpose.mulVecLin := hsurj.mpr hrows
  simpa [Matrix.toLin'_apply'] using hmulSurj

/-- The converse transpose bridge, using independent rows to obtain
injective columns. -/
theorem transpose_of_surjective_is_injective {c d : Nat}
    (M : BinaryMatrix c d)
    (hM : Function.Surjective (Matrix.toLin' M)) :
    Function.Injective (Matrix.toLin' M.transpose) := by
  classical
  have hrows :=
    ActualFiniteBinarySurjectionCounting.matrix_surjective_iff_rows_independent
      M
  have hi : LinearIndependent (ZMod 2) M.row := by
    apply hrows.mp
    simpa [Matrix.toLin'_apply'] using hM
  have hcols : LinearIndependent (ZMod 2) M.transpose.col := by
    simpa [Matrix.col_transpose] using hi
  have hmul : Function.Injective M.transpose.mulVec :=
    Matrix.mulVec_injective_iff.mpr hcols
  intro x y hxy
  apply hmul
  simpa [Matrix.toLin'_apply'] using hxy

/-- Transpose identifies full-row and full-column frames in both directions. -/
def rowColumnFrameEquiv {c d : Nat} :
    FullRowFrame c d ≃ {M : BinaryMatrix d c //
      Function.Injective (Matrix.toLin' M)} where
  toFun R := ⟨R.1.transpose, transpose_of_surjective_is_injective R.1 R.2⟩
  invFun C := ⟨C.1.transpose, transpose_of_injective_is_surjective C.1 C.2⟩
  left_inv R := by
    apply Subtype.ext
    simp
  right_inv C := by
    apply Subtype.ext
    simp

/-- Transposition is an involutive bijection of explicit paired-inverse
square matrices, with the two inverse laws reversed as required. -/
def inversePairTranspose (d : Nat) : InversePair d ≃ InversePair d where
  toFun p := ⟨(p.1.1.transpose, p.1.2.transpose), by
    constructor
    · rw [← Matrix.transpose_mul, p.2.2, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, p.2.1, Matrix.transpose_one]⟩
  invFun p := ⟨(p.1.1.transpose, p.1.2.transpose), by
    constructor
    · rw [← Matrix.transpose_mul, p.2.2, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, p.2.1, Matrix.transpose_one]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- The column-prefix map is the transpose of the first-row map on the
transposed paired-inverse matrix. -/
def columnPrefixMap {c s : Nat} :
    InversePair (c + s) → {M : BinaryMatrix (c + s) c //
      Function.Injective (Matrix.toLin' M)} := fun p =>
  rowColumnFrameEquiv (rowPrefixMap c s ((inversePairTranspose (c + s)) p))

/-- Exact normalized full-column marginal. It follows by transposing both the
finite inverse-pair carrier and the full-row frame carrier, then applying the
first-row marginal. This is the all-width GL column-prefix identity. -/
theorem column_prefix_uniform_mean {c s : Nat}
    (g : {M : BinaryMatrix (c + s) c //
      Function.Injective (Matrix.toLin' M)} → Real) :
    (∑ p : InversePair (c + s), g (columnPrefixMap p)) /
        (Fintype.card (InversePair (c + s)) : Real) =
      (∑ C : {M : BinaryMatrix (c + s) c //
        Function.Injective (Matrix.toLin' M)}, g C) /
        (Fintype.card {M : BinaryMatrix (c + s) c //
          Function.Injective (Matrix.toLin' M)} : Real) := by
  classical
  letI : Fintype (InversePair (c + s)) := Fintype.ofFinite _
  letI : Fintype (FullRowFrame c (c + s)) := Fintype.ofFinite _
  letI : Fintype {M : BinaryMatrix (c + s) c //
      Function.Injective (Matrix.toLin' M)} := Fintype.ofFinite _
  let tf := rowColumnFrameEquiv (c := c) (d := c + s)
  let ti := inversePairTranspose (c + s)
  have hrow := row_prefix_uniform_mean
    (fun R : FullRowFrame c (c + s) => g (tf R))
  have hinput :
      (∑ p : InversePair (c + s), g (columnPrefixMap p)) =
        ∑ p : InversePair (c + s), g (tf (rowPrefixMap c s p)) := by
    change (∑ p : InversePair (c + s),
        (fun q => g (tf (rowPrefixMap c s q))) (ti p)) = _
    exact Equiv.sum_comp ti (fun q => g (tf (rowPrefixMap c s q)))
  have houtput :
      (∑ R : FullRowFrame c (c + s), g (tf R)) =
        ∑ C : {M : BinaryMatrix (c + s) c //
          Function.Injective (Matrix.toLin' M)}, g C :=
    Equiv.sum_comp tf g
  have hcard := Fintype.card_congr tf
  rw [hinput, ← houtput, ← hcard]
  exact hrow

/-- The same full-column marginal stated directly on Mathlib's finite GL
carrier. The inverse-pair proof is transported by its explicit equivalence. -/
theorem gl_column_prefix_uniform_mean {c s : Nat}
    (g : {M : BinaryMatrix (c + s) c //
      Function.Injective (Matrix.toLin' M)} → Real) :
    (∑ U : Matrix.GeneralLinearGroup (Fin (c + s)) (ZMod 2),
      g (columnPrefixMap ((inversePairEquivGL (c + s)).symm U))) /
        (Fintype.card (Matrix.GeneralLinearGroup (Fin (c + s)) (ZMod 2)) : Real) =
      (∑ C : {M : BinaryMatrix (c + s) c //
        Function.Injective (Matrix.toLin' M)}, g C) /
        (Fintype.card {M : BinaryMatrix (c + s) c //
          Function.Injective (Matrix.toLin' M)} : Real) := by
  classical
  let e := inversePairEquivGL (c + s)
  have hpair := column_prefix_uniform_mean g
  have hsum :
      (∑ U : Matrix.GeneralLinearGroup (Fin (c + s)) (ZMod 2),
        g (columnPrefixMap (e.symm U))) =
        ∑ p : InversePair (c + s), g (columnPrefixMap p) :=
    Equiv.sum_comp e.symm (fun p => g (columnPrefixMap p))
  have hcard := Fintype.card_congr e
  rw [hsum, ← hcard]
  exact hpair

/-- Right multiplication by a paired-inverse transporter gives an explicit
equivalence between any two fibres of the row-prefix map. The inverse is right
multiplication by the paired inverse; no completion count is assumed. -/
theorem prefix_fiber_equiv_nonempty {c s : Nat}
    (X Y : BinaryMatrix c (c + s))
    (hX : Function.Surjective (Matrix.toLin' X))
    (hY : Function.Surjective (Matrix.toLin' Y)) :
    Nonempty (PrefixFiber c s X ≃ PrefixFiber c s Y) := by
  classical
  have hRange : LinearMap.range (Matrix.toLin' X) =
      LinearMap.range (Matrix.toLin' Y) := by
    rw [LinearMap.range_eq_top.mpr hX, LinearMap.range_eq_top.mpr hY]
  obtain ⟨T, S, hTS, hST, hXY⟩ :=
    same_range_matrix_right_orbit Y X hRange.symm
  refine ⟨{
      toFun := fun w =>
        ⟨⟨(w.1.1.1 * T, S * w.1.1.2), ⟨?_, ?_⟩⟩, ?_⟩
      invFun := fun w =>
        ⟨⟨(w.1.1.1 * S, T * w.1.1.2), ⟨?_, ?_⟩⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }⟩
  · calc
      (w.1.1.1 * T) * (S * w.1.1.2) =
          w.1.1.1 * (T * S) * w.1.1.2 := by simp [Matrix.mul_assoc]
      _ = w.1.1.1 * 1 * w.1.1.2 := by rw [hTS]
      _ = 1 := by simp [w.1.2.1]
  · calc
      (S * w.1.1.2) * (w.1.1.1 * T) =
          S * (w.1.1.2 * w.1.1.1) * T := by simp [Matrix.mul_assoc]
      _ = S * 1 * T := by rw [w.1.2.2]
      _ = 1 := by simp [hST]
  · calc
      canonicalPrefixMatrix c s * (w.1.1.1 * T) =
          (canonicalPrefixMatrix c s * w.1.1.1) * T := by
            simp [Matrix.mul_assoc]
      _ = X * T := by rw [w.2]
      _ = Y := hXY
  · calc
      (w.1.1.1 * S) * (T * w.1.1.2) =
          w.1.1.1 * (S * T) * w.1.1.2 := by simp [Matrix.mul_assoc]
      _ = w.1.1.1 * 1 * w.1.1.2 := by rw [hST]
      _ = 1 := by simp [w.1.2.1]
  · calc
      (T * w.1.1.2) * (w.1.1.1 * S) =
          T * (w.1.1.2 * w.1.1.1) * S := by simp [Matrix.mul_assoc]
      _ = T * 1 * S := by rw [w.1.2.2]
      _ = 1 := by simp [hTS]
  · calc
      canonicalPrefixMatrix c s * (w.1.1.1 * S) =
          (canonicalPrefixMatrix c s * w.1.1.1) * S := by
            simp [Matrix.mul_assoc]
      _ = Y * S := by rw [w.2]
      _ = X := by rw [← hXY, Matrix.mul_assoc, hTS, Matrix.mul_one]
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    ext <;> simp [Matrix.mul_assoc, hTS, hST]
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    ext <;> simp [Matrix.mul_assoc, hTS, hST]

/-- Chosen fibre equivalence, using classical choice only to select the
transporter supplied by the same-range theorem. -/
noncomputable def prefix_fiber_equiv {c s : Nat}
    (X Y : BinaryMatrix c (c + s))
    (hX : Function.Surjective (Matrix.toLin' X))
    (hY : Function.Surjective (Matrix.toLin' Y)) :
    PrefixFiber c s X ≃ PrefixFiber c s Y :=
  Classical.choice (prefix_fiber_equiv_nonempty X Y hX hY)

end
end PvNP.RealizableHardness.RectangularGLRowCompletion
