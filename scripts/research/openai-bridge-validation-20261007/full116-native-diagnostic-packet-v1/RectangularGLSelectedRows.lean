import PvNP.RealizableHardness.RectangularGLRowCompletion

/-!
Selector-parametric form of rectangular completion and uniform row marginals.
The selector need only be onto as a linear map; coordinate selectors are
handled by `LinearMap.funLeft_surjective_of_injective`. This is the path for
the bottom-s-row law used by the restricted-adjoint argument.
-/
namespace PvNP.RealizableHardness.RectangularGLSelectedRows

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixRightOrbit
open PvNP.RealizableHardness.RectangularGLRowCompletion

set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

abbrev SelectedFiber {k d : Nat} (P : BinaryMatrix k d)
    (X : BinaryMatrix k d) :=
  {U : InversePair d // P * U.1.1 = X}

/-- Apply any surjective rectangular row selector to the first matrix in a
paired-inverse GL representative. -/
def selectedRowsMap {k d : Nat} (P : BinaryMatrix k d)
    (hP : Function.Surjective (Matrix.toLin' P)) :
    InversePair d → FullRowFrame k d := fun U =>
  ⟨P * U.1.1, by
    have hU : Function.Surjective (Matrix.toLin' U.1.1) := by
      intro x
      refine ⟨Matrix.toLin' U.1.2 x, ?_⟩
      have hUV : (Matrix.toLin' U.1.1).comp (Matrix.toLin' U.1.2) =
          LinearMap.id := by
        rw [← Matrix.toLin'_mul, U.2.1, Matrix.toLin'_one]
      exact congrArg (fun f => f x) hUV
    change Function.Surjective (Matrix.toLin' (P * U.1.1))
    rw [Matrix.toLin'_mul]
    exact hP.comp hU⟩

/-- Complete any full-row-rank rectangular matrix relative to any fixed
surjective selector P. The selector itself need not be a coordinate block. -/
theorem exists_selected_completion {k d : Nat}
    (P M : BinaryMatrix k d)
    (hP : Function.Surjective (Matrix.toLin' P))
    (hM : Function.Surjective (Matrix.toLin' M)) :
    ∃ U V : BinaryMatrix d d,
      U * V = 1 ∧ V * U = 1 ∧ P * U = M := by
  have hRange : LinearMap.range (Matrix.toLin' M) =
      LinearMap.range (Matrix.toLin' P) := by
    rw [LinearMap.range_eq_top.mpr hM, LinearMap.range_eq_top.mpr hP]
  obtain ⟨U, V, hUV, hVU, hPU⟩ :=
    same_range_matrix_right_orbit M P hRange
  exact ⟨U, V, hUV, hVU, hPU⟩

/-- Every target row frame occurs in the selected-row map. -/
theorem selectedRowsMap_surjective {k d : Nat} (P : BinaryMatrix k d)
    (hP : Function.Surjective (Matrix.toLin' P)) :
    Function.Surjective (selectedRowsMap P hP) := by
  intro X
  obtain ⟨U, V, hUV, hVU, hPU⟩ := exists_selected_completion P X.1 hP X.2
  refine ⟨⟨(U, V), ⟨hUV, hVU⟩⟩, ?_⟩
  apply Subtype.ext
  exact hPU

/-- Explicit paired-inverse transporter equivalence between arbitrary
selected-row fibres. -/
theorem selectedFiber_equiv_nonempty {k d : Nat}
    (P X Y : BinaryMatrix k d)
    (hX : Function.Surjective (Matrix.toLin' X))
    (hY : Function.Surjective (Matrix.toLin' Y)) :
    Nonempty (SelectedFiber P X ≃ SelectedFiber P Y) := by
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
      P * (w.1.1.1 * T) = (P * w.1.1.1) * T := by simp [Matrix.mul_assoc]
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
      P * (w.1.1.1 * S) = (P * w.1.1.1) * S := by simp [Matrix.mul_assoc]
      _ = Y * S := by rw [w.2]
      _ = X := by rw [← hXY, Matrix.mul_assoc, hTS, Matrix.mul_one]
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · calc
        (w.1.1.1 * T) * S = w.1.1.1 * (T * S) := by rw [Matrix.mul_assoc]
        _ = w.1.1.1 * 1 := by rw [hTS]
        _ = w.1.1.1 := by simp
    · calc
        T * (S * w.1.1.2) = (T * S) * w.1.1.2 := by rw [← Matrix.mul_assoc]
        _ = 1 * w.1.1.2 := by rw [hTS]
        _ = w.1.1.2 := by simp
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · calc
        (w.1.1.1 * S) * T = w.1.1.1 * (S * T) := by rw [Matrix.mul_assoc]
        _ = w.1.1.1 * 1 := by rw [hST]
        _ = w.1.1.1 := by simp
    · calc
        S * (T * w.1.1.2) = (S * T) * w.1.1.2 := by rw [← Matrix.mul_assoc]
        _ = 1 * w.1.1.2 := by rw [hST]
        _ = w.1.1.2 := by simp

noncomputable def selectedFiber_equiv {k d : Nat}
    (P X Y : BinaryMatrix k d)
    (hX : Function.Surjective (Matrix.toLin' X))
    (hY : Function.Surjective (Matrix.toLin' Y)) :
    SelectedFiber P X ≃ SelectedFiber P Y :=
  Classical.choice (selectedFiber_equiv_nonempty P X Y hX hY)

def selectedMapFiberEquiv {k d : Nat} (P : BinaryMatrix k d)
    (hP : Function.Surjective (Matrix.toLin' P))
    (X : FullRowFrame k d) :
    RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X ≃
      SelectedFiber P X.1 where
  toFun w := ⟨w.1, by
    have h := congrArg Subtype.val w.2
    simpa [selectedRowsMap] using h⟩
  invFun w := ⟨w.1, by
    apply Subtype.ext
    exact w.2⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

private noncomputable def selectedMap_fiber_equiv {k d : Nat}
    (P : BinaryMatrix k d) (hP : Function.Surjective (Matrix.toLin' P))
    (X Y : FullRowFrame k d) :
    RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X ≃
      RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) Y := by
  let hX : RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X ≃
      SelectedFiber P X.1 := selectedMapFiberEquiv P hP X
  let hXY : SelectedFiber P X.1 ≃ SelectedFiber P Y.1 :=
    selectedFiber_equiv P X.1 Y.1 X.2 Y.2
  let hY : RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) Y ≃
      SelectedFiber P Y.1 := selectedMapFiberEquiv P hP Y
  exact hX.trans (hXY.trans hY.symm)

private theorem selectedMap_fiber_card_eq {k d : Nat}
    (P : BinaryMatrix k d) (hP : Function.Surjective (Matrix.toLin' P))
    (X Y : FullRowFrame k d) :
    Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X) =
      Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) Y) := by
  exact Fintype.card_congr (selectedMap_fiber_equiv P hP X Y)

/-- The normalized selected-row marginal for every surjective selector P.
This specializes to first rows and to the bottom s rows without reindexing
Fin (c+s) as Fin (s+c). -/
theorem selected_rows_uniform_mean {k d : Nat}
    (P : BinaryMatrix k d)
    (hP : Function.Surjective (Matrix.toLin' P))
    (g : FullRowFrame k d → Real) :
    (∑ U : InversePair d, g (selectedRowsMap P hP U)) /
        (Fintype.card (InversePair d) : Real) =
      (∑ X : FullRowFrame k d, g X) /
        (Fintype.card (FullRowFrame k d) : Real) := by
  classical
  let f : InversePair d → FullRowFrame k d := selectedRowsMap P hP
  let X₀ : FullRowFrame k d := ⟨P, hP⟩
  let k₀ := Fintype.card (RectangularFrameFiberAverage.Fiber f X₀)
  have hf : Function.Surjective f := selectedRowsMap_surjective P hP
  have hbase : Nonempty (RectangularFrameFiberAverage.Fiber f X₀) := by
    obtain ⟨U, hU⟩ := hf X₀
    exact ⟨⟨U, hU⟩⟩
  have hk₀ : 0 < k₀ := by
    change 0 < Fintype.card (RectangularFrameFiberAverage.Fiber f X₀)
    exact Fintype.card_pos_iff.mpr hbase
  let hNonempty : Nonempty (FullRowFrame k d) := ⟨X₀⟩
  have hcard : ∀ X : FullRowFrame k d,
      Fintype.card (RectangularFrameFiberAverage.Fiber f X) = k₀ := by
    intro X
    change Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X) =
      Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X₀)
    exact selectedMap_fiber_card_eq P hP X X₀
  have hcardNat : ∀ X : FullRowFrame k d,
      Nat.card (RectangularFrameFiberAverage.Fiber f X) = k₀ := by
    intro X
    simpa only [← Nat.card_eq_fintype_card] using hcard X
  have hmap :
      (∑ U : InversePair d, g (f U)) / (Fintype.card (InversePair d) : Real) =
        (∑ X : FullRowFrame k d, g X) / (Fintype.card (FullRowFrame k d) : Real) :=
    @RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers
      (InversePair d) (FullRowFrame k d)
      inferInstance inferInstance hNonempty f k₀ hk₀
      (by
        intro X
        simpa only [← Nat.card_eq_fintype_card] using hcardNat X)
      g
  exact hmap

/-- Direct bottom-s-row selector. -/
def bottomRowsMap (c s : Nat) :
    (Fin (c + s) → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd c)

def bottomRowsMatrix (c s : Nat) : BinaryMatrix s (c + s) :=
  LinearMap.toMatrix' (bottomRowsMap c s)

theorem bottomRowsMap_surjective (c s : Nat) :
    Function.Surjective (Matrix.toLin' (bottomRowsMatrix c s)) := by
  change Function.Surjective
    (Matrix.toLin' (LinearMap.toMatrix' (bottomRowsMap c s)))
  rw [Matrix.toLin'_toMatrix']
  unfold bottomRowsMap
  apply LinearMap.funLeft_surjective_of_injective
  intro i j h
  exact Fin.ext (by simpa using congrArg Fin.val h)

/-- The GL bottom-s-row marginal, with the original s-by-(c+s) frame carrier. -/
theorem bottom_rows_uniform_mean {c s : Nat}
    (g : FullRowFrame s (c + s) → Real) :
    (∑ U : InversePair (c + s),
      g (selectedRowsMap (bottomRowsMatrix c s) (bottomRowsMap_surjective c s) U)) /
        (Fintype.card (InversePair (c + s)) : Real) =
      (∑ C : FullRowFrame s (c + s), g C) /
        (Fintype.card (FullRowFrame s (c + s)) : Real) := by
  exact selected_rows_uniform_mean (bottomRowsMatrix c s)
    (bottomRowsMap_surjective c s) g

/-- Swap a paired matrix and its inverse. This is the actual inversion map on
the finite GL carrier, with both inverse identities retained. -/
def inversePairSwap (d : Nat) : InversePair d ≃ InversePair d where
  toFun p := ⟨(p.1.2, p.1.1), ⟨p.2.2, p.2.1⟩⟩
  invFun p := ⟨(p.1.2, p.1.1), ⟨p.2.2, p.2.1⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-- The bottom s rows of the inverse matrix, which are the rows required by
the exact restricted-adjoint block calculation. -/
def bottomInverseRowsMap {c s : Nat} (U : InversePair (c + s)) :
    FullRowFrame s (c + s) :=
  selectedRowsMap (bottomRowsMatrix c s)
    (bottomRowsMap_surjective c s) (inversePairSwap (c + s) U)

/-- Inversion preserves the uniform finite GL law; hence the bottom-s rows of
U^{-1} have the same exact uniform full-row-frame marginal as bottom-s rows
of U. This keeps s=0 and c=0 in the same argument. -/
theorem bottom_inverse_rows_uniform_mean {c s : Nat}
    (g : FullRowFrame s (c + s) → Real) :
    (∑ U : InversePair (c + s), g (bottomInverseRowsMap U)) /
        (Fintype.card (InversePair (c + s)) : Real) =
      (∑ C : FullRowFrame s (c + s), g C) /
        (Fintype.card (FullRowFrame s (c + s)) : Real) := by
  classical
  let e := inversePairSwap (c + s)
  have hsum :
      (∑ U : InversePair (c + s), g (bottomInverseRowsMap U)) =
        ∑ p : InversePair (c + s),
          g (selectedRowsMap (bottomRowsMatrix c s)
            (bottomRowsMap_surjective c s) p) := by
    exact Equiv.sum_comp e.symm
      (fun p => g (selectedRowsMap (bottomRowsMatrix c s)
        (bottomRowsMap_surjective c s) p))
  rw [hsum]
  exact bottom_rows_uniform_mean g

end
end PvNP.RealizableHardness.RectangularGLSelectedRows
