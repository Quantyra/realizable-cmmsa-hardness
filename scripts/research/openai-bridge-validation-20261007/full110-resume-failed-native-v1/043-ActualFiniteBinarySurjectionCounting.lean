import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.GrassmannCounting

/-!
Exact finite count of surjective binary linear maps between coordinate spaces.

The proof identifies a matrix map with its ordered family of rows, proves that
surjectivity is equivalent to row independence using the rank/range identities,
and applies the finite-field independent-frame count.  Dimensions are separate
parameters; in particular, the out-of-range case is included by the frame
count theorem's `i ≤ d` guard.
-/

namespace PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting

open PvNP.RealizableHardness.GrassmannCounting

open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev BinaryCoordinateSpace (n : Nat) := Fin n → ZMod 2

/-- Row independence characterizes surjectivity of the associated matrix map. -/
theorem matrix_surjective_iff_rows_independent {d i : Nat}
    (A : Matrix (Fin i) (Fin d) (ZMod 2)) :
    Function.Surjective A.mulVecLin ↔ LinearIndependent (ZMod 2) A.row := by
  classical
  have hrankRange : A.rank =
      Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) := by
    rfl
  have hcod : Module.finrank (ZMod 2) (Fin i → ZMod 2) = i := by
    simp
  have hsurjRank : Function.Surjective A.mulVecLin ↔ A.rank = i := by
    rw [← LinearMap.range_eq_top]
    constructor
    · intro h
      rw [h] at hrankRange
      simpa [hcod] using hrankRange
    · intro h
      apply (Submodule.eq_top_iff_finrank_eq).2
      rw [← hrankRange, h]
      exact hcod.symm
  have hrowRank : LinearIndependent (ZMod 2) A.row ↔ A.rank = i := by
    constructor
    · intro h
      simpa [Fintype.card_fin] using h.rank_matrix
    · intro h
      rw [Matrix.rank_eq_finrank_span_row] at h
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      simpa [Fintype.card_fin, Set.finrank] using h.symm
  exact hsurjRank.trans hrowRank.symm

/-- Surjective maps represented by `i × d` matrices are exactly independent
ordered `i`-frames in the `d`-dimensional binary coordinate space. -/
def surjectiveMatrixFrameEquiv (d i : Nat) :
    {A : Matrix (Fin i) (Fin d) (ZMod 2) // Function.Surjective A.mulVecLin} ≃
      Frame (BinaryCoordinateSpace d) i := by
  classical
  exact (Equiv.refl (Matrix (Fin i) (Fin d) (ZMod 2))).subtypeEquiv
    (fun A => by
      change Function.Surjective A.mulVecLin ↔
        LinearIndependent (ZMod 2) (fun j => A j)
      simpa [Matrix.row] using matrix_surjective_iff_rows_independent A)

/-- Exact number of surjective linear maps between finite binary coordinate
spaces.  If the target dimension exceeds the source dimension, the subtype is
empty and `frameProduct` is the corresponding zero product. -/
theorem card_surjective_coordinate_maps (d i : Nat) :
    Nat.card
      {f : BinaryCoordinateSpace d →ₗ[ZMod 2] BinaryCoordinateSpace i //
        Function.Surjective f} = frameProduct d i := by
  classical
  let : Fintype {A : Matrix (Fin i) (Fin d) (ZMod 2) //
      Function.Surjective A.mulVecLin} := Fintype.ofFinite _
  let e : {A : Matrix (Fin i) (Fin d) (ZMod 2) // Function.Surjective A.mulVecLin} ≃
      {f : BinaryCoordinateSpace d →ₗ[ZMod 2] BinaryCoordinateSpace i //
        Function.Surjective f} :=
    (Matrix.toLin' : Matrix (Fin i) (Fin d) (ZMod 2) ≃ₗ[ZMod 2]
      (BinaryCoordinateSpace d →ₗ[ZMod 2] BinaryCoordinateSpace i)).toEquiv.subtypeEquiv
      (fun A => by
        change Function.Surjective (Matrix.toLin' A) ↔
          Function.Surjective A.mulVecLin
        simp [Matrix.toLin'_apply'])
  have hmaps : Nat.card
      {f : BinaryCoordinateSpace d →ₗ[ZMod 2] BinaryCoordinateSpace i //
        Function.Surjective f} =
      Fintype.card {A : Matrix (Fin i) (Fin d) (ZMod 2) //
        Function.Surjective A.mulVecLin} := by
    calc
      Nat.card {f : BinaryCoordinateSpace d →ₗ[ZMod 2] BinaryCoordinateSpace i //
          Function.Surjective f} = Nat.card
          {A : Matrix (Fin i) (Fin d) (ZMod 2) //
            Function.Surjective A.mulVecLin} := Nat.card_congr e.symm
      _ = Fintype.card {A : Matrix (Fin i) (Fin d) (ZMod 2) //
          Function.Surjective A.mulVecLin} := Nat.card_eq_fintype_card
  have hframes : Fintype.card
      {A : Matrix (Fin i) (Fin d) (ZMod 2) // Function.Surjective A.mulVecLin} =
      Fintype.card (Frame (BinaryCoordinateSpace d) i) :=
    Fintype.card_congr (surjectiveMatrixFrameEquiv d i)
  rw [hmaps, hframes]
  by_cases hi : i ≤ d
  · have hi' : i ≤ Module.finrank (ZMod 2) (BinaryCoordinateSpace d) := by
      simpa [BinaryCoordinateSpace] using hi
    simpa [BinaryCoordinateSpace] using
      (card_frame (V := BinaryCoordinateSpace d) (a := i) hi')
  · have hd : d < i := Nat.lt_of_not_ge hi
    have hzero : Fintype.card (Frame (BinaryCoordinateSpace d) i) = 0 := by
      let : IsEmpty (Frame (BinaryCoordinateSpace d) i) := ⟨fun f => by
        have hle := f.property.fintype_card_le_finrank
        have hle' : i ≤ d := by simpa [BinaryCoordinateSpace] using hle
        exact (Nat.not_le_of_gt hd) hle'⟩
      simp
    have hprod : frameProduct d i = 0 := by
      unfold frameProduct
      apply Finset.prod_eq_zero (Finset.mem_univ ⟨d, hd⟩)
      simp
    rw [hzero, hprod]

/-- Coordinates on an arbitrary finite-dimensional binary space. -/
noncomputable def binaryCoordinateEquiv (V : Type*)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [FiniteDimensional (ZMod 2) V] :
    V ≃ₗ[ZMod 2] BinaryCoordinateSpace (Module.finrank (ZMod 2) V) :=
  (Module.finBasis (ZMod 2) V).equivFun

/-- Transport a linear map across coordinate equivalences on its domain and
codomain. -/
def linearMapCoordinateEquiv {V W X Y : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (eV : V ≃ₗ[ZMod 2] X) (eW : W ≃ₗ[ZMod 2] Y) :
    (V →ₗ[ZMod 2] W) ≃ (X →ₗ[ZMod 2] Y) where
  toFun f := eW.toLinearMap.comp (f.comp eV.symm.toLinearMap)
  invFun g := eW.symm.toLinearMap.comp (g.comp eV.toLinearMap)
  left_inv f := by
    ext v
    simp
  right_inv g := by
    ext x
    simp

theorem linearMapCoordinateEquiv_surjective_iff {V W X Y : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (eV : V ≃ₗ[ZMod 2] X) (eW : W ≃ₗ[ZMod 2] Y)
    (f : V →ₗ[ZMod 2] W) :
    Function.Surjective f ↔
      Function.Surjective (linearMapCoordinateEquiv eV eW f) := by
  constructor
  · intro hf y
    obtain ⟨w, hw⟩ := hf (eW.symm y)
    refine ⟨eV w, ?_⟩
    simp [linearMapCoordinateEquiv, hw]
  · intro hg y
    obtain ⟨x, hx⟩ := hg (eW y)
    refine ⟨eV.symm x, ?_⟩
    apply eW.injective
    simpa [linearMapCoordinateEquiv] using hx

/-- Exact surjection count for any finite-dimensional binary vector spaces;
the formula depends only on their separate source and target dimensions. -/
theorem card_surjective_linear_maps
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [FiniteDimensional (ZMod 2) W] :
    Nat.card {f : V →ₗ[ZMod 2] W // Function.Surjective f} =
      frameProduct (Module.finrank (ZMod 2) V) (Module.finrank (ZMod 2) W) := by
  classical
  let eV := binaryCoordinateEquiv V
  let eW := binaryCoordinateEquiv W
  let e :
      {f : V →ₗ[ZMod 2] W // Function.Surjective f} ≃
        {g : BinaryCoordinateSpace (Module.finrank (ZMod 2) V) →ₗ[ZMod 2]
          BinaryCoordinateSpace (Module.finrank (ZMod 2) W) // Function.Surjective g} :=
    (linearMapCoordinateEquiv eV eW).subtypeEquiv
    (fun f => linearMapCoordinateEquiv_surjective_iff eV eW f)
  rw [Nat.card_congr e]
  exact card_surjective_coordinate_maps
    (Module.finrank (ZMod 2) V) (Module.finrank (ZMod 2) W)

end
end PvNP.RealizableHardness.ActualFiniteBinarySurjectionCounting
