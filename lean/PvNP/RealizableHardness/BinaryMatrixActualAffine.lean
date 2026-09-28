import PvNP.RealizableHardness.BinaryMatrixLineA15
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace PvNP.RealizableHardness.BinaryMatrixActualAffine

open BinaryMatrixFourier BinaryMatrixLineA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Intrinsic manuscript affine restriction: fix a domain subspace A,
allow variation only inside codomain subspace B, and fix one base matrix T.
The fibre is the affine coset T + Hom(V/A,B) without a chosen basis. -/
structure ActualAffineRestriction (n d : ℕ) where
  domainFixed : Submodule (ZMod 2) (Fin d → ZMod 2)
  codomainVariation : Submodule (ZMod 2) (Fin n → ZMod 2)
  base : BinaryMatrix n d

def ActualAffineRestriction.order {n d : ℕ}
    (Q : ActualAffineRestriction n d) : ℕ :=
  Module.finrank (ZMod 2) Q.domainFixed +
    Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ Q.codomainVariation)

def ActualAffineRestriction.fibre {n d : ℕ}
    (Q : ActualAffineRestriction n d) : Finset (BinaryMatrix n d) :=
  Finset.univ.filter (fun M =>
    (∀ a ∈ Q.domainFixed, (M - Q.base).mulVec a = 0) ∧
    (∀ v : Fin d → ZMod 2,
      (M - Q.base).mulVec v ∈ Q.codomainVariation))

def UpToActualSquareGlobal {n d : ℕ} (r : ℕ) (ε : ℝ)
    (f : BinaryMatrix n d → ℝ) : Prop :=
  ∀ Q : ActualAffineRestriction n d, Q.order ≤ r →
    (∑ M ∈ Q.fibre, f M ^ 2) / Q.fibre.card ≤ ε

/-- The actual domain-fixed and codomain-variation subspaces represented
by a consistent raw system, with the chosen solution as its affine base. -/
def actualOfRaw {n d : ℕ} (R : AffineRestriction n d)
    (T : BinaryMatrix n d) : ActualAffineRestriction n d where
  domainFixed := LinearMap.range R.rightDirections.mulVecLin
  codomainVariation := LinearMap.ker R.leftDirections.mulVecLin
  base := T

theorem actualOfRaw_order_le_budget {n d : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d) :
    (actualOfRaw R T).order ≤ R.budget := by
  have hA := R.rightDirections.mulVecLin.finrank_range_le
  have hB : Module.finrank (ZMod 2)
      (LinearMap.range R.leftDirections.mulVecLin) ≤ R.rows := by
    change R.leftDirections.rank ≤ R.rows
    simpa using R.leftDirections.rank_le_card_height
  have hquot : Module.finrank (ZMod 2)
      ((Fin n → ZMod 2) ⧸ LinearMap.ker R.leftDirections.mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.range R.leftDirections.mulVecLin) := by
    exact LinearEquiv.finrank_eq R.leftDirections.mulVecLin.quotKerEquivRange
  unfold actualOfRaw ActualAffineRestriction.order AffineRestriction.budget
  rw [hquot]
  simpa using Nat.add_le_add hA hB

private theorem right_eq_iff_range {n d : ℕ}
    (R : AffineRestriction n d) (T M : BinaryMatrix n d) :
    M * R.rightDirections = T * R.rightDirections ↔
      ∀ a ∈ LinearMap.range R.rightDirections.mulVecLin,
        (M - T).mulVec a = 0 := by
  constructor
  · intro h a ha
    obtain ⟨v, rfl⟩ := ha
    have hv := congrArg (fun X : Matrix (Fin n) (Fin R.columns) (ZMod 2) =>
      X.mulVec v) h
    change (M - T).mulVec (R.rightDirections.mulVec v) = 0
    rw [Matrix.sub_mulVec]
    apply sub_eq_zero.mpr
    calc
      M.mulVec (R.rightDirections.mulVec v) =
          (M * R.rightDirections).mulVec v := Matrix.mulVec_mulVec v M R.rightDirections
      _ = (T * R.rightDirections).mulVec v := hv
      _ = T.mulVec (R.rightDirections.mulVec v) :=
        (Matrix.mulVec_mulVec v T R.rightDirections).symm
  · intro h
    apply Matrix.mulVec_injective
    funext v
    have hv := h (R.rightDirections.mulVec v) ⟨v, rfl⟩
    rw [Matrix.sub_mulVec] at hv
    simpa only [← Matrix.mulVec_mulVec] using (sub_eq_zero.mp hv)

private theorem left_eq_iff_kernel {n d : ℕ}
    (R : AffineRestriction n d) (T M : BinaryMatrix n d) :
    R.leftDirections * M = R.leftDirections * T ↔
      ∀ v : Fin d → ZMod 2,
        (M - T).mulVec v ∈ LinearMap.ker R.leftDirections.mulVecLin := by
  constructor
  · intro h v
    change R.leftDirections.mulVec ((M - T).mulVec v) = 0
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
    apply sub_eq_zero.mpr
    calc
      R.leftDirections.mulVec (M.mulVec v) =
          (R.leftDirections * M).mulVec v :=
            Matrix.mulVec_mulVec v R.leftDirections M
      _ = (R.leftDirections * T).mulVec v :=
        congrArg (fun X : Matrix (Fin R.rows) (Fin d) (ZMod 2) => X.mulVec v) h
      _ = R.leftDirections.mulVec (T.mulVec v) :=
        (Matrix.mulVec_mulVec v R.leftDirections T).symm
  · intro h
    apply Matrix.mulVec_injective
    funext v
    have hv := h v
    change R.leftDirections.mulVec ((M - T).mulVec v) = 0 at hv
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub] at hv
    have hveq := sub_eq_zero.mp hv
    calc
      (R.leftDirections * M).mulVec v =
          R.leftDirections.mulVec (M.mulVec v) :=
            (Matrix.mulVec_mulVec v R.leftDirections M).symm
      _ = R.leftDirections.mulVec (T.mulVec v) := hveq
      _ = (R.leftDirections * T).mulVec v :=
        Matrix.mulVec_mulVec v R.leftDirections T

/-- A consistent raw pair of equation systems has exactly the intrinsic
affine coset fixed on the range of its right directions and varying in
the kernel of its left directions. Equality of fibres preserves the
uniform conditional measure without a basis choice. -/
theorem actualOfRaw_fibre {n d : ℕ}
    (R : AffineRestriction n d) (T : BinaryMatrix n d)
    (hT : T ∈ R.fibre) :
    (actualOfRaw R T).fibre = R.fibre := by
  have ⟨hTr, hTl⟩ := (Finset.mem_filter.mp hT).2
  ext M
  constructor
  · intro hM
    have ⟨hA, hB⟩ := (Finset.mem_filter.mp hM).2
    have hr := (right_eq_iff_range R T M).mpr hA
    have hl := (left_eq_iff_kernel R T M).mpr hB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨hr.trans hTr, hl.trans hTl⟩⟩
  · intro hM
    have ⟨hMr, hMl⟩ := (Finset.mem_filter.mp hM).2
    have hr := (right_eq_iff_range R T M).mp (hMr.trans hTr.symm)
    have hl := (left_eq_iff_kernel R T M).mp (hMl.trans hTl.symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hr, hl⟩⟩

/-- Every actual affine restriction of order at most r is controlled by
the manuscript up-to-r premise. A nonempty raw system represents one
such actual restriction with identical uniform fibre and no greater
order; an inconsistent raw system has zero normalized square mean. -/
theorem upToActual_implies_upToRaw {n d r : ℕ} {ε : ℝ}
    (f : BinaryMatrix n d → ℝ) (hε : 0 ≤ ε)
    (hf : UpToActualSquareGlobal r ε f) :
    UpToRawSquareGlobal r ε f := by
  intro R hR
  by_cases hne : R.fibre.Nonempty
  · obtain ⟨T, hT⟩ := hne
    let Q := actualOfRaw R T
    have heq : Q.fibre = R.fibre := actualOfRaw_fibre R T hT
    rw [← heq]
    exact hf Q (le_trans (actualOfRaw_order_le_budget R T) hR)
  · have hempty : R.fibre = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, hε]

/-- The manuscript actual up-to-order premise discharges the raw
premise of the fixed-base A15 inequality. The conclusion is stated
on raw reduced restrictions; the reverse raw-to-actual output bridge
remains separate. -/
theorem actualGlobal_A15_fixedBase_rawOutput {n d k : ℕ}
    {ε : ℝ} (t : Fin n → ZMod 2)
    (f : BinaryMatrix n (d + 1) → ℝ)
    (hε : 0 ≤ ε)
    (hf : UpToActualSquareGlobal (k + 1) ε f) :
    UpToRawSquareGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (BinaryMatrixHybridSelector.rawLastColumnRestrict t
        (BinaryMatrixLineTranslation.lineP k f)) := by
  exact upToRawSquareGlobal_A15_fixedBase t f hε
    (upToActual_implies_upToRaw f hε hf)

end
end PvNP.RealizableHardness.BinaryMatrixActualAffine
