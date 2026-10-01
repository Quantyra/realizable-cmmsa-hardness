import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18Conditioning
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Exact carrier identity for the expanded branch of the A18 column split.
For a codimension-one extension `B ≤ B'`, every vector outside `B` spans
`B'` together with `B`. This is the typed bridge needed to reindex actual
outside-column maps by their column value.
-/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18SourceConditioning

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18Conditioning

/-- An outside vector in a one-dimensional extension generates the actual
expanded codomain together with the old subspace. -/
theorem spanExtension_eq_of_codim_one
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (B B' : Submodule (ZMod 2) W) (hB : B ≤ B')
    (hdim : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B + 1)
    (w : B') (hw : (w : W) ∉ B) :
    spanExtensionSubmodule B (w : W) = B' := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨b, hb, c, hc, hbc⟩
    rcases Submodule.mem_span_singleton.mp hc with ⟨a, ha⟩
    rw [← hbc, ← ha]
    exact B'.add_mem (hB hb) (B'.smul_mem a w.property)
  · rw [spanExtensionSubmodule, Submodule.finrank_sup_span_singleton hw]
    exact hdim.symm

/-- Partition actual linear maps into fibers of their distinguished column.
This is the exact dependent sum behind the expanded A18 branch; the next
step transports each fiber through the quotient-section coordinates. -/
noncomputable def outsideColumnSigmaEquiv
    {X W : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B B' : Submodule (ZMod 2) W) (hB : B ≤ B') (v : X) :
    {F : X →ₗ[ZMod 2] B' // (F v : W) ∉ B} ≃
      Σ w : {w : B' // (w : W) ∉ B},
        {F : X →ₗ[ZMod 2] B' // F v = w} where
  toFun F := ⟨⟨F.1 v, F.2⟩, ⟨F.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by simpa only [p.2.2] using p.1.2⟩
  left_inv F := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨w, F⟩
    rcases F with ⟨F, hF⟩
    apply Sigma.ext
    · exact hF.symm
    · apply Subtype.ext
      rfl

/-- Exact finite sum reindexing for the outside-column event, with the
column value kept as the dependent sigma index. -/
theorem outsideColumnSigma_sum
    {X W : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype X] [Fintype W]
    (B B' : Submodule (ZMod 2) W) (hB : B ≤ B') (v : X)
    (g : {F : X →ₗ[ZMod 2] B' // (F v : W) ∉ B} → ℝ) :
    (∑ F : {F : X →ₗ[ZMod 2] B' // (F v : W) ∉ B}, g F) =
      ∑ p : Σ w : {w : B' // (w : W) ∉ B},
          {F : X →ₗ[ZMod 2] B' // F v = w},
        g ((outsideColumnSigmaEquiv B B' hB v).symm p) := by
  classical
  exact (Equiv.sum_comp (outsideColumnSigmaEquiv B B' hB v).symm
    (fun F => g F)).symm

/-- Normalized outside-column averaging is exactly averaging first over the
column and then its map fiber. No branch-mass or energy hypothesis is used. -/
theorem outsideColumnSigma_mean
    {X W : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype X] [Fintype W]
    (B B' : Submodule (ZMod 2) W) (hB : B ≤ B') (v : X)
    (g : {F : X →ₗ[ZMod 2] B' // (F v : W) ∉ B} → ℝ) :
    (∑ F : {F : X →ₗ[ZMod 2] B' // (F v : W) ∉ B}, g F) /
        (Fintype.card {F : X →ₗ[ZMod 2] B' // (F v : W) ∉ B} : ℝ) =
      (∑ p : Σ w : {w : B' // (w : W) ∉ B},
          {F : X →ₗ[ZMod 2] B' // F v = w},
        g ((outsideColumnSigmaEquiv B B' hB v).symm p)) /
        (Fintype.card (Σ w : {w : B' // (w : W) ∉ B},
          {F : X →ₗ[ZMod 2] B' // F v = w}) : ℝ) := by
  rw [outsideColumnSigma_sum B B' hB v g,
    Fintype.card_congr (outsideColumnSigmaEquiv B B' hB v)]

end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18SourceConditioning
