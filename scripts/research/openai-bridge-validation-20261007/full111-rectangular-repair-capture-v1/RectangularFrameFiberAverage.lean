import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import PvNP.RealizableHardness.ActualFiniteFrameProductDuality

/-!
The finite-fibre averaging identity used by a rectangular GL marginal.
This is a candidate generic finite-sum proof, not the matrix-completion
theorem itself and not an accepted independent milestone. The actual GL
prefix map must be shown onto with pairwise equivalent fibres in a native
check before any proof claim is made.
-/

namespace PvNP.RealizableHardness.RectangularFrameFiberAverage

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Fiber {A B : Type*} (f : A → B) (b : B) := {a : A // f a = b}

/-- The disjoint union of the fibers of `f` is equivalent to its domain.
Both inverse laws are explicit, so no surjectivity assumption is hidden. -/
def sigmaFiberEquiv {A B : Type*} (f : A → B) :
    (Σ b : B, Fiber f b) ≃ A where
  toFun p := p.2.1
  invFun a := ⟨f a, ⟨a, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨b, ⟨a, hab⟩⟩
    subst b
    rfl
  right_inv a := rfl

/-- Group a function sum by its fibers when all fibers have the same finite
cardinality. This is the exact unnormalized counting identity. -/
theorem sum_comp_eq_card_mul_sum {A B : Type*}
    [Fintype A] [Fintype B] (f : A → B) (k : Nat)
    (hcard : ∀ b : B, Fintype.card (Fiber f b) = k)
    (g : B → Real) :
    (∑ a : A, g (f a)) = (k : Real) * ∑ b : B, g b := by
  classical
  calc
    (∑ a : A, g (f a)) =
        ∑ p : Σ b : B, Fiber f b, g (f (sigmaFiberEquiv f p)) := by
          exact (Equiv.sum_comp (sigmaFiberEquiv f) (fun a => g (f a))).symm
    _ = ∑ p : Σ b : B, Fiber f b, g p.1 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact congrArg g p.2.2
    _ = ∑ b : B, ∑ a : Fiber f b, g b := by
          simp only [Fintype.sum_sigma]
    _ = ∑ b : B, (k : Real) * g b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [← hcard b]
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (k : Real) * ∑ b : B, g b := by
          rw [Finset.mul_sum]

/-- Exact normalized pushforward: if a surjective finite map has equipotent
fibres, its uniform law pushes forward to the uniform law on the codomain.
The positive fibre-size premise is explicit so both normalizers are nonzero. -/
theorem uniformMean_map_of_equipotent_fibers {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B) (k : Nat) (hk : 0 < k)
    (hcard : ∀ b : B, Fintype.card (Fiber f b) = k)
    (g : B → Real) :
    (∑ a : A, g (f a)) / (Fintype.card A : Real) =
      (∑ b : B, g b) / (Fintype.card B : Real) := by
  classical
  have htotal : Fintype.card A = Fintype.card B * k := by
    calc
      Fintype.card A = Fintype.card (Σ b : B, Fiber f b) :=
        (Fintype.card_congr (sigmaFiberEquiv f)).symm
      _ = ∑ b : B, Fintype.card (Fiber f b) := Fintype.card_sigma
      _ = Fintype.card B * k := by
        simp_rw [hcard]
        simp [Finset.sum_const]
  have hsum := sum_comp_eq_card_mul_sum f k hcard g
  have hA : (Fintype.card A : Real) ≠ 0 := by
    rw [htotal]
    exact_mod_cast (ne_of_gt (Nat.mul_pos (Fintype.card_pos) hk))
  have hB : (Fintype.card B : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card B))
  have hkR : (k : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  rw [hsum, htotal]
  push_cast
  field_simp

/-- Mathlib's ordered independent-frame count specialized to binary coordinate
space, in the exact `frameProduct` notation used by the manuscript. -/
theorem card_binary_rectangular_frames (d c : Nat) (hc : c ≤ d) :
    Fintype.card (Frame (Fin d → ZMod 2) c) = frameProduct d c := by
  classical
  have hfinrank : c ≤ Module.finrank (ZMod 2) (Fin d → ZMod 2) := by
    simpa using hc
  simpa using (card_frame (V := Fin d → ZMod 2) (a := c) hfinrank)

/-- Zero columns have exactly one full-column frame. This is the degenerate
prefix case of the rectangular marginal, not an appeal to positive width. -/
theorem zero_width_frame_card (d : Nat) :
    Fintype.card (Frame (Fin d → ZMod 2) 0) = 1 := by
  classical
  rw [card_binary_rectangular_frames d 0 (Nat.zero_le d)]
  simp [frameProduct]

end
end PvNP.RealizableHardness.RectangularFrameFiberAverage
