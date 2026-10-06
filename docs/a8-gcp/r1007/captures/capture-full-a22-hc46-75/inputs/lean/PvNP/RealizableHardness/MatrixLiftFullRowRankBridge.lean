import PvNP.RealizableHardness.MatrixLiftAffineTarget
import PvNP.RealizableHardness.MatrixFullRowRankHalf

/-! The strict binary full-row-rank count discharges the only counting
premise of the actual affine-target matrix-lift comparison. -/
namespace PvNP.RealizableHardness.MatrixLiftFullRowRankBridge
open scoped BigOperators
open GrassmannCounting MatrixGrassmannIntersectingAnchor
set_option autoImplicit false
set_option linter.defProp false
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {D₀ : Type*} [AddCommGroup D₀] [Module (ZMod 2) D₀]

/-- Surjectivity of the independent row constraints gives surjectivity of
the nonzero-target rows on the zero-target row kernel. -/
theorem residual_row_surjective {c : ℕ}
    (X₀ : V →ₗ[ZMod 2] D₀) (X₁ : V →ₗ[ZMod 2] (Fin c → ZMod 2))
    (hrows : Function.Surjective (X₁.prod X₀)) :
    Function.Surjective (X₁.domRestrict (LinearMap.ker X₀)) := by
  intro y
  obtain ⟨v, hv⟩ := hrows (y, 0)
  refine ⟨⟨v, ?_⟩, ?_⟩
  · apply LinearMap.mem_ker.mpr
    exact congrArg Prod.snd hv
  · exact congrArg Prod.fst hv

/-- More than half of the concrete binary targets have full row rank. -/
theorem binary_target_half (c k : ℕ) (hck : c < k) :
    Fintype.card (Fin k → (Fin c → ZMod 2)) <
      2 * Fintype.card {B : Fin k → (Fin c → ZMod 2) //
        Function.Surjective (MatrixLiftAffineTarget.columnLinear B)} :=
  MatrixFullRowRankHalf.full_row_rank_gt_half c k hck

theorem binary_target_half_natCard (c k : ℕ) (hck : c < k) :
    Nat.card (Fin k → (Fin c → ZMod 2)) <
      2 * Nat.card {B : Fin k → (Fin c → ZMod 2) //
        Function.Surjective (MatrixLiftAffineTarget.columnLinear B)} := by
  simpa only [Nat.card_eq_fintype_card] using binary_target_half c k hck

def binary_affine_target_score_sum_le_twice {a k c : ℕ}
    (hck : c < k)
    (H : Submodule (ZMod 2) V)
    (f : Frame V a)
    (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X₁ : H →ₗ[ZMod 2] (Fin c → ZMod 2))
    (B : Fin k → (Fin c → ZMod 2))
    (hB : Function.Surjective (MatrixLiftAffineTarget.columnLinear B)) :=
  @MatrixLiftAffineTarget.affine_target_score_sum_le_twice_natCard
    V inferInstance inferInstance inferInstance
    (Fin c → ZMod 2) inferInstance inferInstance inferInstance
    a k f g hg H X₁ B hB (binary_target_half_natCard c k hck)

/-- Concrete normalized factor-two comparison on actual ordered columns. -/
def binary_affine_target_mean_le_twice {a k c : ℕ}
    (hck : c < k)
    (H : Submodule (ZMod 2) V)
    (f : Frame V a)
    (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (X₁ : H →ₗ[ZMod 2] (Fin c → ZMod 2))
    (hX₁ : Function.Surjective X₁)
    (B : Fin k → (Fin c → ZMod 2))
    (hB : Function.Surjective (MatrixLiftAffineTarget.columnLinear B)) :=
  @MatrixLiftAffineTarget.affine_target_mean_le_twice_natCard
    V inferInstance inferInstance inferInstance
    (Fin c → ZMod 2) inferInstance inferInstance inferInstance
    a k f g hg H X₁ hX₁ B hB (binary_target_half_natCard c k hck)

/-- Concrete affine-target density bound feeding the fixed-U decoder's
matrix-lift comparison. The zoom density premise remains exactly local to
the eligible interval. -/
def binary_affine_target_zoom_density_le_two_e {a z k c : ℕ}
    (hck : c < k)
    (Q H : Submodule (ZMod 2) V)
    (f : Frame V a) (s : Frame V z)
    (hfQ : Submodule.span (ZMod 2) (Set.range f.val) = Q)
    (hsQH : Submodule.span (ZMod 2) (Set.range s.val) = Q ⊓ H)
    (g : Grass V (a+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (e : ℝ) (he : 0 ≤ e)
    (hzoom : (∑ L : HomEligible f H k, g L.val) ≤
      e * (Fintype.card (HomEligible f H k) : ℝ))
    (X₁ : H →ₗ[ZMod 2] (Fin c → ZMod 2))
    (hX₁ : Function.Surjective X₁)
    (B : Fin k → (Fin c → ZMod 2))
    (hB : Function.Surjective (MatrixLiftAffineTarget.columnLinear B)) :=
  @MatrixLiftAffineTarget.affine_target_zoom_density_le_two_e_natCard
    V inferInstance inferInstance inferInstance
    (Fin c → ZMod 2) inferInstance inferInstance inferInstance
    a z k Q H f s hfQ hsQH g hg e he hzoom X₁ hX₁ B hB
    (binary_target_half_natCard c k hck)

end
end PvNP.RealizableHardness.MatrixLiftFullRowRankBridge
