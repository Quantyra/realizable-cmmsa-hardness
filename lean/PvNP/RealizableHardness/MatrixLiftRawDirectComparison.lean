import PvNP.RealizableHardness.MatrixLiftLeftRowDirectTransport
import PvNP.RealizableHardness.MatrixLiftFullRowRankBridge

namespace PvNP.RealizableHardness.MatrixLiftRawDirectComparison
open scoped BigOperators
open GrassmannCounting MatrixGrassmannFibre MatrixLiftAffineTarget
open MatrixLiftLeftRowNormalForm MatrixLiftLeftRowDirectTransport
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {C : Type*} [AddCommGroup C] [Module (ZMod 2) C] [Fintype C]

private def explicitScore {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (H : Submodule (ZMod 2) V)
    (X₁ : H →ₗ[ZMod 2] C) (B : Fin k → C) : ℝ :=
  ∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B}, liftScore f g H N.val

private theorem explicitScore_nonneg {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C) (B : Fin k → C) :
    0 ≤ explicitScore f g H X₁ B := by
  unfold explicitScore
  apply Finset.sum_nonneg
  intro N _
  unfold liftScore extensionTest
  split_ifs
  · exact hg _
  · exact le_refl _

private theorem explicit_score_cross {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (B : Fin k → C) (hB : Function.Surjective (columnLinear B))
    (hhalf : Fintype.card (Fin k → C) <
      2 * Fintype.card {B' : Fin k → C // Function.Surjective (columnLinear B')}) :
    explicitScore f g H X₁ B * (Fintype.card (Fin k → C) : ℝ) ≤
      2 * ∑ N : FreeColumns H k, liftScore f g H N := by
  let P : (Fin k → C) → Prop := fun B' => Function.Surjective (columnLinear B')
  have hcard : (Fintype.card (Fin k → C) : ℝ) <
      2 * (Fintype.card {B' : Fin k → C // P B'} : ℝ) := by
    exact_mod_cast hhalf
  have hmass : 0 ≤ explicitScore f g H X₁ B :=
    explicitScore_nonneg f g hg H X₁ B
  have hconst : (∑ B' : {B' : Fin k → C // P B'},
        explicitScore f g H X₁ B'.val) =
      (Fintype.card {B' : Fin k → C // P B'} : ℝ) *
        explicitScore f g H X₁ B := by
    have heq (B' : {B' : Fin k → C // P B'}) :
        explicitScore f g H X₁ B'.val = explicitScore f g H X₁ B := by
      exact fullRank_target_score_eq f g H X₁ B B'.val hB B'.property
    simp only [heq]
    simp [nsmul_eq_mul]
  have hsubset : (∑ B' : {B' : Fin k → C // P B'},
      explicitScore f g H X₁ B'.val) ≤
      ∑ B' : Fin k → C, explicitScore f g H X₁ B' := by
    have hs := Fintype.sum_subtype_add_sum_subtype P (explicitScore f g H X₁)
    have hbad : 0 ≤ ∑ B' : {B' : Fin k → C // ¬P B'},
        explicitScore f g H X₁ B'.val := by
      apply Finset.sum_nonneg
      intro B' _
      exact explicitScore_nonneg f g hg H X₁ B'.val
    calc
      _ ≤ (∑ B' : {B' : Fin k → C // P B'},
            explicitScore f g H X₁ B'.val) +
          (∑ B' : {B' : Fin k → C // ¬P B'},
            explicitScore f g H X₁ B'.val) := le_add_of_nonneg_right hbad
      _ = _ := hs
  have hdisintegrate : (∑ N : FreeColumns H k, liftScore f g H N) =
      ∑ B' : Fin k → C, explicitScore f g H X₁ B' := by
    simpa only [explicitScore] using
      (Fintype.sum_fiberwise (rowTarget H X₁)
        (fun N : FreeColumns H k => liftScore f g H N)).symm
  rw [hdisintegrate]
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hcard) hmass
  nlinarith [hmul]

theorem explicit_mean_le_twice {d k : ℕ} (f : Frame V d)
    (g : Grass V (d+k) → ℝ) (hg : ∀ W, 0 ≤ g W)
    (H : Submodule (ZMod 2) V) (X₁ : H →ₗ[ZMod 2] C)
    (hX₁ : Function.Surjective X₁)
    (B : Fin k → C) (hB : Function.Surjective (columnLinear B))
    (hhalf : Fintype.card (Fin k → C) <
      2 * Fintype.card {B' : Fin k → C // Function.Surjective (columnLinear B')}) :
    (∑ N : {N : FreeColumns H k // rowTarget H X₁ N = B},
      liftScore f g H N.val) /
        (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) ≤
      2 * ((∑ N : FreeColumns H k, liftScore f g H N) /
        (Fintype.card (FreeColumns H k) : ℝ)) := by
  have hnonempty : Nonempty {N : FreeColumns H k // rowTarget H X₁ N = B} := by
    refine ⟨⟨fun i => Classical.choose (hX₁ (B i)), ?_⟩⟩
    funext i
    exact Classical.choose_spec (hX₁ (B i))
  have hm : (0 : ℝ) <
      (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) := by
    exact_mod_cast Fintype.card_pos (α :=
      {N : FreeColumns H k // rowTarget H X₁ N = B})
  have ht : (0 : ℝ) < (Fintype.card (Fin k → C) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fin k → C)
  have hfactor := card_freeColumns_eq_card_targets_mul_fibre H X₁ hX₁ B
  have hcross := explicit_score_cross f g hg H X₁ B hB hhalf
  change (explicitScore f g H X₁ B) /
      (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) ≤ _
  rw [hfactor, Nat.cast_mul]
  have hden : (0 : ℝ) <
      (Fintype.card (Fin k → C) : ℝ) *
        (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ) :=
    mul_pos ht hm
  calc
    _ ≤ (2 * ∑ N : FreeColumns H k, liftScore f g H N) /
        ((Fintype.card (Fin k → C) : ℝ) *
          (Fintype.card {N : FreeColumns H k // rowTarget H X₁ N = B} : ℝ)) := by
            apply (div_le_div_iff₀ hm hden).2
            have hmul := mul_le_mul_of_nonneg_right hcross (le_of_lt hm)
            nlinarith [hmul]
    _ = _ := by ring

end
end PvNP.RealizableHardness.MatrixLiftRawDirectComparison
