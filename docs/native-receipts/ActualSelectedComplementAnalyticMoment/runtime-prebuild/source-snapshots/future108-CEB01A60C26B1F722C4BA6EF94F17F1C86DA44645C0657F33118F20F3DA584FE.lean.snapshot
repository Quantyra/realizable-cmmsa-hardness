import PvNP.RealizableHardness.ActualTypedABMixedTower

namespace PvNP.RealizableHardness.ActualTypedABRankedTower

open ActualTypedABMixedTower
open BinaryMatrixA1NestedCarrier
open BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixTypedA15HyperplaneReducedGlobal

noncomputable section
set_option autoImplicit false

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- An A15 tower with an explicit residual rank. A node with `k+1` steps
uses the selected operator at rank `r+k`; after all steps the terminal
carrier retains the rank-r globalness bound. This is the source-shaped form
needed when derivative order is smaller than the input degree. It does not
assert that the entire terminal signal is homogeneous of rank r. -/
inductive ActualTypedABRankedTower {n d : Nat} :
    (A : Submodule F (V d)) → (B : Submodule F (W n)) →
    (((V d ⧸ A) →ₗ[F] B) → Complex) → Nat → Nat → Type 1
  | done {A : Submodule F (V d)} {B : Submodule F (W n)}
      (f : ((V d ⧸ A) →ₗ[F] B) → Complex) (r : Nat) :
      ActualTypedABRankedTower A B f r 0
  | line {A : Submodule F (V d)} {B : Submodule F (W n)}
      {A' : Submodule F (V d)}
      (hA : A ≤ A')
      (hL : Module.finrank F (A'.map A.mkQ) = 1)
      {r k : Nat} (T : (V d ⧸ A) →ₗ[F] B)
      (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
      (tail : ActualTypedABRankedTower A' B
        (fun M => typedLineReducedWitness (k := r + k)
          B (A'.map A.mkQ) hL T f
          (M.comp (nestedDomainEquiv A A' hA))) r k) :
      ActualTypedABRankedTower A B f r (k + 1)
  | hyperplane {A : Submodule F (V d)} {B : Submodule F (W n)}
      {H : Submodule F B}
      (hH : Module.finrank F (B ⧸ H) = 1)
      {r k : Nat} (T : (V d ⧸ A) →ₗ[F] B)
      (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
      (tail : ActualTypedABRankedTower A (H.map B.subtype)
        (fun N => typedHyperplaneReducedWitness (k := r + k) B H hH T f
          ((Submodule.equivMapOfInjective B.subtype B.injective_subtype H).symm
            .toLinearMap.comp N)) r k) :
      ActualTypedABRankedTower A B f r (k + 1)

structure RankedTerminalData {n d : Nat} {r k : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    {f : ((V d ⧸ A) →ₗ[F] B) → Complex}
    (tower : ActualTypedABRankedTower A B f r k) where
  Aend : Submodule F (V d)
  Bend : Submodule F (W n)
  fend : ((V d ⧸ Aend) →ₗ[F] Bend) → Complex

def rankedTerminalData {n d : Nat} {r k : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    {f : ((V d ⧸ A) →ₗ[F] B) → Complex} :
    (tower : ActualTypedABRankedTower A B f r k) → RankedTerminalData tower
  | .done f _ => ⟨_, _, f⟩
  | .line _ _ _ _ tail => rankedTerminalData tail
  | .hyperplane _ _ _ tail => rankedTerminalData tail

/-- The product of the exact A15 losses for ranks `r+1` through `r+k`.
The terminal rank `r` is retained and is not charged as a derivative step. -/
def rankedA15Loss (r : Nat) : Nat → Real
  | 0 => 1
  | k + 1 => (4 * (2 : Real) ^ (4 * (r + k + 1))) * rankedA15Loss r k

theorem rankedA15Loss_nonneg (r k : Nat) : 0 ≤ rankedA15Loss r k := by
  induction k with
  | zero => simp [rankedA15Loss]
  | succ k ih =>
      simp only [rankedA15Loss]
      positivity

theorem rankedA15Loss_eq_pow (r k : Nat) :
    rankedA15Loss r k =
      (2 : Real) ^ (4 * r * k + 2 * k ^ 2 + 4 * k) := by
  induction k with
  | zero => simp [rankedA15Loss]
  | succ k ih =>
      have hexp :
          4 * r * (k + 1) + 2 * (k + 1) ^ 2 + 4 * (k + 1) =
            (4 * r * k + 2 * k ^ 2 + 4 * k) + (4 * (r + k + 1) + 2) := by
        ring
      rw [rankedA15Loss, ih, hexp, pow_add]
      norm_num [pow_add]
      ring

/-- If the highest selected rank is at most D, the accumulated actual A15
loss is bounded by the manuscript's `2^(11 D^2)` envelope. -/
theorem rankedA15Loss_le_degree (r k D : Nat) (hlevel : r + k ≤ D) :
    rankedA15Loss r k ≤ (2 : Real) ^ (11 * D ^ 2) := by
  rw [rankedA15Loss_eq_pow]
  have hr : r ≤ D := Nat.le_trans (Nat.le_add_right r k) hlevel
  have hk : k ≤ D := Nat.le_trans (Nat.le_add_left k r) hlevel
  have hDsq : D ≤ D ^ 2 := by
    by_cases hD : D = 0
    · simp [hD]
    · have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hD
      nlinarith [Nat.mul_le_mul_left D hDpos]
  have hrk : r * k ≤ D ^ 2 := by
    calc
      r * k ≤ D * D := Nat.mul_le_mul hr hk
      _ = D ^ 2 := by simp [pow_two]
  have hk2 : k ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hk 2
  have hexp : 4 * r * k + 2 * k ^ 2 + 4 * k ≤ 11 * D ^ 2 := by
    nlinarith
  exact pow_le_pow_right' (by norm_num : 1 ≤ (2 : Real)) hexp

/-- Repeated A15 transitions preserve the genuine residual level `r` and
bound its terminal typed globalness from the original function's bound
through `r+k`. No projected-globalness premise is introduced. -/
theorem ranked_tower_terminal_global {n d : Nat} {r k : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    {f : ((V d ⧸ A) →ₗ[F] B) → Complex}
    (tower : ActualTypedABRankedTower A B f r k) :
    ∀ eps : Real, 0 ≤ eps → UpToTypedNormSqGlobal A B (r + k) eps f →
      UpToTypedNormSqGlobal (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend r
        (rankedA15Loss r k * eps) (rankedTerminalData tower).fend := by
  induction tower with
  | @done n d A B f r =>
      intro eps heps hglobal
      simpa [rankedTerminalData] using hglobal
  | @line n d A B A' hA hL r k T f tail ih =>
      intro eps heps hglobal
      have hglobal' : UpToTypedNormSqGlobal A B ((r + k) + 1) eps f := by
        simpa [Nat.add_assoc] using hglobal
      have hred := adapted_line_oneStep_A15_global (k := r + k)
        A A' B hA hL T f heps hglobal'
      have hflat := reduced_global_to_flat_adapted
        A A' B hA
        (typedLineReducedWitness (k := r + k) B (A'.map A.mkQ) hL T f)
        hred
      have heps' : 0 ≤
          (4 * (2 : Real) ^ (4 * (r + k + 1))) * eps := by positivity
      have htail := ih ((4 * (2 : Real) ^ (4 * (r + k + 1))) * eps)
        heps' hflat
      have hscale : rankedA15Loss r k *
          ((4 * (2 : Real) ^ (4 * (r + k + 1))) * eps) =
          rankedA15Loss r (k + 1) * eps := by
        simp [rankedA15Loss, mul_assoc, mul_left_comm, mul_comm]
      simpa [rankedTerminalData] using hscale ▸ htail
  | @hyperplane n d A B H hH r k T f tail ih =>
      intro eps heps hglobal
      have hglobal' : UpToTypedNormSqGlobal A B ((r + k) + 1) eps f := by
        simpa [Nat.add_assoc] using hglobal
      have hred := adapted_hyperplane_oneStep_A15_global (k := r + k)
        A B H hH T f heps hglobal'
      have hflat := hyperplane_reduced_global_to_flat_adapted
        A B H
        (typedHyperplaneReducedWitness (k := r + k) B H hH T f)
        hred
      have heps' : 0 ≤
          (4 * (2 : Real) ^ (4 * (r + k + 1))) * eps := by positivity
      have htail := ih ((4 * (2 : Real) ^ (4 * (r + k + 1))) * eps)
        heps' hflat
      have hscale : rankedA15Loss r k *
          ((4 * (2 : Real) ^ (4 * (r + k + 1))) * eps) =
          rankedA15Loss r (k + 1) * eps := by
        simp [rankedA15Loss, mul_assoc, mul_left_comm, mul_comm]
      simpa [rankedTerminalData] using hscale ▸ htail

end
end PvNP.RealizableHardness.ActualTypedABRankedTower
