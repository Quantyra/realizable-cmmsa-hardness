import Mathlib.Tactic
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

/-! Independent finite Fourier-energy route from the selected high-rank
projection sum to the actual source tail. The second spectral term keeps its
rank index i throughout; only the explicit ambient hypothesis pays for it. -/
namespace PvNP.RealizableHardness.ActualSelectedHighEnergyTail

open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Parseval aggregated over every integral rank level. -/
theorem rankProjection_all_levels_energy_eq {n d : Nat}
    (F : BinaryMatrix n d -> Real) :
    (Finset.sum (Finset.range (d + 1)) (fun i =>
      uniformMean (fun M : BinaryMatrix n d =>
        (rankProjection i F M) ^ 2))) = uniformMean (fun M => F M ^ 2) := by
  classical
  rw [show (Finset.sum (Finset.range (d + 1)) (fun i =>
      uniformMean (fun M : BinaryMatrix n d =>
        (rankProjection i F M) ^ 2))) =
      Finset.sum (Finset.range (d + 1)) (fun i =>
        Finset.sum Finset.univ (fun Y : BinaryMatrix n d =>
          (fourierCoeff (rankProjection i F) Y) ^ 2)) by
        apply Finset.sum_congr rfl
        intro i hi
        exact fourier_parseval (rankProjection i F)]
  rw [Finset.sum_comm]
  have hcoeff (Y : BinaryMatrix n d) :
      Finset.sum (Finset.range (d + 1)) (fun i =>
        (fourierCoeff (rankProjection i F) Y) ^ 2) =
          (fourierCoeff F Y) ^ 2 := by
    rw [Finset.sum_eq_single Y.rank]
    · rw [fourierCoeff_rankProjection]
      have hrank : Y.rank < d + 1 := Nat.lt_succ_of_le (Matrix.rank_le_width Y)
      simp [hrank]
    · intro i hi hne
      rw [fourierCoeff_rankProjection]
      simp [hne.symm]
    · intro hnot
      have hrank : Y.rank < d + 1 := Nat.lt_succ_of_le (Matrix.rank_le_width Y)
      exact (hnot (Finset.mem_range.mpr hrank)).elim
  simp_rw [hcoeff]
  exact (fourier_parseval F).symm

/-- Boolean indicators have squared matrix mean at most one. -/
theorem indicator_squared_mean_le_one {n d : Nat}
    (b : BinaryMatrix n d -> Bool) :
    uniformMean (fun M => (indicator b M) ^ 2) <= 1 := by
  classical
  unfold uniformMean
  have hsum :
      Finset.sum Finset.univ (fun M : BinaryMatrix n d =>
        (indicator b M) ^ 2) <=
      Finset.sum Finset.univ (fun _ : BinaryMatrix n d => (1 : Real)) := by
    apply Finset.sum_le_sum
    intro M hM
    cases hb : b M <;> simp [indicator, hb]
  have hden : 0 < (Fintype.card (BinaryMatrix n d) : Real) := by positivity
  rw [div_le_iff₀ hden]
  simpa using hsum

/-- Each spectral rank layer of a Boolean indicator has at most unit squared
energy by the Fourier projection energy inequality. -/
theorem selected_rank_layer_energy_le_one {n d i : Nat}
    (b : BinaryMatrix n d -> Bool) :
    uniformMean (fun M : BinaryMatrix n d =>
      (rankProjection i (indicator b) M) ^ 2) <= 1 := by
  exact (rankProjection_energy_le (indicator b)).trans
    (indicator_squared_mean_le_one b)

/-- A Parseval-controlled weighted level sum is at most its largest weight.
The index set may be any subset of ranks; Parseval avoids multiplying by the
number of levels. -/
theorem selected_weighted_levels_le_max_weight {n d : Nat}
    (F : BinaryMatrix n d -> Real) (S : Finset (Fin (d + 1)))
    (weight : Fin (d + 1) -> Real) (B : Real)
    (hB : 0 <= B)
    (hweight0 : forall i, i ∈ S -> 0 <= weight i)
    (hweight : forall i, i ∈ S -> weight i <= B)
    (hFenergy : uniformMean (fun M => F M ^ 2) <= 1) :
    Finset.sum S (fun i => weight i *
      uniformMean (fun M : BinaryMatrix n d =>
        (rankProjection i.val F M) ^ 2)) <= B := by
  classical
  let energy : Fin (d + 1) -> Real := fun i =>
    uniformMean (fun M : BinaryMatrix n d =>
      (rankProjection i.val F M) ^ 2)
  have henergy0 (i : Fin (d + 1)) : 0 <= energy i := by
    dsimp [energy, uniformMean]
    apply div_nonneg
    · exact Finset.sum_nonneg (fun M _ => sq_nonneg _)
    · positivity
  have hsubsetEnergy :
      Finset.sum S energy <= Finset.sum Finset.univ energy := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => henergy0 i)
  have hfinRange : Finset.sum Finset.univ energy =
      Finset.sum (Finset.range (d + 1)) (fun i =>
        uniformMean (fun M : BinaryMatrix n d =>
          (rankProjection i F M) ^ 2)) := by
    simpa [energy] using
      (Fin.sum_univ_eq_sum_range
        (fun i : Nat => uniformMean (fun M : BinaryMatrix n d =>
          (rankProjection i F M) ^ 2)) (d + 1))
  have hparseval := rankProjection_all_levels_energy_eq F
  have hsumEnergy : Finset.sum S energy <= 1 := by
    rw [hfinRange, hparseval] at hsubsetEnergy
    exact hsubsetEnergy.trans hFenergy
  calc
    Finset.sum S (fun i => weight i * energy i) <=
        Finset.sum S (fun i => B * energy i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hweight i hi) (henergy0 i)
    _ = B * Finset.sum S energy := by rw [Finset.mul_sum]
    _ <= B := by nlinarith [mul_nonneg hB (sub_nonneg.mpr hsumEnergy)]

/-- Source Lemma 4.8 coefficient estimate. The ambient term remains indexed
by i; the explicit d-versus-n guard is what bounds its worst allowed value. -/
theorem selected_spectral_coefficient_le_tail {d i r s n : Nat}
    (hi : r < i) (hiD : i <= d)
    (hb : 1 <= (s : Real) - 1)
    (hn : (d : Real) - (n : Real) <=
      -(r : Real) * ((s : Real) - 1) - 3) :
    (2 : Real) ^ (-(i : Real) * ((s : Real) - 1)) +
        3 * (2 : Real) ^ ((i : Real) - (n : Real)) <=
      (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) := by
  have hiR : (r : Real) + 1 <= (i : Real) := by
    exact_mod_cast (Nat.succ_le_of_lt hi)
  have hiD_R : (i : Real) <= d := by exact_mod_cast hiD
  have hb0 : 0 <= (s : Real) - 1 := by linarith
  have hgap : 0 <= (i : Real) - ((r : Real) + 1) := by linarith
  have hfirstExp :
      -(i : Real) * ((s : Real) - 1) <=
        -(r : Real) * ((s : Real) - 1) - 1 := by
    nlinarith [mul_nonneg hgap hb0]
  have hsecondExp :
      (i : Real) - (n : Real) <=
        -(r : Real) * ((s : Real) - 1) - 3 := by
    linarith
  have hx : 0 < (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hfirst := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) <= 2) hfirstExp
  have hsecond := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) <= 2) hsecondExp
  have hshift1 :
      (2 : Real) ^ (-(r : Real) * ((s : Real) - 1) - 1) =
        (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) * (1 / 2) := by
    rw [show -(r : Real) * ((s : Real) - 1) - 1 =
      -(r : Real) * ((s : Real) - 1) + (-1) by ring,
      Real.rpow_add (by norm_num : (0 : Real) < 2)]
    norm_num [Real.rpow_neg]
  have hshift3 :
      (2 : Real) ^ (-(r : Real) * ((s : Real) - 1) - 3) =
        (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) * (1 / 8) := by
    rw [show -(r : Real) * ((s : Real) - 1) - 3 =
      -(r : Real) * ((s : Real) - 1) + (-3) by ring,
      Real.rpow_add (by norm_num : (0 : Real) < 2)]
    norm_num [Real.rpow_neg]
  calc
    (2 : Real) ^ (-(i : Real) * ((s : Real) - 1)) +
        3 * (2 : Real) ^ ((i : Real) - (n : Real)) <=
      (2 : Real) ^ (-(r : Real) * ((s : Real) - 1) - 1) +
        3 * (2 : Real) ^ (-(r : Real) * ((s : Real) - 1) - 3) := by
          exact add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = (7 / 8 : Real) *
        (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) := by
          rw [hshift1, hshift3]
          ring
    _ <= (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) := by
          nlinarith

/-- The actual selected Boolean leaf's high spectral expression is bounded by
the source tail after Parseval aggregates all high-rank energies. -/
theorem selected_actual_high_spectral_sum_le_tail {n d r s : Nat}
    (b : BinaryMatrix n d -> Bool)
    (hb : 1 <= (s : Real) - 1)
    (hn : (d : Real) - (n : Real) <=
      -(r : Real) * ((s : Real) - 1) - 3) :
    Finset.sum (selectedHighFinIndexSet d r) (fun i =>
      ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
        3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
        uniformMean (fun W : BinaryMatrix n d =>
          (rankProjection i.val (indicator b) W) ^ 2)) <=
      (2 : Real) ^ (-(r : Real) * ((s : Real) - 1)) := by
  let S := selectedHighFinIndexSet d r
  let wt : Fin (d + 1) -> Real := fun i =>
    (2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
      3 * (2 : Real) ^ ((i.val : Real) - (n : Real))
  let B : Real := (2 : Real) ^ (-(r : Real) * ((s : Real) - 1))
  have hB : 0 <= B := by positivity
  have hwt0 : forall i, i ∈ S -> 0 <= wt i := by
    intro i hi
    dsimp [wt]
    positivity
  have hwt : forall i, i ∈ S -> wt i <= B := by
    intro i hi
    have hir : r < i.val := (Finset.mem_filter.mp hi).2
    have hiD : i.val <= d := Nat.le_of_lt_succ i.isLt
    simpa [wt, B] using
      selected_spectral_coefficient_le_tail hir hiD hb hn
  have hF := indicator_squared_mean_le_one b
  have henergy := selected_weighted_levels_le_max_weight
    (indicator b) S wt B hB hwt0 hwt hF
  simpa [S, wt, B] using henergy

end
end PvNP.RealizableHardness.ActualSelectedHighEnergyTail