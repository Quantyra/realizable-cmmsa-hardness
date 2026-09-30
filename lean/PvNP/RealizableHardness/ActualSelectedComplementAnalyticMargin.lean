import Mathlib.Tactic
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
import PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection

/-! Component arithmetic for comparing the selected large-dyadic analytic
bound with the actual selected-star signal.  The source's chosen-functional
signal is consumed separately from this scalar work; no final margin, beta
lower bound, or inverse conclusion is assumed here. -/

namespace PvNP.RealizableHardness.ActualSelectedComplementAnalyticMargin

open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
open PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
open PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.ActualOrdinaryStarMatchingFiber

noncomputable section

def sourceRankExponent (m : Nat) : Nat := 40000 * m ^ 3

def sourceMomentTLowerBound (m : Nat) : Nat := sourceHolderLowerBound m

def sourceMomentT (m : Nat) : Nat := 2 ^ sourceMomentTLowerBound m

def sourceMomentP (m : Nat) : Nat := 2 ^ (m * sourceMomentT m)

def sourceTailHeightFloor (m : Nat) : Nat := max (4000 * m ^ 2) (12 * m)

def sourceMarginHeightFloor (m : Nat) : Nat :=
  max (sourceTailHeightFloor m) (20001 * m ^ 2)

def sourceHighErrorExponentGap (m h : Nat) : Real :=
  (((8 : Real) / 3) * (m : Real) - 2 +
      (3996 * (m : Real) + 2) * (fixedRho m : Real)) * (h : Real) -
    ((sourceRankExponent m : Real) + 7)

def sourceHighErrorExponent (m h : Nat) : Real :=
  (sourceRankExponent m : Real) + 2 -
    ((20 : Real) / 3) * (m : Real) * (h : Real)

def sourceWeightedSignalExponent (m h : Nat) : Real :=
  -4 * (1 - 1000 * (fixedRho m : Real)) * (m : Real) * (h : Real) - 5 -
    2 * (1 - (fixedRho m : Real)) * (h : Real) -
    4 * (m : Real) * (fixedRho m : Real) * (h : Real)

theorem source_signal_exponent_gap_exact {m h : Nat} :
    sourceWeightedSignalExponent m h - sourceHighErrorExponent m h =
      sourceHighErrorExponentGap m h := by
  unfold sourceWeightedSignalExponent sourceHighErrorExponent
    sourceHighErrorExponentGap sourceRankExponent
  ring

theorem source_high_error_exponent_gap_positive {m h : Nat}
    (hm : 256 <= m) (hh : 20001 * m ^ 2 <= h) :
    0 < sourceHighErrorExponentGap m h := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hmRlarge : (256 : Real) <= (m : Real) := by exact_mod_cast hm
  have hhR : 20001 * (m : Real) ^ 2 <= (h : Real) := by exact_mod_cast hh
  have hrho := fixed_rho_pos hmpos
  have hcoeff :
      2 * (m : Real) <=
        (8 / 3 : Real) * (m : Real) - 2 +
          (3996 * (m : Real) + 2) * (fixedRho m : Real) := by
    have hbase : 2 * (m : Real) <= (8 / 3 : Real) * (m : Real) - 2 := by
      nlinarith
    exact hbase.trans (by nlinarith [mul_nonneg
      (show 0 <= 3996 * (m : Real) + 2 by positivity)
      (show 0 <= (fixedRho m : Real) by exact hrho.le)])
  have hrNat : (sourceRankExponent m : Real) = 40000 * (m : Real) ^ 3 := by
    norm_num [sourceRankExponent, pow_succ]
  unfold sourceHighErrorExponentGap
  rw [hrNat]
  have hmul : 2 * (m : Real) * (20001 * (m : Real) ^ 2) =
      40002 * (m : Real) ^ 3 := by ring
  have hmain :
      40002 * (m : Real) ^ 3 > 40000 * (m : Real) ^ 3 + 7 := by
    nlinarith
  have hmulcoeff := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : (0 : Real) <= (h : Real))
  nlinarith [mul_le_mul_of_nonneg_left hhR (by positivity : (0 : Real) <= 2 * m),
    hmul, hmulcoeff, hmain]

def sourceSuccessScale (m h : Nat) : Real :=
  (2 : Real) ^ (-2 * (1 - 1000 * (fixedRho m : Real)) *
    (m : Real) * (h : Real))

def sourceAgreementScale (m h : Nat) : Real := manuscriptAgreementFloor m h

def sourceThresholdScale (m h : Nat) : Real := manuscriptMomentThreshold m h

/-- The accepted global-functional selection gives a genuine additive
selected-f signal. Combined with `X_f <= beta_f`, its positive unconditional
term proves the selected beta lower bound; beta is not supplied as a margin
hypothesis. -/
theorem ordinary_selected_functional_beta_lower
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {t d m E : Nat}
    (htd : t <= d) (hdV : d <= Module.finrank (ZMod 2) V)
    (hk : 1 <= d - t)
    (hguard : m * (d - t) + E + 2 <= Module.finrank (ZMod 2) V - t)
    (hcenter : Nonempty (Grass V t))
    (hleaf : forall K : Grass V t, Nonempty (LeafOver K d))
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (hscore : successMargin E <= StarDensity (k := m) hcenter hleaf C T) :
    exists f : Module.Dual (ZMod 2) V,
      let beta := matchingCenterMass (m := m) htd hdV C f
      let M : Rat := 2 ^ (Module.finrank (ZMod 2) V -
        (t + m * (d - t)))
      let F : Rat := 2 ^ Module.finrank (ZMod 2) V
      (successMargin E / 4) * (M / F) <= beta := by
  obtain ⟨f, hselected⟩ :=
    ActualOrdinaryStarWeightedSelection.ordinary_star_selects_weighted_functional
      htd hdV hk hguard hcenter hleaf C T hscore
  refine ⟨f, ?_⟩
  dsimp at hselected ⊢
  rcases hselected with ⟨hsignal, hdom⟩
  have hfirst : 0 <=
      (successMargin E / 4) *
        (2 ^ (Module.finrank (ZMod 2) V -
          (t + m * (d - t))) /
          2 ^ (Module.finrank (ZMod 2) V)) *
        matchingCenterMass (m := m) htd hdV C f := by positivity
  nlinarith

/-- Parseval aggregated over every integral rank level.  This is the finite
identity needed to control the total selected high-level energy without an
extra factor for the number of levels. -/
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
theorem indicator_squared_mean_le_one {n d : Nat} (b : BinaryMatrix n d -> Bool) :
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

/-- Each spectral rank layer of the actual Boolean indicator carries at most
unit squared energy, by the proved Fourier Parseval/Bessel identity. -/
theorem selected_rank_layer_energy_le_one {n d i : Nat}
    (b : BinaryMatrix n d -> Bool) :
    uniformMean (fun M : BinaryMatrix n d =>
      (rankProjection i (indicator b) M) ^ 2) <= 1 := by
  exact (rankProjection_energy_le (indicator b)).trans
    (indicator_squared_mean_le_one b)

/-- A Parseval-controlled weighted level sum is at most its largest weight.
The high index set may be any subset of the available ranks; the proof uses
the full rank-energy identity above, not a per-level bound multiplied by d. -/
theorem selected_weighted_levels_le_max_weight {n d : Nat}
    (F : BinaryMatrix n d -> Real) (S : Finset (Fin (d + 1)))
    (weight : Fin (d + 1) -> Real) (B : Real)
    (hB : 0 <= B)
    (hweight0 : forall i, i in S -> 0 <= weight i)
    (hweight : forall i, i in S -> weight i <= B)
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

/-- Pointwise spectral coefficient estimate under the explicit ambient
condition in Lemma 4.8. For i>r, the first spectral term contributes at most
half of 2^{-r(s-1)} and the ambient term contributes at most three eighths. -/
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
the source tail after Parseval aggregates all high rank energies. Conditions
are stated in the source's integral dimensions; no assumed high-energy field
is introduced. -/
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
  have hwt0 : forall i, i in S -> 0 <= wt i := by
    intro i hi
    dsimp [wt]
    positivity
  have hwt : forall i, i in S -> wt i <= B := by
    intro i hi
    have hir : r < i.val := (Finset.mem_filter.mp hi).2
    have hiD : i.val <= d := Nat.le_of_lt_succ i.isLt
    simpa [wt, B] using
      selected_spectral_coefficient_le_tail hir hiD hb hn
  have hF := indicator_squared_mean_le_one b
  have henergy := selected_weighted_levels_le_max_weight
    (indicator b) S wt B hB hwt0 hwt hF
  simpa [S, wt, B] using henergy

/-- The explicit enlarged-height and block-growth guards imply the two
ambient hypotheses used in the high spectral tail estimate. The only
dimension growth used is the selected sampler's existing `h^2 < J`. -/
theorem source_tail_guards_of_growth {m h J s : Nat}
    (hm : 256 <= m) (hhS : 4000 * m ^ 2 <= h)
    (hh12 : 12 * m <= h) (hJ : h ^ 2 < J)
    (hs : (s : Real) = 2 * (fixedRho m : Real) * (h : Real)) :
    1 <= (s : Real) - 1 /\
    (2 * (h : Real) : Real) - (2 * (J : Real)) <=
      -(sourceRankExponent m : Real) * ((s : Real) - 1) - 3 := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hhS_R : 4000 * (m : Real) ^ 2 <= (h : Real) := by exact_mod_cast hhS
  have hh12_R : 12 * (m : Real) <= (h : Real) := by exact_mod_cast hh12
  have hJ_R : (h : Real) ^ 2 < (J : Real) := by exact_mod_cast hJ
  have hrho := fixed_rho_explicit hmpos
  have hsExact : (s : Real) = (h : Real) / (2000 * (m : Real) ^ 2) := by
    rw [hrho] at hs
    rw [hs]
    field_simp [ne_of_gt hmR]
    ring
  have hs2 : 2 <= (s : Real) := by
    rw [hsExact]
    rw [le_div_iff₀ (by positivity : (0 : Real) < 2000 * (m : Real) ^ 2)]
    nlinarith
  have hb : 1 <= (s : Real) - 1 := by linarith
  have hr : (sourceRankExponent m : Real) = 40000 * (m : Real) ^ 3 := by
    norm_num [sourceRankExponent, pow_succ]
  have hproduct :
      (sourceRankExponent m : Real) * (s : Real) <=
        20 * (m : Real) * (h : Real) := by
    rw [hr, hsExact]
    field_simp [ne_of_gt hmR]
    ring
  have hprodsub :
      (sourceRankExponent m : Real) * ((s : Real) - 1) <=
        20 * (m : Real) * (h : Real) := by
    have hrnonneg : 0 <= (sourceRankExponent m : Real) := by positivity
    nlinarith
  constructor
  · exact hb
  · have hlarge :
        2 * (h : Real) ^ 2 + 2 <= 2 * (J : Real) := by nlinarith
    have hsq :
        12 * (m : Real) * (h : Real) <= (h : Real) ^ 2 :=
      mul_le_mul_of_nonneg_right hh12_R (by positivity)
    have hcompare :
        20 * (m : Real) * (h : Real) + 2 * (h : Real) + 3 <=
          2 * (h : Real) ^ 2 + 2 := by nlinarith [hsq]
    nlinarith

theorem source_tail_guards_of_margin_floor {m h J s : Nat}
    (hm : 256 <= m) (hfloor : sourceMarginHeightFloor m <= h)
    (hJ : h ^ 2 < J)
    (hs : (s : Real) = 2 * (fixedRho m : Real) * (h : Real)) :
    1 <= (s : Real) - 1 /\
    (2 * (h : Real) : Real) - (2 * (J : Real)) <=
      -(sourceRankExponent m : Real) * ((s : Real) - 1) - 3 := by
  have htail : sourceTailHeightFloor m <= h :=
    (Nat.le_max_left _ _).trans hfloor
  have hhS : 4000 * m ^ 2 <= h :=
    (Nat.le_max_left _ _).trans htail
  have hh12 : 12 * m <= h :=
    (Nat.le_max_right _ _).trans htail
  exact source_tail_guards_of_growth hm hhS hh12 hJ hs

end PvNP.RealizableHardness.ActualSelectedComplementAnalyticMargin
