import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
import PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
import PvNP.RealizableHardness.BinaryMatrixA1TypedFourier

/-! Manuscript A7, degree zero, on every finite binary space.

`a7HybridQ` is the unweighted sum, over every actual subspace pair, of the
uniform average in the affine base of the carrier `L2` fourth power. The pair
set includes the zero-order pair `(⊥, ⊤)`. At Fourier degree zero the positive
pairs vanish, the zero-order term equals the fourth moment, and that moment
equals `2^(100*0*0) * Q(f)`.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer

open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.BinaryMatrixA1TypedFourier

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Unweighted all-hybrid `Q`, including the zero-order pair. -/
def a7HybridQ {n d : Nat} (f : BinaryMatrix n d → Complex) : ℝ :=
  ∑ p : Submodule F (V d) × Submodule F (W n),
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      typedW6QComponent p.1 p.2 T f)

theorem a7_uniformMean_const {n d : Nat} (c : ℝ) :
    uniformMean (fun _ : BinaryMatrix n d => c) = c :=
  uniformMean_const c

/-- A degree-zero complex source is constant. The induction base uses this on
every finite pair of dimensions, with no extra scalar hypothesis. -/
theorem a7_constant_of_degree_zero {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    ∀ M N, f M = f N := by
  intro M N
  have hM := complexFourierInversion f M
  have hN := complexFourierInversion f N
  have hterm : ∀ Y : BinaryMatrix n d,
      complexFourierCoeff f Y * (character Y M : Complex) =
        complexFourierCoeff f Y * (character Y N : Complex) := by
    intro Y
    by_cases hY : Y = 0
    · simp [hY]
    · have hrank : 0 < Y.rank := by
        have hne : Y.rank ≠ 0 := by
          intro hr
          exact hY ((rank_eq_zero_iff Y).mp hr)
        omega
      have h0 : complexFourierCoeff f Y = 0 := hsupport Y hrank
      simp [h0]
  have hsum : (∑ Y : BinaryMatrix n d,
      complexFourierCoeff f Y * (character Y M : Complex)) =
      ∑ Y : BinaryMatrix n d,
        complexFourierCoeff f Y * (character Y N : Complex) :=
    Finset.sum_congr rfl (fun Y _ => hterm Y)
  rw [← hM, ← hN, hsum]

theorem a7_selected_zero_order {n d : Nat} (Y : W n →ₗ[F] V d) :
    Selected (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) Y :=
  ⟨bot_le, fun _ _ => Submodule.mem_top⟩

theorem a7_zero_matrix_selected_iff {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Selected A B ((0 : BinaryMatrix n d).transpose.toLin') ↔
      A = ⊥ ∧ B = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · intro v hv
        have hv0 : v = 0 := by
          have hrange : v ∈ LinearMap.range ((0 : BinaryMatrix n d).transpose.toLin') :=
            h.1 hv
          rcases hrange with ⟨w, hw⟩
          simpa using hw.symm
        simp [hv0]
      · exact bot_le
    · apply le_antisymm
      · exact le_top
      · intro w hw
        have h0 : ((0 : BinaryMatrix n d).transpose.toLin') w ∈ A := by
          simp
        exact h.2 w h0
  · intro h
    rcases h with ⟨hA, hB⟩
    subst hA
    subst hB
    exact a7_selected_zero_order _

/-- Positive hybrid pairs kill a degree-zero source. -/
theorem a7_filter_zero_of_positive_pair {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f)
    (hpos : A ≠ ⊥ ∨ B ≠ ⊤) :
    complexAmbientHybridFilter A B f = 0 := by
  funext M
  unfold complexAmbientHybridFilter
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : Y = 0
  · have hnot : ¬ Selected A B Y.transpose.toLin' := by
      intro hsel
      have hpair := (a7_zero_matrix_selected_iff A B).1 (by simpa [hY] using hsel)
      cases hpos with
      | inl hA => exact hA hpair.1
      | inr hB => exact hB hpair.2
    simp [hnot]
  · have hrank : 0 < Y.rank := by
      have hne : Y.rank ≠ 0 := by
        intro hr
        exact hY ((rank_eq_zero_iff Y).mp hr)
      omega
    have hcoeff : complexFourierCoeff f Y = 0 := hsupport Y hrank
    simp [hcoeff]

theorem a7_qComponent_zero_of_positive_pair {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f)
    (hpos : A ≠ ⊥ ∨ B ≠ ⊤) :
    typedW6QComponent A B T f = 0 := by
  have hfilter := a7_filter_zero_of_positive_pair A B f hsupport hpos
  unfold typedW6QComponent filteredCarrierFunction complexAmbientAffineRestrict
  rw [hfilter]
  unfold carrierMean
  simp [Complex.normSq_zero, Finset.sum_const_zero, zero_div]

theorem a7_zero_order_qComponent {n d : Nat}
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f =
      (uniformMean (fun M => Complex.normSq (f M))) ^ 2 := by
  have hconst : ∀ M, f M = f 0 := fun M =>
    a7_constant_of_degree_zero f hsupport M 0
  have hmean : uniformMean (fun M => Complex.normSq (f M)) =
      Complex.normSq (f 0) := by
    rw [show (fun M : BinaryMatrix n d => Complex.normSq (f M)) =
        fun _ => Complex.normSq (f 0) from funext (fun M =>
          congrArg Complex.normSq (hconst M))]
    exact uniformMean_const _
  unfold typedW6QComponent
  have hcarrier : carrierMean (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n))
      (fun M => Complex.normSq
        (filteredCarrierFunction (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) T f M)) =
      Complex.normSq (f 0) := by
    have hfun : ∀ M : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
        (⊤ : Submodule F (W n)),
        filteredCarrierFunction (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) T f M = f 0 := by
      intro M
      rw [filteredCarrierFunction_bot_top_base]
      exact hconst _
    unfold carrierMean
    rw [show (fun M : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
          (⊤ : Submodule F (W n)) =>
          Complex.normSq (filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) T f M)) =
        fun _ => Complex.normSq (f 0) from funext (fun M =>
          congrArg Complex.normSq (hfun M))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
        (⊤ : Submodule F (W n))) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
          (⊤ : Submodule F (W n))) ≠ 0)
    field_simp [hcard]
  rw [hcarrier, hmean]

/-- At degree zero, `Q` is exactly the zero-order term. -/
theorem a7_q_eq_zero_order {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    a7HybridQ f =
      (uniformMean (fun M => Complex.normSq (f M))) ^ 2 := by
  classical
  unfold a7HybridQ
  have hsingle : typedUniformMean (fun T : V d →ₗ[F] W n =>
      typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f) =
      (uniformMean (fun M => Complex.normSq (f M))) ^ 2 := by
    have hconst : ∀ T : V d →ₗ[F] W n,
        typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f =
          (uniformMean (fun M => Complex.normSq (f M))) ^ 2 :=
      fun T => a7_zero_order_qComponent T f hsupport
    unfold typedUniformMean
    rw [show (fun T : V d →ₗ[F] W n =>
        typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f) =
        fun _ => (uniformMean (fun M => Complex.normSq (f M))) ^ 2 from
          funext hconst]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (V d →ₗ[F] W n) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (V d →ₗ[F] W n) ≠ 0)
    field_simp [hcard]
  have hsum : (∑ p : Submodule F (V d) × Submodule F (W n),
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        typedW6QComponent p.1 p.2 T f)) =
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f) := by
    rw [Finset.sum_eq_single (⟨⊥, ⊤⟩ : Submodule F (V d) × Submodule F (W n))]
    · intro p _ hp
      have hpos : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤ := by
        by_cases hA : p.1 = ⊥
        · right
          intro hB
          apply hp
          cases p with
          | mk A B =>
            apply Prod.ext
            · exact hA
            · exact hB
        · left
          exact hA
      unfold typedUniformMean
      have hzero : ∀ T : V d →ₗ[F] W n, typedW6QComponent p.1 p.2 T f = 0 :=
        fun T => a7_qComponent_zero_of_positive_pair p.1 p.2 T f hsupport hpos
      rw [show (fun T : V d →ₗ[F] W n => typedW6QComponent p.1 p.2 T f) =
          fun _ => (0 : ℝ) from funext hzero]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, hsingle]

theorem a7_fourth_eq_l2_of_degree_zero {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) =
      (uniformMean (fun M => Complex.normSq (f M))) ^ 2 := by
  have hconst : ∀ M, f M = f 0 := fun M =>
    a7_constant_of_degree_zero f hsupport M 0
  have hfourth : uniformMean (fun M => Complex.normSq (f M) ^ 2) =
      Complex.normSq (f 0) ^ 2 := by
    rw [show (fun M : BinaryMatrix n d => Complex.normSq (f M) ^ 2) =
        fun _ => Complex.normSq (f 0) ^ 2 from funext (fun M => by
          rw [hconst M])]
    exact uniformMean_const _
  have hmean : uniformMean (fun M => Complex.normSq (f M)) =
      Complex.normSq (f 0) := by
    rw [show (fun M : BinaryMatrix n d => Complex.normSq (f M)) =
        fun _ => Complex.normSq (f 0) from funext (fun M =>
          congrArg Complex.normSq (hconst M))]
    exact uniformMean_const _
  rw [hfourth, hmean]

/-- Degree-zero A7, simultaneously for every finite binary space: the fourth
moment equals `2^(100*0*0)` times the unweighted all-hybrid `Q`, and that
factor is the zero-order term. -/
theorem manuscript_A7_degree_zero {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 0 f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) =
      (2 : ℝ) ^ (100 * 0 * 0) * a7HybridQ f := by
  have hQ := a7_q_eq_zero_order f hsupport
  have hfourth := a7_fourth_eq_l2_of_degree_zero f hsupport
  rw [hfourth, hQ]
  simp

/-- The `L2` slack used when a positive degree is later absorbed into `Q`. -/
theorem a7_l2_slack (D : Nat) (hD : 0 < D) :
    (162 : ℝ) * (2 : ℝ) ^ (6 * D * D) ≤ (2 : ℝ) ^ (100 * D * D) := by
  have h162 : (162 : ℝ) ≤ (2 : ℝ) ^ 8 := by norm_num
  have hexp : 8 + 6 * D * D ≤ 100 * D * D := by
    have hk : 1 ≤ D * D := Nat.mul_le_mul hD hD
    have h8 : 8 ≤ 94 * (D * D) := by
      have hpos : 0 < D * D := Nat.succ_le_iff.mp hk
      calc
        8 ≤ 94 := by decide
        _ ≤ 94 * (D * D) := Nat.le_mul_of_pos_right 94 hpos
    calc
      8 + 6 * D * D = 8 + 6 * (D * D) := by rw [Nat.mul_assoc]
      _ ≤ 94 * (D * D) + 6 * (D * D) := Nat.add_le_add_right h8 _
      _ = (94 + 6) * (D * D) := by rw [← Nat.add_mul]
      _ = 100 * (D * D) := by simp
      _ = 100 * D * D := by rw [Nat.mul_assoc]
  calc
    (162 : ℝ) * (2 : ℝ) ^ (6 * D * D) ≤
        (2 : ℝ) ^ 8 * (2 : ℝ) ^ (6 * D * D) := by
          gcongr
    _ = (2 : ℝ) ^ (8 + 6 * D * D) := by rw [← pow_add]
    _ ≤ (2 : ℝ) ^ (100 * D * D) :=
      pow_le_pow_right₀ (by norm_num) hexp

/-- Manuscript terminal factor at every positive degree. -/
theorem a7_terminal_factor (D : Nat) (hD : 0 < D) :
    (162 : ℝ) * ((2 : ℝ) ^ (-(94 * D * D : ℤ)) + (2 : ℝ) ^ ((1 : ℤ) - 31 * D)) < 1 := by
  have hsmall : (162 : ℝ) * ((2 : ℝ) ^ (-94 : ℤ) + (2 : ℝ) ^ (-30 : ℤ)) < 1 := by
    norm_num
  have h94 : (94 : ℤ) ≤ 94 * D * D := by
    have hsq : (1 : ℤ) ≤ D := by exact_mod_cast hD
    have hmul : (1 : ℤ) ≤ (D : ℤ) * D := by nlinarith
    nlinarith
  have h31 : (30 : ℤ) ≤ 31 * D - 1 := by
    have hD1 : (1 : ℤ) ≤ D := by exact_mod_cast hD
    nlinarith
  have hpow94 : (2 : ℝ) ^ (-(94 * D * D : ℤ)) ≤ (2 : ℝ) ^ (-94 : ℤ) := by
    have hbase : (1 : ℝ) ≤ 2 := by norm_num
    exact zpow_le_zpow_right₀ hbase (by linarith : (-(94 * D * D : ℤ)) ≤ (-94 : ℤ))
  have hpow31 : (2 : ℝ) ^ ((1 : ℤ) - 31 * D) ≤ (2 : ℝ) ^ (-30 : ℤ) := by
    have hbase : (1 : ℝ) ≤ 2 := by norm_num
    have hexp : ((1 : ℤ) - 31 * D) ≤ (-30 : ℤ) := by linarith
    exact zpow_le_zpow_right₀ hbase hexp
  have hsum : (2 : ℝ) ^ (-(94 * D * D : ℤ)) + (2 : ℝ) ^ ((1 : ℤ) - 31 * D) ≤
      (2 : ℝ) ^ (-94 : ℤ) + (2 : ℝ) ^ (-30 : ℤ) := by
    gcongr
  have hnonneg : 0 ≤ (2 : ℝ) ^ (-(94 * D * D : ℤ)) + (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 162)
  exact lt_of_le_of_lt hmul hsmall

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
