import PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
import PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
import PvNP.RealizableHardness.BinaryMatrixA1TypedFourier

/-! Manuscript A7, degree zero, on every finite binary space.

`a7HybridQ` is the unweighted sum, over every actual subspace pair, of the
uniform average in the affine base of the carrier `L2` fourth power. The pair
set includes the zero-order pair `(⊥, ⊤)`. At Fourier degree zero the positive
pairs vanish, the zero-order term equals the fourth moment, and that moment
equals `2^(100*0*0) * Q(f)`. For every source, that same zero-order term is the
squared `L2` energy, so it sits under `Q`. The positive-degree closure from A6
is stated only under an explicit mixed-sum bound; that bound is not A7.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer

open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Moment
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

set_option maxHeartbeats 1500000

/-- Bottom/top carrier maps are the ambient linear maps. -/
private def a7BotTopHomEquiv {n d : Nat} :
    ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F] (⊤ : Submodule F (W n))) ≃ₗ[F]
      (V d →ₗ[F] W n) :=
  LinearEquiv.arrowCongr
    ((⊥ : Submodule F (V d)).quotEquivOfEqBot rfl)
    (Submodule.topEquiv)

private theorem a7BotTopHomEquiv_apply {n d : Nat}
    (M : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F] (⊤ : Submodule F (W n))) :
    a7BotTopHomEquiv (n := n) (d := d) M =
      (⊤ : Submodule F (W n)).subtype.comp
        (M.comp (Submodule.mkQ (⊥ : Submodule F (V d)))) := by
  ext x
  simp [a7BotTopHomEquiv, LinearEquiv.arrowCongr_apply]

/-- Standard matrix coordinates of a bottom/top carrier map. -/
private def a7BotTopMatrixEquiv {n d : Nat} :
    ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F] (⊤ : Submodule F (W n))) ≃
      BinaryMatrix n d :=
  ((a7BotTopHomEquiv (n := n) (d := d)).trans LinearMap.toMatrix').toEquiv

private theorem a7_addLeft_apply {n d : Nat}
    (T M : BinaryMatrix n d) : Equiv.addLeft T M = T + M := rfl

private theorem a7_filter_matrix {n d : Nat}
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F] (⊤ : Submodule F (W n))) :
    filteredCarrierFunction (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f M =
      f (LinearMap.toMatrix' T + a7BotTopMatrixEquiv M) := by
  rw [filteredCarrierFunction_bot_top_base]
  have hhom := a7BotTopHomEquiv_apply (n := n) (d := d) M
  have hadd :
      LinearMap.toMatrix' (T + a7BotTopHomEquiv (n := n) (d := d) M) =
        LinearMap.toMatrix' T +
          LinearMap.toMatrix' (a7BotTopHomEquiv (n := n) (d := d) M) :=
    map_add LinearMap.toMatrix' T (a7BotTopHomEquiv (n := n) (d := d) M)
  apply congrArg f
  rw [← hhom, hadd]
  simp [a7BotTopMatrixEquiv, LinearEquiv.trans_apply]

/-- For every source, the zero-order hybrid component is the squared `L2`
energy. The carrier is a translate of the ambient matrix space. -/
theorem a7_zero_order_component {n d : Nat}
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex) :
    typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f =
      (uniformMean (fun M => Complex.normSq (f M))) ^ 2 := by
  classical
  let carrier :=
    (V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F] (⊤ : Submodule F (W n))
  let e : carrier ≃ BinaryMatrix n d :=
    (a7BotTopMatrixEquiv (n := n) (d := d)).trans
      (Equiv.addLeft (LinearMap.toMatrix' T))
  have hpoint : ∀ M : carrier,
      Complex.normSq
        (filteredCarrierFunction (⊥ : Submodule F (V d))
          (⊤ : Submodule F (W n)) T f M) =
        Complex.normSq (f (e M)) := by
    intro M
    have he : e M = LinearMap.toMatrix' T + a7BotTopMatrixEquiv M := by
      unfold e
      rw [Equiv.trans_apply]
      exact a7_addLeft_apply (LinearMap.toMatrix' T) (a7BotTopMatrixEquiv M)
    rw [a7_filter_matrix T f M, he]
  have hsum :
      (∑ M : carrier,
        Complex.normSq
          (filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) T f M)) =
        ∑ X : BinaryMatrix n d, Complex.normSq (f X) := by
    calc
      _ = ∑ M : carrier, Complex.normSq (f (e M)) :=
        Finset.sum_congr rfl (fun M _ => hpoint M)
      _ = ∑ X : BinaryMatrix n d, Complex.normSq (f X) :=
        Equiv.sum_comp e (fun X => Complex.normSq (f X))
  have hcard : Fintype.card carrier = Fintype.card (BinaryMatrix n d) :=
    Fintype.card_congr e
  unfold typedW6QComponent
  have hmean :
      carrierMean (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n))
        (fun M => Complex.normSq
          (filteredCarrierFunction (⊥ : Submodule F (V d))
            (⊤ : Submodule F (W n)) T f M)) =
        uniformMean (fun M => Complex.normSq (f M)) := by
    unfold carrierMean uniformMean
    rw [hsum]
    have hcardR : (Fintype.card carrier : ℝ) =
        (Fintype.card (BinaryMatrix n d) : ℝ) := congrArg Nat.cast hcard
    rw [hcardR]
  rw [hmean]

theorem a7HybridQ_nonneg {n d : Nat} (f : BinaryMatrix n d → Complex) :
    0 ≤ a7HybridQ f := by
  unfold a7HybridQ
  refine Finset.sum_nonneg (fun p _ => ?_)
  unfold typedUniformMean
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  refine Finset.sum_nonneg (fun T _ => ?_)
  unfold typedW6QComponent
  exact sq_nonneg _

/-- The zero-order pair is one nonnegative term of the unweighted all-hybrid
`Q`, so the squared `L2` energy is at most `Q`. -/
theorem a7_zero_order_uniform {n d : Nat} (f : BinaryMatrix n d → Complex) :
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f) =
      (uniformMean (fun M => Complex.normSq (f M))) ^ 2 := by
  classical
  unfold typedUniformMean
  have hconst : ∀ T : V d →ₗ[F] W n,
      typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f =
        (uniformMean (fun M => Complex.normSq (f M))) ^ 2 :=
    fun T => a7_zero_order_component T f
  have hfun :
      (fun T : V d →ₗ[F] W n =>
        typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f) =
        fun _ => (uniformMean (fun M => Complex.normSq (f M))) ^ 2 :=
    funext hconst
  rw [hfun, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (V d →ₗ[F] W n) ≠ 0))

/-- One subspace pair's summand in unweighted `Q`. These summands are the
concrete disjoint shares of `Q`. -/
def a7PairShare {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) : ℝ :=
  typedUniformMean (fun T : V d →ₗ[F] W n => typedW6QComponent A B T f)

theorem a7_qComponent_uniform_nonneg {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) :
    0 ≤ typedUniformMean (fun T : V d →ₗ[F] W n => typedW6QComponent A B T f) := by
  unfold typedUniformMean
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  refine Finset.sum_nonneg (fun _ _ => ?_)
  unfold typedW6QComponent
  exact sq_nonneg _

theorem a7_pair_share_nonneg {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) :
    0 ≤ a7PairShare A B f := by
  simpa [a7PairShare] using a7_qComponent_uniform_nonneg A B f

/-- The pair shares are exactly the summands of unweighted `Q`. -/
theorem a7_pair_shares_exhaust {n d : Nat} (f : BinaryMatrix n d → Complex) :
    (∑ p : Submodule F (V d) × Submodule F (W n), a7PairShare p.1 p.2 f) =
      a7HybridQ f := by
  classical
  let g : Submodule F (V d) × Submodule F (W n) → ℝ :=
    fun p => typedUniformMean (fun T : V d →ₗ[F] W n =>
      typedW6QComponent p.1 p.2 T f)
  have hg : ∀ p, a7PairShare p.1 p.2 f = g p := by
    intro p
    unfold a7PairShare g
    rfl
  have hQ : (∑ p, g p) = a7HybridQ f := by
    unfold a7HybridQ g
    rfl
  have hsum :
      (∑ p : Submodule F (V d) × Submodule F (W n), a7PairShare p.1 p.2 f) =
        ∑ p, g p :=
    Finset.sum_congr rfl (fun (p : Submodule F (V d) × Submodule F (W n)) _ => hg p)
  exact hsum.trans hQ

theorem a7_q_ge_l2 {n d : Nat} (f : BinaryMatrix n d → Complex) :
    (uniformMean (fun M => Complex.normSq (f M))) ^ 2 ≤ a7HybridQ f := by
  classical
  let pair : Submodule F (V d) × Submodule F (W n) := ⟨⊥, ⊤⟩
  let g : Submodule F (V d) × Submodule F (W n) → ℝ := fun p =>
    typedUniformMean (fun T : V d →ₗ[F] W n => typedW6QComponent p.1 p.2 T f)
  have hnn : ∀ p : Submodule F (V d) × Submodule F (W n), 0 ≤ g p := by
    intro p
    unfold g
    exact a7_qComponent_uniform_nonneg p.1 p.2 f
  have hadd : g pair + ∑ p ∈ Finset.univ.erase pair, g p = ∑ p, g p :=
    Finset.add_sum_erase Finset.univ g (Finset.mem_univ pair)
  have hrest : 0 ≤ ∑ p ∈ Finset.univ.erase pair, g p :=
    Finset.sum_nonneg (fun p _ => hnn p)
  have hle : g pair ≤ g pair + ∑ p ∈ Finset.univ.erase pair, g p :=
    le_add_of_nonneg_right hrest
  have hpair : g pair =
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        typedW6QComponent (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f) := by
    unfold g pair
    rfl
  have hsum : g pair ≤ ∑ p, g p := by
    rw [← hadd]
    exact hle
  have hQ : (∑ p, g p) = a7HybridQ f := by
    unfold a7HybridQ g
    rfl
  have hL : (uniformMean (fun M => Complex.normSq (f M))) ^ 2 = g pair := by
    rw [hpair]
    exact (a7_zero_order_uniform f).symm
  rw [hL, ← hQ]
  exact hsum

/-- A mixed derivative whose order exceeds the Fourier degree has fourth
moment zero. -/
theorem a7_derivative_fourth_zero_of_high {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (ht : D < a6Order t) :
    a6DerivativeFourth A B t f = 0 := by
  classical
  unfold a6DerivativeFourth
  have hzero : ∀ (T : V d →ₗ[F] W n) (M : (V d ⧸ A) →ₗ[F] B),
      typedW6FourierDerivative (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
        (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
        (t1OutputEquiv t M) = 0 :=
    fun T M => a6_mixed_zero_of_order_gt t f hsupport ht T M
  have hsumM : ∀ T : V d →ₗ[F] W n,
      (∑ M : (V d ⧸ A) →ₗ[F] B,
        Complex.normSq (typedW6FourierDerivative (t1AmbientC t.C)
          (t1AmbientH t.K) (t1PullbackMap t)
          (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
          (t1OutputEquiv t M)) ^ 2) = 0 := by
    intro T
    apply Finset.sum_eq_zero
    intro M _
    rw [hzero T M, Complex.normSq_zero]
    simp
  simp [hsumM, zero_div]

/-- One positive triple's A6 weight times the lower-degree A7 factor fits in
the terminal allowance `2^{100 D^2} * 2^{1-31 D}`. -/
theorem a7_triple_exponent_fits (D t : Nat) (ht : 0 < t) (hle : t ≤ D) :
    (2 : ℝ) ^ (24 * D * t) * (2 : ℝ) ^ (100 * (D - t) * (D - t)) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
  let L := 24 * D * t + 100 * (D - t) * (D - t)
  have hL : (L : ℤ) ≤ (100 * D * D : ℤ) + 1 - 31 * (D : ℤ) := by
    have hsub : ((D - t : ℕ) : ℤ) = (D : ℤ) - t := Nat.cast_sub hle
    have hLexp : (L : ℤ) =
        24 * (D : ℤ) * t + 100 * ((D : ℤ) - t) * ((D : ℤ) - t) := by
      simp [L, hsub, Nat.cast_add, Nat.cast_mul]
    have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have hle' : (t : ℤ) ≤ D := by exact_mod_cast hle
    nlinarith [hLexp, ht1, hle']
  have hpow : (2 : ℝ) ^ L =
      (2 : ℝ) ^ (24 * D * t) * (2 : ℝ) ^ (100 * (D - t) * (D - t)) := by
    rw [← pow_add]
  rw [← hpow]
  have hbase : (1 : ℝ) ≤ 2 := by norm_num
  have hleR : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ ((100 * D * D : ℤ) + 1 - 31 * (D : ℤ)) := by
    rw [← zpow_natCast (2 : ℝ) L]
    exact zpow_le_zpow_right₀ hbase hL
  have hadd : (2 : ℝ) ^ ((100 * D * D : ℤ) + (1 - 31 * (D : ℤ))) =
      (2 : ℝ) ^ (100 * D * D : ℤ) * (2 : ℝ) ^ (1 - 31 * (D : ℤ)) :=
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _
  have hnatR : (2 : ℝ) ^ (100 * D * D : ℤ) = (2 : ℝ) ^ (100 * D * D) :=
    zpow_natCast (2 : ℝ) (100 * D * D)
  have hexp : (100 * D * D : ℤ) + 1 - 31 * (D : ℤ) =
      (100 * D * D : ℤ) + (1 - 31 * (D : ℤ)) := by ring
  calc
    (2 : ℝ) ^ L ≤ (2 : ℝ) ^ ((100 * D * D : ℤ) + 1 - 31 * (D : ℤ)) := hleR
    _ = (2 : ℝ) ^ ((100 * D * D : ℤ) + (1 - 31 * (D : ℤ))) := by rw [hexp]
    _ = (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
      rw [hadd, hnatR]

/-- Room for one triple to carry an extra `2^{9 D t}`. That factor is large
enough for an A9 multiplicity `2^{3 D t}` and an A8 graph cost `2^{6 D k}`
once `k ≤ t`. It is not a count of those graphs. -/
theorem a7_triple_share_exponent_fits (D t : Nat) (ht : 0 < t) (hle : t ≤ D) :
    (2 : ℝ) ^ (24 * D * t) *
        ((2 : ℝ) ^ (100 * (D - t) * (D - t)) * (2 : ℝ) ^ (9 * D * t)) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
  let L := 24 * D * t + 100 * (D - t) * (D - t) + 9 * D * t
  have hL : (L : ℤ) ≤ (100 * D * D : ℤ) + 1 - 31 * (D : ℤ) := by
    have hsub : ((D - t : ℕ) : ℤ) = (D : ℤ) - t := Nat.cast_sub hle
    have hLexp : (L : ℤ) =
        24 * (D : ℤ) * t + 100 * ((D : ℤ) - t) * ((D : ℤ) - t) +
          9 * (D : ℤ) * t := by
      simp [L, hsub, Nat.cast_add, Nat.cast_mul]
    have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have hle' : (t : ℤ) ≤ D := by exact_mod_cast hle
    nlinarith [hLexp, ht1, hle']
  have hflat : (2 : ℝ) ^ L =
      (2 : ℝ) ^ (24 * D * t + 100 * (D - t) * (D - t)) * (2 : ℝ) ^ (9 * D * t) := by
    rw [← pow_add]
  have hsplit : (2 : ℝ) ^ (24 * D * t + 100 * (D - t) * (D - t)) =
      (2 : ℝ) ^ (24 * D * t) * (2 : ℝ) ^ (100 * (D - t) * (D - t)) := by
    rw [← pow_add]
  have hpow : (2 : ℝ) ^ L =
      (2 : ℝ) ^ (24 * D * t) *
        ((2 : ℝ) ^ (100 * (D - t) * (D - t)) * (2 : ℝ) ^ (9 * D * t)) := by
    rw [hflat, hsplit]
    ring
  rw [← hpow]
  have hbase : (1 : ℝ) ≤ 2 := by norm_num
  have hleR : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ ((100 * D * D : ℤ) + 1 - 31 * (D : ℤ)) := by
    rw [← zpow_natCast (2 : ℝ) L]
    exact zpow_le_zpow_right₀ hbase hL
  have hadd : (2 : ℝ) ^ ((100 * D * D : ℤ) + (1 - 31 * (D : ℤ))) =
      (2 : ℝ) ^ (100 * D * D : ℤ) * (2 : ℝ) ^ (1 - 31 * (D : ℤ)) :=
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _
  have hnatR : (2 : ℝ) ^ (100 * D * D : ℤ) = (2 : ℝ) ^ (100 * D * D) :=
    zpow_natCast (2 : ℝ) (100 * D * D)
  have hexp : (100 * D * D : ℤ) + 1 - 31 * (D : ℤ) =
      (100 * D * D : ℤ) + (1 - 31 * (D : ℤ)) := by ring
  calc
    (2 : ℝ) ^ L ≤ (2 : ℝ) ^ ((100 * D * D : ℤ) + 1 - 31 * (D : ℤ)) := hleR
    _ = (2 : ℝ) ^ ((100 * D * D : ℤ) + (1 - 31 * (D : ℤ))) := by rw [hexp]
    _ = (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
      rw [hadd, hnatR]

/-- The mixed sum follows from per-triple shares of unweighted `Q`. Each share
may be zero. Orders above `D` contribute nothing, because their fourth moment
is zero. This does not build the shares, and it does not remove the hypothesis
from `a7_positive_of_mixed_bound`. -/
theorem a7_mixed_sum_of_shares {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (c : Nat → ℝ)
    (e : (p : dr6ActualNonzeroABPairs (n := n) (d := d)) →
      T1IndexTriple p.1.1 p.1.2 → ℝ)
    (hcoeff : ∀ t : Nat, 0 < t → t ≤ D →
      (2 : ℝ) ^ (24 * D * t) * c t ≤
        (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D))
    (hfourth : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
        (t : T1IndexTriple p.1.1 p.1.2),
        0 < a6Order t → a6Order t ≤ D →
          a6DerivativeFourth p.1.1 p.1.2 t f ≤ c (a6Order t) * e p t)
    (hnn : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
        (t : T1IndexTriple p.1.1 p.1.2), 0 ≤ e p t)
    (hshare :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t ∧ a6Order t ≤ D then e p t else 0) ≤
        a7HybridQ f) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) * a7HybridQ f := by
  classical
  set allowance :=
    (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D)
  have hterm : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2),
      (if 0 < a6Order t then
        (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
      else 0) ≤
        allowance * (if 0 < a6Order t ∧ a6Order t ≤ D then e p t else 0) := by
    intro p t
    by_cases hspan : 0 < a6Order t ∧ a6Order t ≤ D
    · rw [if_pos hspan.1, if_pos hspan]
      have h4 := hfourth p t hspan.1 hspan.2
      have hco := hcoeff (a6Order t) hspan.1 hspan.2
      have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ (24 * D * a6Order t) :=
        pow_nonneg (by norm_num) _
      calc
        (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f ≤
            (2 : ℝ) ^ (24 * D * a6Order t) * (c (a6Order t) * e p t) :=
          mul_le_mul_of_nonneg_left h4 hpow0
        _ = ((2 : ℝ) ^ (24 * D * a6Order t) * c (a6Order t)) * e p t := by ring
        _ ≤ allowance * e p t := mul_le_mul_of_nonneg_right hco (hnn p t)
    · rw [if_neg hspan]
      by_cases ht0 : 0 < a6Order t
      · have hgt : D < a6Order t := by
          have hnot : ¬ a6Order t ≤ D := by
            intro hle
            exact hspan ⟨ht0, hle⟩
          exact not_le.mp hnot
        rw [if_pos ht0, a7_derivative_fourth_zero_of_high t f hsupport hgt]
        simp
      · rw [if_neg ht0]
        simp
  have hS :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t then
            (2 : ℝ) ^ (24 * D * a6Order t) *
              a6DerivativeFourth p.1.1 p.1.2 t f
          else 0) ≤
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            allowance *
              (if 0 < a6Order t ∧ a6Order t ≤ D then e p t else 0) :=
    Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun t _ => hterm p t))
  have hpull :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          allowance * (if 0 < a6Order t ∧ a6Order t ≤ D then e p t else 0)) =
        allowance *
          ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              if 0 < a6Order t ∧ a6Order t ≤ D then e p t else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
  have hallow : 0 ≤ allowance :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  exact hS.trans (by
    rw [hpull]
    exact mul_le_mul_of_nonneg_left hshare hallow)

/-- Positive-degree arithmetic closure. This is not manuscript A7: the mixed
sum is an explicit hypothesis, and discharging it is the remaining induction
step. -/
theorem a7_positive_of_mixed_bound {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hD : 0 < D)
    (hS :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t then
            (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
          else 0) ≤
        (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) * a7HybridQ f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : ℝ) ^ (100 * D * D) * a7HybridQ f := by
  have hA6 := manuscript_A6 f hsupport
  have hL2 := a7_q_ge_l2 f
  set Q := a7HybridQ f
  set fourth := uniformMean (fun M => Complex.normSq (f M) ^ 2)
  set l2 := (uniformMean (fun M => Complex.normSq (f M))) ^ 2
  set S := ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
    ∑ t : T1IndexTriple p.1.1 p.1.2,
      if 0 < a6Order t then
        (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
      else 0
  have hL : (2 : ℝ) ^ (6 * D * D) * l2 ≤ (2 : ℝ) ^ (6 * D * D) * Q :=
    mul_le_mul_of_nonneg_left hL2 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hsplit : fourth / 162 ≤ (2 : ℝ) ^ (6 * D * D) * Q +
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) * Q :=
    le_trans hA6 (add_le_add hL hS)
  have hpow : (2 : ℝ) ^ (6 * D * D) =
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ (-(94 * D * D : ℤ)) := by
    have h6z : ((6 * D * D : ℕ) : ℤ) =
        (100 * D * D : ℤ) + (-(94 * D * D : ℤ)) := by
      push_cast
      ring
    calc
      (2 : ℝ) ^ (6 * D * D) = (2 : ℝ) ^ ((6 * D * D : ℕ) : ℤ) :=
        (zpow_natCast (2 : ℝ) (6 * D * D)).symm
      _ = (2 : ℝ) ^ ((100 * D * D : ℤ) + (-(94 * D * D : ℤ))) := by rw [h6z]
      _ = (2 : ℝ) ^ (100 * D * D : ℤ) * (2 : ℝ) ^ (-(94 * D * D : ℤ)) :=
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _
      _ = (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ (-(94 * D * D : ℤ)) := by
        have hexp : (100 * (D : ℤ) * D) = ((100 * D * D : ℕ) : ℤ) := by
          push_cast
          ring
        rw [hexp, zpow_natCast]
  set c := (2 : ℝ) ^ (-(94 * D * D : ℤ)) + (2 : ℝ) ^ ((1 : ℤ) - 31 * D)
  set p := (2 : ℝ) ^ (100 * D * D)
  have hfac : (2 : ℝ) ^ (6 * D * D) * Q +
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) * Q =
      p * c * Q := by
    rw [hpow]
    ring
  have hfourth : fourth / 162 ≤ p * c * Q := by
    rw [← hfac]
    exact hsplit
  have hback : fourth = 162 * (fourth / 162) := by
    field_simp
  have hscale : fourth ≤ 162 * (p * c * Q) := by
    rw [hback]
    exact mul_le_mul_of_nonneg_left hfourth (by norm_num : (0 : ℝ) ≤ 162)
  have hprod : 162 * (p * c * Q) = (162 * c) * (p * Q) := by ring
  have hQ : 0 ≤ Q := a7HybridQ_nonneg f
  have hp : 0 ≤ p := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htail := a7_terminal_factor D hD
  have hle : (162 * c) * (p * Q) ≤ 1 * (p * Q) :=
    mul_le_mul_of_nonneg_right (le_of_lt htail) (mul_nonneg hp hQ)
  have hone : 1 * (p * Q) = p * Q := one_mul _
  rw [hprod] at hscale
  exact le_trans hscale (hle.trans (le_of_eq hone))

/-- Positive-degree closure when each triple is charged a share `e` and the
fourth moment absorbs an ambient-free overlap `2^{9 D t}`. The shares are
still a hypothesis: their sum is at most unweighted `Q`, and this is not
manuscript A7. -/
theorem a7_positive_of_overlapping_shares {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hD : 0 < D)
    (e : (p : dr6ActualNonzeroABPairs (n := n) (d := d)) →
      T1IndexTriple p.1.1 p.1.2 → ℝ)
    (hfourth : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
        (t : T1IndexTriple p.1.1 p.1.2),
        0 < a6Order t → a6Order t ≤ D →
          a6DerivativeFourth p.1.1 p.1.2 t f ≤
            (2 : ℝ) ^ (100 * (D - a6Order t) * (D - a6Order t)) *
              (2 : ℝ) ^ (9 * D * a6Order t) * e p t)
    (hnn : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
        (t : T1IndexTriple p.1.1 p.1.2), 0 ≤ e p t)
    (hshare :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t ∧ a6Order t ≤ D then e p t else 0) ≤
        a7HybridQ f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : ℝ) ^ (100 * D * D) * a7HybridQ f := by
  refine a7_positive_of_mixed_bound f hsupport hD ?_
  let c : Nat → ℝ := fun t =>
    (2 : ℝ) ^ (100 * (D - t) * (D - t)) * (2 : ℝ) ^ (9 * D * t)
  have hfourth' : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2),
      0 < a6Order t → a6Order t ≤ D →
        a6DerivativeFourth p.1.1 p.1.2 t f ≤ c (a6Order t) * e p t := by
    intro p t ht0 hle
    simpa [c, mul_assoc] using hfourth p t ht0 hle
  exact a7_mixed_sum_of_shares f hsupport c e
    (fun t ht hle => a7_triple_share_exponent_fits D t ht hle)
    hfourth' hnn hshare

/-- Fourth moment of one mixed derivative on the output carrier of its
pullback. The original pair's Hom is not the output domain. -/
def a7MixedOutputFourth {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) : ℝ :=
  a6MixedOutputFourth t T f

/-- A6's mixed fourth moment is the uniform average, over the affine base, of
the fourth moment on the actual output carrier. `t1OutputEquiv` is a bijection,
so the original Hom contributes no extra factor. -/
theorem a7_mixed_fourth_output {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex) :
    a6DerivativeFourth A B t f =
      typedUniformMean (fun T : V d →ₗ[F] W n => a7MixedOutputFourth t T f) := by
  simpa [a7MixedOutputFourth] using a6_mixed_fourth_output t f

/-- The mixed output fourth moment is the typed W6 fourth moment of the
filtered carrier. -/
theorem a7_mixed_output_fourth_typed {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    a7MixedOutputFourth t T f =
      typedW6OutputFourth (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
        (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f) := by
  unfold a7MixedOutputFourth a6MixedOutputFourth typedW6OutputFourth
  rfl

/-- That typed fourth moment is the coordinate mean of `|actual W6 derivative|^4`. -/
theorem a7_mixed_output_fourth_coordinate {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    a7MixedOutputFourth t T f =
      carrierMean
        (LinearMap.range (carrierFrequencyEquiv (t1AmbientC t.C) (t1AmbientH t.K)
          (t1PullbackMap t)).transpose.toLin')
        (LinearMap.ker (carrierFrequencyEquiv (t1AmbientC t.C) (t1AmbientH t.K)
          (t1PullbackMap t)).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (carrierFrequencyEquiv (t1AmbientC t.C)
            (t1AmbientH t.K) (t1PullbackMap t)) 0
            (fun K => filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f
              ((carrierMatrixEquiv (t1AmbientC t.C) (t1AmbientH t.K)).symm K)) M) ^ 2) := by
  rw [a7_mixed_output_fourth_typed]
  exact typedW6OutputFourth_coordinate (t1AmbientC t.C) (t1AmbientH t.K)
    (t1PullbackMap t)
    (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)

/-- Coordinate source of one mixed derivative. Its degree is the ambient
degree minus the carrier cost of the triple. -/
def a7MixedCoordinate {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    BinaryMatrix
      (Module.finrank F (t1AmbientH t.K))
      (Module.finrank F (V d ⧸ t1AmbientC t.C)) → Complex :=
  fun K => filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f
    ((carrierMatrixEquiv (t1AmbientC t.C) (t1AmbientH t.K)).symm K)

/-- Matrix representative of the triple's pullback on that coordinate space. -/
def a7MixedCoordinateParent {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    BinaryMatrix
      (Module.finrank F (t1AmbientH t.K))
      (Module.finrank F (V d ⧸ t1AmbientC t.C)) :=
  carrierFrequencyEquiv (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)

/-- The coordinate W6 derivative of a mixed triple has Fourier support through
`D` minus the mixed order. Frequencies above that rank are collisions of
ambient predecessors whose own rank exceeds the carrier support. -/
theorem a7_mixed_output_coordinate_support {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) :
    CarrierComplexFourierSupportedThrough
      (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
      (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
      (D - a6Order t)
      (actualW6Derivative (a7MixedCoordinateParent t) 0
        (a7MixedCoordinate t T f)) := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let s := Module.finrank F C + Module.finrank F (W n ⧸ H)
  let k := Module.finrank F (LinearMap.range X)
  have horder_add : a6Order t = s + k := by
    simp [a6Order, C, H, X, s, k]
  have hs : s ≤ D := by
    have hk : k ≤ s + k := Nat.le_add_left k s
    omega
  have hdrop := filteredCarrierFunction_support_drop C H T f hsupport hs
  have hcoord : ComplexFourierSupportedThrough (D - s)
      (a7MixedCoordinate t T f) :=
    (carrierFourier_support_iff_coordinate C H (D - s)
      (filteredCarrierFunction C H T f)).mp (by simpa [C, H] using hdrop)
  have hparent : (a7MixedCoordinateParent t).rank = k := by
    simpa [a7MixedCoordinateParent, C, H, X, k] using
      carrierFrequency_rank C H X
  have hgap : D - a6Order t = (D - s) - k := by
    omega
  intro Z hZ
  have hcoeff := actualW6Derivative_carrier_fourierCoeff
    (a7MixedCoordinateParent t) 0 (a7MixedCoordinate t T f) Z
  rw [hcoeff]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hprec : w6Precedes (a7MixedCoordinateParent t) Y
  · rw [if_pos hprec]
    by_cases hfreq : Z =
        (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin').mkQ.comp
          (Y.transpose.toLin'.comp
            (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin').subtype)
    · rw [if_pos hfreq]
      have hth := w6_precedes_actual_carrier_frequency_rank
        (a7MixedCoordinateParent t) Y hprec
      have hfreqId : w6ActualCarrierFrequency (a7MixedCoordinateParent t) Y = Z := by
        simpa [w6ActualCarrierFrequency] using hfreq.symm
      have hgt : (D - s) - k < (Y - a7MixedCoordinateParent t).rank := by
        rw [hgap] at hZ
        rw [← hth, hfreqId]
        exact hZ
      have hY : D - s < Y.rank := by
        have hprecRank : Y.rank =
            (a7MixedCoordinateParent t).rank +
              (Y - a7MixedCoordinateParent t).rank := hprec
        rw [hprecRank, hparent]
        omega
      have hzero : complexFourierCoeff (a7MixedCoordinate t T f) Y = 0 :=
        hcoord Y hY
      simp [hzero]
    · simp [hfreq]
  · simp [hprec]

/-- The mixed coordinate function loses the ambient carrier cost `s`. -/
theorem a7_mixed_coordinate_support {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) :
    ComplexFourierSupportedThrough
      (D - (Module.finrank F (t1AmbientC t.C) +
        Module.finrank F (W n ⧸ t1AmbientH t.K)))
      (a7MixedCoordinate t T f) := by
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let s := Module.finrank F C + Module.finrank F (W n ⧸ H)
  have hs : s ≤ D := by
    have hk : Module.finrank F (LinearMap.range (t1PullbackMap t)) ≤ a6Order t := by
      dsimp [a6Order]
      exact Nat.le_add_left _ _
    have hsplit : a6Order t =
        s + Module.finrank F (LinearMap.range (t1PullbackMap t)) := by
      simp [a6Order, C, H, s]
    omega
  have hdrop := filteredCarrierFunction_support_drop C H T f hsupport hs
  exact (carrierFourier_support_iff_coordinate C H (D - s)
    (filteredCarrierFunction C H T f)).mp (by simpa [C, H, s] using hdrop)

/-- At mixed order `D`, the output derivative is constant. Its fourth moment
is its squared carrier energy, and that energy is at most the ambient pair
share. One triple uses one share; this does not sum shares across triples. -/
theorem a7_saturated_output_le_component {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t = D) :
    a7MixedOutputFourth t T f ≤
      typedW6QComponent (t1AmbientC t.C) (t1AmbientH t.K) T f := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let s := Module.finrank F C + Module.finrank F (W n ⧸ H)
  let k := Module.finrank F (LinearMap.range X)
  let parent := a7MixedCoordinateParent t
  let coord := a7MixedCoordinate t T f
  have hsplit : a6Order t = s + k := by
    simp [a6Order, C, H, X, s, k]
  have hDk : D - s = k := by
    have hsum : D = s + k := by rw [← horder, hsplit]
    omega
  have hparent : parent.rank = k := by
    simpa [parent, a7MixedCoordinateParent, C, H, X, k] using
      carrierFrequency_rank C H X
  have hcoord := a7_mixed_coordinate_support t T f hsupport (le_of_eq horder)
  have hcoordK : ComplexFourierSupportedThrough k coord := by
    have hsdef : s = Module.finrank F C + Module.finrank F (W n ⧸ H) := rfl
    rw [← hDk, hsdef]
    simpa [coord] using hcoord
  let Cout := LinearMap.range parent.transpose.toLin'
  let Hout := LinearMap.ker parent.transpose.toLin'
  let deriv := actualW6Derivative parent 0 coord
  let hfun : BinaryMatrix (Module.finrank F Hout)
      (Module.finrank F (V (Module.finrank F (V d ⧸ C)) ⧸ Cout)) → Complex :=
    fun M => deriv ((carrierMatrixEquiv Cout Hout).symm M)
  have hbin : ComplexFourierSupportedThrough 0
      (fun M => deriv ((carrierMatrixEquiv Cout Hout).symm M)) :=
    (carrierFourier_support_iff_coordinate Cout Hout 0 deriv).mp
      (by simpa [deriv, parent, coord, horder] using
        a7_mixed_output_coordinate_support t T f hsupport (le_of_eq horder))
  have hfourthEq := a7_fourth_eq_l2_of_degree_zero
    (fun M => deriv ((carrierMatrixEquiv Cout Hout).symm M)) hbin
  have hL4 := carrierMean_coordinate Cout Hout
    (fun M => Complex.normSq (deriv M) ^ 2)
  have hL2 := carrierComplexEnergy_coordinate Cout Hout deriv
  have hsq :=
    ActualBinaryMatrixHC46A7EnergyConsumer.actualW6Derivative_energy_sq_le_degree_predecessorFourierEnergy
      (D := k) parent 0 coord hcoordK
  have hexp0 : 4 * parent.rank * (k - parent.rank) = 0 := by
    rw [hparent]
    simp
  have hpow0 : (2 : ℝ) ^ (4 * parent.rank * (k - parent.rank)) = 1 := by
    rw [hexp0]
    simp
  let E := uniformMean (fun M => Complex.normSq (coord M))
  let aEnergy :=
    ActualBinaryMatrixHC46A7EnergyConsumer.w6PredecessorFourierEnergy parent coord
  have ha : aEnergy ≤ E := by
    simpa [aEnergy, E, coord] using
      ActualBinaryMatrixHC46A7EnergyConsumer.w6PredecessorFourierEnergy_le_uniformMean
        parent coord
  have hE : 0 ≤ E := by
    unfold E uniformMean
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have henergy : (carrierMean Cout Hout (fun M => Complex.normSq (deriv M))) ^ 2 ≤
      E ^ 2 := by
    have hbase :
        (carrierMean Cout Hout (fun M => Complex.normSq (deriv M))) ^ 2 ≤
          (2 : ℝ) ^ (4 * parent.rank * (k - parent.rank)) * E * aEnergy := by
      simpa [Cout, Hout, deriv, E, aEnergy, parent, coord] using hsq
    have hstep : (2 : ℝ) ^ (4 * parent.rank * (k - parent.rank)) * E * aEnergy ≤
        E * aEnergy := by
      rw [hpow0]
      simp
    have hmul : E * aEnergy ≤ E * E :=
      mul_le_mul_of_nonneg_left ha hE
    have hsquare : E * E = E ^ 2 := by ring
    exact le_trans hbase (le_trans hstep (hsquare ▸ hmul))
  have hEshare : E ^ 2 = typedW6QComponent C H T f := by
    have hmean := carrierComplexEnergy_coordinate C H
      (filteredCarrierFunction C H T f)
    have hEq : E =
        carrierMean C H (fun M => Complex.normSq (filteredCarrierFunction C H T f M)) := by
      simpa [E, coord, a7MixedCoordinate, C, H] using hmean.symm
    unfold typedW6QComponent
    rw [← hEq]
  have hfourMean : a7MixedOutputFourth t T f =
      uniformMean (fun M =>
        Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M)) ^ 2) := by
    rw [a7_mixed_output_fourth_coordinate]
    change carrierMean Cout Hout (fun M => Complex.normSq (deriv M) ^ 2) =
      uniformMean (fun M =>
        Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M)) ^ 2)
    exact hL4
  rw [hfourMean, hfourthEq]
  have hL2eq : uniformMean (fun M =>
      Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M))) =
      carrierMean Cout Hout (fun M => Complex.normSq (deriv M)) := hL2.symm
  rw [hL2eq]
  exact henergy.trans (le_of_eq hEshare)

/-- Saturated mixed order charges at most the ambient pair share. -/
theorem a7_saturated_fourth_le_share {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t = D) :
    a6DerivativeFourth A B t f ≤
      a7PairShare (t1AmbientC t.C) (t1AmbientH t.K) f := by
  classical
  rw [a7_mixed_fourth_output, a7PairShare]
  unfold typedUniformMean
  have hpt : ∀ T : V d →ₗ[F] W n,
      a7MixedOutputFourth t T f ≤
        typedW6QComponent (t1AmbientC t.C) (t1AmbientH t.K) T f :=
    fun T => a7_saturated_output_le_component t T f hsupport horder
  have hsum := Finset.sum_le_sum (fun T (_ : T ∈ Finset.univ) => hpt T)
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
