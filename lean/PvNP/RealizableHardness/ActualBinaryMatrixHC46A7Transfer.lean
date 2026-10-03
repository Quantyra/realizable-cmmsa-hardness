import PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph
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
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A9InitialGraph
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Moment
open PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixA1Composition
open PvNP.RealizableHardness.BinaryMatrixA1Phase
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

/-- Squared output carrier energy is at most `2^{4 k (D - order)}` times the
ambient pair's `Q` component. This bounds the squared `L2` energy, not the
fourth moment, except at order `D` where the derivative is constant. -/
theorem a7_output_energy_sq_le_component {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) :
    (carrierMean
        (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
        (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (a7MixedCoordinateParent t) 0
            (a7MixedCoordinate t T f) M))) ^ 2 ≤
      (2 : ℝ) ^ (4 * Module.finrank F (LinearMap.range (t1PullbackMap t)) *
        (D - a6Order t)) *
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
  have hsle : s + k ≤ D := by rwa [← hsplit]
  have hparent : parent.rank = k := by
    simpa [parent, a7MixedCoordinateParent, C, H, X, k] using
      carrierFrequency_rank C H X
  have hcoord := a7_mixed_coordinate_support t T f hsupport horder
  have hsq :=
    ActualBinaryMatrixHC46A7EnergyConsumer.actualW6Derivative_energy_sq_le_degree_predecessorFourierEnergy
      (D := D - s) parent 0 coord (by
        have hsdef : s = Module.finrank F C + Module.finrank F (W n ⧸ H) := rfl
        simpa [coord, hsdef] using hcoord)
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
  have hexp : 4 * parent.rank * ((D - s) - parent.rank) =
      4 * k * (D - a6Order t) := by
    rw [hparent]
    have hsub : (D - s) - k = D - (s + k) := by
      have hk : k ≤ D - s := by omega
      omega
    rw [hsub, hsplit]
  have hbase :
      (carrierMean (LinearMap.range parent.transpose.toLin')
          (LinearMap.ker parent.transpose.toLin')
          (fun M => Complex.normSq (actualW6Derivative parent 0 coord M))) ^ 2 ≤
        (2 : ℝ) ^ (4 * parent.rank * ((D - s) - parent.rank)) * E * aEnergy := by
    simpa [E, aEnergy, parent, coord] using hsq
  have hEa : E * aEnergy ≤ E * E := mul_le_mul_of_nonneg_left ha hE
  have hfactor :
      (2 : ℝ) ^ (4 * parent.rank * ((D - s) - parent.rank)) * E * aEnergy ≤
        (2 : ℝ) ^ (4 * k * (D - a6Order t)) * (E * E) := by
    rw [hexp]
    have hleft :
        (2 : ℝ) ^ (4 * k * (D - a6Order t)) * E * aEnergy =
          (2 : ℝ) ^ (4 * k * (D - a6Order t)) * (E * aEnergy) := by ring
    have hright :
        (2 : ℝ) ^ (4 * k * (D - a6Order t)) * (E * E) =
          (2 : ℝ) ^ (4 * k * (D - a6Order t)) * (E * E) := rfl
    rw [hleft]
    exact mul_le_mul_of_nonneg_left hEa
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hEshare : E ^ 2 = typedW6QComponent C H T f := by
    have hmean := carrierComplexEnergy_coordinate C H
      (filteredCarrierFunction C H T f)
    have hEq : E =
        carrierMean C H (fun M =>
          Complex.normSq (filteredCarrierFunction C H T f M)) := by
      simpa [E, coord, a7MixedCoordinate, C, H] using hmean.symm
    unfold typedW6QComponent
    rw [← hEq]
  have hsquare : E * E = E ^ 2 := by ring
  have hle := le_trans hbase hfactor
  rw [hsquare, hEshare] at hle
  simpa [parent, coord, C, H, X, k] using hle

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

/-- At mixed order `D`, the output fourth moment is the squared W6 energy of
this triple's pullback parent. -/
theorem a7_saturated_output_eq_energy_sq {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t = D) :
    a7MixedOutputFourth t T f =
      (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
        (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2 := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let parent := a7MixedCoordinateParent t
  let coord := a7MixedCoordinate t T f
  let Cout := LinearMap.range parent.transpose.toLin'
  let Hout := LinearMap.ker parent.transpose.toLin'
  let deriv := actualW6Derivative parent 0 coord
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
  have hfourMean : a7MixedOutputFourth t T f =
      uniformMean (fun M =>
        Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M)) ^ 2) := by
    rw [a7_mixed_output_fourth_coordinate]
    change carrierMean Cout Hout (fun M => Complex.normSq (deriv M) ^ 2) =
      uniformMean (fun M =>
        Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M)) ^ 2)
    exact hL4
  have hL2eq : uniformMean (fun M =>
      Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M))) =
      carrierMean Cout Hout (fun M => Complex.normSq (deriv M)) := hL2.symm
  have hsqMean : a7MixedOutputFourth t T f =
      (carrierMean Cout Hout (fun M => Complex.normSq (deriv M))) ^ 2 := by
    rw [hfourMean, hfourthEq, hL2eq]
  have hE := typedW6OutputEnergy_coordinate C H X
    (filteredCarrierFunction C H T f)
  have hcarrier : typedW6OutputEnergy C H X (filteredCarrierFunction C H T f) =
      carrierMean Cout Hout (fun M => Complex.normSq (deriv M)) := by
    rw [hE]
    rfl
  rw [hsqMean, hcarrier]

/-- One saturated output fourth moment is one nonnegative term of that
carrier's parent-energy pool. -/
theorem a7_saturated_output_le_pool {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t = D) :
    a7MixedOutputFourth t T f ≤
      ∑ Z : (t1AmbientH t.K) →ₗ[F] (V d ⧸ t1AmbientC t.C),
        (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) Z
          (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2 := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let g : (H →ₗ[F] (V d ⧸ C)) → ℝ := fun Z =>
    (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)) ^ 2
  have hnn : ∀ Z : H →ₗ[F] (V d ⧸ C), 0 ≤ g Z := fun _ => sq_nonneg _
  have hadd : g X + ∑ Z ∈ Finset.univ.erase X, g Z = ∑ Z, g Z :=
    Finset.add_sum_erase Finset.univ g (Finset.mem_univ X)
  have hrest : 0 ≤ ∑ Z ∈ Finset.univ.erase X, g Z :=
    Finset.sum_nonneg (fun Z _ => hnn Z)
  have hle : g X ≤ ∑ Z, g Z := by
    rw [← hadd]
    exact le_add_of_nonneg_right hrest
  have hX : g X = a7MixedOutputFourth t T f := by
    unfold g
    exact (a7_saturated_output_eq_energy_sq t T f hsupport horder).symm
  have hsum : (∑ Z, g Z) =
      ∑ Z : H →ₗ[F] (V d ⧸ C),
        (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)) ^ 2 := by
    unfold g
    rfl
  rw [← hX, hsum]
  exact hle

/-- On one ordinary pair, the ambient carrier and the pullback determine the
triple. Two saturated fourth moments on that pair cannot charge one parent
twice. -/
theorem a7_same_pair_parent_unique {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t s : T1IndexTriple A B)
    (hC : t1AmbientC t.C = t1AmbientC s.C)
    (hH : t1AmbientH t.K = t1AmbientH s.K)
    (hX : ∀ h : t1AmbientH t.K,
      t1PullbackMap t h =
        hC.symm ▸ t1PullbackMap s ⟨h.1, by
          rw [← hH]
          exact h.2⟩) :
    t = s := by
  cases t with
  | mk tC tK tXbar =>
    cases s with
    | mk sC sK sXbar =>
      have hCint : tC = sC := by
        ext a
        constructor
        · intro ha
          have hmem : (a : V d) ∈ t1AmbientC sC := by
            rw [← hC]
            exact ⟨a, ha, rfl⟩
          rcases hmem with ⟨a', ha', hval⟩
          have haa : a = a' := Subtype.ext hval.symm
          simpa [haa] using ha'
        · intro ha
          have hmem : (a : V d) ∈ t1AmbientC tC := by
            rw [hC]
            exact ⟨a, ha, rfl⟩
          rcases hmem with ⟨a', ha', hval⟩
          have haa : a = a' := Subtype.ext hval.symm
          simpa [haa] using ha'
      subst sC
      have hKint : tK = sK := by
        ext x
        have ht := t1AmbientH_quotientRange B tK
        have hs := t1AmbientH_quotientRange B sK
        constructor
        · intro hx
          rw [← hs]
          have hx' : x ∈ LinearMap.range
              ((Submodule.mkQ B).comp (t1AmbientH tK).subtype) := by
            rw [ht]
            exact hx
          rcases hx' with ⟨w, hw⟩
          refine ⟨⟨w.1, ?_⟩, ?_⟩
          · rw [← hH]
            exact w.2
          · simpa using hw
        · intro hx
          rw [← ht]
          have hx' : x ∈ LinearMap.range
              ((Submodule.mkQ B).comp (t1AmbientH sK).subtype) := by
            rw [hs]
            exact hx
          rcases hx' with ⟨w, hw⟩
          refine ⟨⟨w.1, ?_⟩, ?_⟩
          · rw [hH]
            exact w.2
          · simpa using hw
      subst sK
      have hmap : t1TripleToMap ⟨tC, tK, tXbar⟩ =
          t1TripleToMap ⟨tC, tK, sXbar⟩ := by
        apply LinearMap.ext
        intro a
        let y : tK := tXbar.symm (tC.mkQ a)
        let q := (t1AmbientHQuotientEquiv B tK).symm y
        obtain ⟨h, hq⟩ := Submodule.mkQ_surjective
          (B.comap (t1AmbientH tK).subtype) q
        have hpullT : t1PullbackMap ⟨tC, tK, tXbar⟩ h =
            Submodule.mkQ (t1AmbientC tC) a.val := by
          have hy : t1AmbientHQuotientEquiv B tK
              (Submodule.mkQ (B.comap (t1AmbientH tK).subtype) h) = y := by
            rw [hq]
            exact (t1AmbientHQuotientEquiv B tK).apply_symm_apply y
          change t1AQuotientToAmbient tC
              (tXbar (t1AmbientHQuotientEquiv B tK
                (Submodule.mkQ _ h))) =
            Submodule.mkQ (t1AmbientC tC) a.val
          rw [hy]
          rw [tXbar.apply_symm_apply]
          exact t1AQuotientToAmbient_apply_mk tC a
        have hmapT :=
          (t1TripleToMap_pullback_iff ⟨tC, tK, tXbar⟩ a h).2 hpullT
        have hpullS : t1PullbackMap ⟨tC, tK, sXbar⟩ h =
            Submodule.mkQ (t1AmbientC tC) a.val := by
          have htrans := hX h
          simpa [hC, hpullT] using htrans.symm
        have hmapS :=
          (t1TripleToMap_pullback_iff ⟨tC, tK, sXbar⟩ a h).2 hpullS
        calc
          t1TripleToMap ⟨tC, tK, tXbar⟩ a = Submodule.mkQ B h.val := hmapT
          _ = t1TripleToMap ⟨tC, tK, sXbar⟩ a := hmapS.symm
      have htriple := t1TripleToMap_injective hmap
      exact htriple

/-- Rewriting the ambient carrier does not change the pullback energy. -/
theorem a7_output_energy_carrier_cast {n d : Nat}
    (C1 C2 : Submodule F (V d)) (H1 H2 : Submodule F (W n))
    (hC : C1 = C2) (hH : H1 = H2)
    (Z : H1 →ₗ[F] (V d ⧸ C1)) (Z' : H2 →ₗ[F] (V d ⧸ C2))
    (hZ : HEq Z Z') (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex) :
    typedW6OutputEnergy C1 H1 Z (filteredCarrierFunction C1 H1 T f) =
      typedW6OutputEnergy C2 H2 Z' (filteredCarrierFunction C2 H2 T f) := by
  subst hC
  subst hH
  cases hZ
  rfl

/-- The ambient image of an internal subspace determines that subspace. -/
theorem a7_ambientC_injective {d : Nat} {A : Submodule F (V d)}
    {C1 C2 : Submodule F A} (h : t1AmbientC C1 = t1AmbientC C2) : C1 = C2 := by
  ext a
  constructor
  · intro ha
    have hmem : (a : V d) ∈ t1AmbientC C2 := by
      rw [← h]
      exact ⟨a, ha, rfl⟩
    rcases hmem with ⟨a', ha', hval⟩
    have haa : a = a' := Subtype.ext hval.symm
    simpa [haa] using ha'
  · intro ha
    have hmem : (a : V d) ∈ t1AmbientC C1 := by
      rw [h]
      exact ⟨a, ha, rfl⟩
    rcases hmem with ⟨a', ha', hval⟩
    have haa : a = a' := Subtype.ext hval.symm
    simpa [haa] using ha'

/-- On one ordinary codomain, the ambient `H` determines the quotient
subspace. -/
theorem a7_ambientH_injective {n : Nat} {B : Submodule F (W n)}
    {K1 K2 : Submodule F (W n ⧸ B)}
    (h : t1AmbientH K1 = t1AmbientH K2) : K1 = K2 := by
  ext x
  have h1 := t1AmbientH_quotientRange B K1
  have h2 := t1AmbientH_quotientRange B K2
  constructor
  · intro hx
    rw [← h2]
    have hx' : x ∈ LinearMap.range
        ((Submodule.mkQ B).comp (t1AmbientH K1).subtype) := by
      rw [h1]
      exact hx
    rcases hx' with ⟨w, hw⟩
    refine ⟨⟨w.1, ?_⟩, ?_⟩
    · rw [← h]
      exact w.2
    · simpa using hw
  · intro hx
    rw [← h1]
    have hx' : x ∈ LinearMap.range
        ((Submodule.mkQ B).comp (t1AmbientH K2).subtype) := by
      rw [h2]
      exact hx
    rcases hx' with ⟨w, hw⟩
    refine ⟨⟨w.1, ?_⟩, ?_⟩
    · rw [h]
      exact w.2
    · simpa using hw

/-- Move a pullback to the carrier named by field equalities.
The body is `Eq.rec`. Unfold it only after those equalities are `rfl`. -/
def a7PullbackAt {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (c0 : Submodule F A) (k0 : Submodule F (W n ⧸ B))
    (t : T1IndexTriple A B) (hC : t.C = c0) (hK : t.K = k0) :
    t1AmbientH k0 →ₗ[F] (V d ⧸ t1AmbientC c0) :=
  hK ▸ hC ▸ t1PullbackMap t

/-- At mixed order `D`, a triple's output fourth moment is the squared energy
of its pullback on the carrier named by its internal fields. -/
theorem a7_pullback_at_fourth {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (c0 : Submodule F A) (k0 : Submodule F (W n ⧸ B))
    (t : T1IndexTriple A B) (hC : t.C = c0) (hK : t.K = k0)
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t = D) :
    a7MixedOutputFourth t T f =
      (typedW6OutputEnergy (t1AmbientC c0) (t1AmbientH k0)
        (a7PullbackAt c0 k0 t hC hK)
        (filteredCarrierFunction (t1AmbientC c0) (t1AmbientH k0) T f)) ^ 2 := by
  cases t with
  | mk tC tK tX =>
    have hCf : tC = c0 := hC
    have hKf : tK = k0 := hK
    subst tC
    subst tK
    exact a7_saturated_output_eq_energy_sq ⟨c0, k0, tX⟩ T f hsupport horder

/-- Equal transported pullbacks on one ordinary pair come from one triple. -/
theorem a7_pullback_at_injective {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (c0 : Submodule F A) (k0 : Submodule F (W n ⧸ B))
    (t s : T1IndexTriple A B)
    (hCt : t.C = c0) (hCs : s.C = c0) (hKt : t.K = k0) (hKs : s.K = k0)
    (hφ : a7PullbackAt c0 k0 t hCt hKt = a7PullbackAt c0 k0 s hCs hKs) :
    t = s := by
  cases t with
  | mk tC tK tX =>
    cases s with
    | mk sC sK sX =>
      have hCtf : tC = c0 := hCt
      have hCsf : sC = c0 := hCs
      have hKtf : tK = k0 := hKt
      have hKsf : sK = k0 := hKs
      subst tC
      subst sC
      subst tK
      subst sK
      have hmaps : t1PullbackMap ⟨c0, k0, tX⟩ =
          t1PullbackMap ⟨c0, k0, sX⟩ := by
        unfold a7PullbackAt at hφ
        exact hφ
      apply a7_same_pair_parent_unique ⟨c0, k0, tX⟩ ⟨c0, k0, sX⟩ rfl rfl
      intro h
      have hpoint : t1PullbackMap ⟨c0, k0, tX⟩ h =
          t1PullbackMap ⟨c0, k0, sX⟩ h :=
        DFunLike.congr_fun hmaps h
      simpa using hpoint

/-- A parent pullback, transported onto one carrier by `HEq`, reconstructs
the ordinary pair. -/
theorem a7_parent_reconstructs_pair {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (t : T1IndexTriple A B)
    (hC : t1AmbientC t.C = C) (hH : t1AmbientH t.K = H)
    (Z : H →ₗ[F] (V d ⧸ C)) (hZ : HEq (t1PullbackMap t) Z) :
    Submodule.comap (Submodule.mkQ C) (LinearMap.range Z) = A ∧
      Submodule.map H.subtype (LinearMap.ker Z) = B := by
  subst hC
  subst hH
  cases hZ
  exact a6_reconstruct_forward t

/-- Equal ambient carriers and `HEq` pullbacks come from one ordinary pair and
one triple. Pairs are not yet summed. -/
theorem a7_global_parent_unique {n d : Nat}
    {A A' : Submodule F (V d)} {B B' : Submodule F (W n)}
    (t : T1IndexTriple A B) (s : T1IndexTriple A' B')
    (hC : t1AmbientC t.C = t1AmbientC s.C)
    (hH : t1AmbientH t.K = t1AmbientH s.K)
    (hZ : HEq (t1PullbackMap t) (t1PullbackMap s)) :
    A = A' ∧ B = B' ∧ HEq t s := by
  have ht := a6_reconstruct_forward t
  have hs := a7_parent_reconstructs_pair (t1AmbientC t.C) (t1AmbientH t.K) s
    hC.symm hH.symm (t1PullbackMap t) hZ.symm
  have hA : A = A' := ht.1.symm.trans hs.1
  have hB : B = B' := ht.2.symm.trans hs.2
  subst A'
  subst B'
  refine ⟨rfl, rfl, ?_⟩
  cases t with
  | mk tC tK tX =>
    cases s with
    | mk sC sK sX =>
      have hCf : tC = sC := a7_ambientC_injective hC
      have hKf : tK = sK := a7_ambientH_injective hH
      subst sC
      subst sK
      have hmaps : t1PullbackMap ⟨tC, tK, tX⟩ =
          t1PullbackMap ⟨tC, tK, sX⟩ := eq_of_heq hZ
      apply heq_of_eq
      apply a7_same_pair_parent_unique ⟨tC, tK, tX⟩ ⟨tC, tK, sX⟩ rfl rfl
      intro h
      have hpoint : t1PullbackMap ⟨tC, tK, tX⟩ h =
          t1PullbackMap ⟨tC, tK, sX⟩ h :=
        DFunLike.congr_fun hmaps h
      simpa using hpoint

/-- Every parent derivative on one carrier has squared energy adding to at
most `2^{6 D^2 + 1}` times that carrier's `Q` component. High-rank parents
vanish. This is the W6 pool on one pair; it does not inject triples into
parents, so it does not discharge the mixed sum. -/
theorem a7_carrier_energy_sq_sum_le {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ Z : B →ₗ[F] (V d ⧸ A),
        (typedW6OutputEnergy A B Z (filteredCarrierFunction A B T f)) ^ 2) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent A B T f := by
  classical
  let g := filteredCarrierFunction A B T f
  have hW6 := typedW6FilteredCarrierFunction_le_two A B T f hsupport
  have hcomp : (carrierMean A B (fun M => Complex.normSq (g M))) ^ 2 =
      typedW6QComponent A B T f := by
    unfold typedW6QComponent g
    rfl
  have hweighted :
      (∑ Z : B →ₗ[F] (V d ⧸ A),
          (typedW6OutputEnergy A B Z g) ^ 2 /
            (2 : ℝ) ^ (6 * D * (carrierFrequencyEquiv A B Z).rank)) ≤
        2 * typedW6QComponent A B T f := by
    rw [← hcomp]
    simpa [g] using hW6
  have hterm : ∀ Z : B →ₗ[F] (V d ⧸ A),
      (typedW6OutputEnergy A B Z g) ^ 2 ≤
        (2 : ℝ) ^ (6 * D * D) *
          ((typedW6OutputEnergy A B Z g) ^ 2 /
            (2 : ℝ) ^ (6 * D * (carrierFrequencyEquiv A B Z).rank)) := by
    intro Z
    let r := (carrierFrequencyEquiv A B Z).rank
    by_cases hr : r ≤ D
    · have hpow : (2 : ℝ) ^ (6 * D * r) ≤ (2 : ℝ) ^ (6 * D * D) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (Nat.mul_le_mul_left (6 * D) hr)
      have hden : (0 : ℝ) < (2 : ℝ) ^ (6 * D * r) := by positivity
      have hident : (typedW6OutputEnergy A B Z g) ^ 2 =
          (2 : ℝ) ^ (6 * D * r) *
            ((typedW6OutputEnergy A B Z g) ^ 2 / (2 : ℝ) ^ (6 * D * r)) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hden)]
      have hnn : 0 ≤ (typedW6OutputEnergy A B Z g) ^ 2 /
          (2 : ℝ) ^ (6 * D * r) :=
        div_nonneg (sq_nonneg _) (le_of_lt hden)
      conv_lhs => rw [hident]
      exact mul_le_mul_of_nonneg_right hpow hnn
    · have hgt : D < r := not_le.mp hr
      have hsup :=
        ActualBinaryMatrixHC46A20SquareSupport.filteredCarrierFunction_supportedThrough
          A B T f hsupport
      have hg : ComplexFourierSupportedThrough D
          (fun K => g ((carrierMatrixEquiv A B).symm K)) :=
        (carrierFourier_support_iff_coordinate A B D g).mp hsup
      have hE0 :=
        ActualBinaryMatrixHC46A7EnergyConsumer.actualW6Derivative_energy_eq_zero_of_rank_gt
          (carrierFrequencyEquiv A B Z) 0
          (fun K => g ((carrierMatrixEquiv A B).symm K)) hg hgt
      have hcoord := typedW6OutputEnergy_coordinate A B Z g
      have hzero : typedW6OutputEnergy A B Z g = 0 := by
        rw [hcoord]
        simpa [g] using hE0
      rw [hzero]
      simp
  have hsum : (∑ Z : B →ₗ[F] (V d ⧸ A), (typedW6OutputEnergy A B Z g) ^ 2) ≤
      (2 : ℝ) ^ (6 * D * D) *
        ∑ Z : B →ₗ[F] (V d ⧸ A),
          (typedW6OutputEnergy A B Z g) ^ 2 /
            (2 : ℝ) ^ (6 * D * (carrierFrequencyEquiv A B Z).rank) := by
    calc
      _ ≤ ∑ Z : B →ₗ[F] (V d ⧸ A),
            (2 : ℝ) ^ (6 * D * D) *
              ((typedW6OutputEnergy A B Z g) ^ 2 /
                (2 : ℝ) ^ (6 * D * (carrierFrequencyEquiv A B Z).rank)) :=
          Finset.sum_le_sum (fun Z _ => hterm Z)
      _ = (2 : ℝ) ^ (6 * D * D) *
            ∑ Z : B →ₗ[F] (V d ⧸ A),
              (typedW6OutputEnergy A B Z g) ^ 2 /
                (2 : ℝ) ^ (6 * D * (carrierFrequencyEquiv A B Z).rank) := by
          rw [Finset.mul_sum]
  have htwo : (2 : ℝ) ^ (6 * D * D) * (2 * typedW6QComponent A B T f) =
      (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent A B T f := by
    rw [pow_succ]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hweighted
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * D * D))
  rw [htwo] at hscaled
  exact le_trans hsum hscaled

/-- On one ordinary pair, saturated triples with one internal carrier inject
into distinct parents. Their output fourth moments at one base sum to at most
that carrier's parent-energy pool. Orders below `D` are not included. -/
theorem a7_saturated_same_field_output_sum_le {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (c0 : Submodule F A) (k0 : Submodule F (W n ⧸ B))
    (ts : Finset (T1IndexTriple A B))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : ∀ t ∈ ts, a6Order t = D)
    (hC : ∀ t ∈ ts, t.C = c0) (hK : ∀ t ∈ ts, t.K = k0) :
    (∑ t ∈ ts, a7MixedOutputFourth t T f) ≤
      ∑ Z : t1AmbientH k0 →ₗ[F] (V d ⧸ t1AmbientC c0),
        (typedW6OutputEnergy (t1AmbientC c0) (t1AmbientH k0) Z
          (filteredCarrierFunction (t1AmbientC c0) (t1AmbientH k0) T f)) ^ 2 := by
  classical
  let C := t1AmbientC c0
  let H := t1AmbientH k0
  let φ : {t : T1IndexTriple A B // t ∈ ts} → (H →ₗ[F] (V d ⧸ C)) :=
    fun u => a7PullbackAt c0 k0 u.1 (hC u.1 u.2) (hK u.1 u.2)
  let genergy : (H →ₗ[F] (V d ⧸ C)) → ℝ := fun Z =>
    (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)) ^ 2
  have hinj : Function.Injective φ := by
    intro u v huv
    apply Subtype.ext
    exact a7_pullback_at_injective c0 k0 u.1 v.1
      (hC u.1 u.2) (hC v.1 v.2) (hK u.1 u.2) (hK v.1 v.2) huv
  have hterm : ∀ u : {t : T1IndexTriple A B // t ∈ ts},
      a7MixedOutputFourth u.1 T f = genergy (φ u) := by
    intro u
    exact a7_pullback_at_fourth c0 k0 u.1 (hC u.1 u.2) (hK u.1 u.2)
      T f hsupport (horder u.1 u.2)
  have hsumφ : (∑ u ∈ ts.attach, a7MixedOutputFourth u.1 T f) =
      ∑ u ∈ ts.attach, genergy (φ u) :=
    Finset.sum_congr rfl (fun u _ => hterm u)
  have himage : (∑ Z ∈ ts.attach.image φ, genergy Z) =
      ∑ u ∈ ts.attach, genergy (φ u) :=
    Finset.sum_image (f := genergy) (hinj.injOn (s := (ts.attach : Set _)))
  have hrest : (∑ Z ∈ ts.attach.image φ, genergy Z) ≤ ∑ Z, genergy Z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun Z _ _ => sq_nonneg
        (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)))
  calc
    (∑ t ∈ ts, a7MixedOutputFourth t T f)
        = ∑ u ∈ ts.attach, a7MixedOutputFourth u.1 T f :=
          (Finset.sum_attach (s := ts)
            (f := fun t => a7MixedOutputFourth t T f)).symm
    _ = ∑ u ∈ ts.attach, genergy (φ u) := hsumφ
    _ = ∑ Z ∈ ts.attach.image φ, genergy Z := himage.symm
    _ ≤ ∑ Z, genergy Z := hrest

/-- Saturated fourth moments on one ordinary pair, for triples with one
internal carrier, sum to at most the W6 pool factor times that carrier's pair
share. This is one pair and order `D` only. It does not discharge the mixed
sum, and it does not remove the share hypothesis. -/
theorem a7_saturated_same_field_fourth_sum_le {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (c0 : Submodule F A) (k0 : Submodule F (W n ⧸ B))
    (ts : Finset (T1IndexTriple A B))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : ∀ t ∈ ts, a6Order t = D)
    (hC : ∀ t ∈ ts, t.C = c0) (hK : ∀ t ∈ ts, t.K = k0) :
    (∑ t ∈ ts, a6DerivativeFourth A B t f) ≤
      (2 : ℝ) ^ (6 * D * D + 1) *
        a7PairShare (t1AmbientC c0) (t1AmbientH k0) f := by
  classical
  let C := t1AmbientC c0
  let H := t1AmbientH k0
  let card : ℝ := Fintype.card (V d →ₗ[F] W n)
  have hT : ∀ T : V d →ₗ[F] W n,
      (∑ t ∈ ts, a7MixedOutputFourth t T f) ≤
        (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f := by
    intro T
    exact le_trans
      (a7_saturated_same_field_output_sum_le c0 k0 ts T f hsupport horder hC hK)
      (a7_carrier_energy_sq_sum_le C H T f hsupport)
  have hderiv : ∀ t ∈ ts, a6DerivativeFourth A B t f =
      (∑ T : V d →ₗ[F] W n, a7MixedOutputFourth t T f) / card := by
    intro t _
    rw [a7_mixed_fourth_output]
    rfl
  calc
    (∑ t ∈ ts, a6DerivativeFourth A B t f)
        = ∑ t ∈ ts, (∑ T : V d →ₗ[F] W n, a7MixedOutputFourth t T f) / card := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          exact hderiv t ht
    _ = (∑ t ∈ ts, ∑ T : V d →ₗ[F] W n, a7MixedOutputFourth t T f) / card := by
          rw [Finset.sum_div]
    _ = (∑ T : V d →ₗ[F] W n, ∑ t ∈ ts, a7MixedOutputFourth t T f) / card := by
          rw [Finset.sum_comm]
    _ ≤ (∑ T : V d →ₗ[F] W n,
          (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f) / card := by
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          refine Finset.sum_le_sum ?_
          intro T _
          exact hT T
    _ = (2 : ℝ) ^ (6 * D * D + 1) *
          ((∑ T : V d →ₗ[F] W n, typedW6QComponent C H T f) / card) := by
          rw [← Finset.mul_sum, mul_div_assoc]
    _ = (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare C H f := by
          rw [a7PairShare, typedUniformMean]

/-- Saturated fourth moments on one ordinary pair, for triples whose ambient
carrier is one fixed pair, sum to at most the W6 pool factor times that pair
share. Parents are not charged twice: `a7_same_pair_parent_unique` supplies
the injection. Other ordinary pairs and orders below `D` stay outside this
sum. -/
theorem a7_saturated_carrier_fourth_sum_le {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (ts : Finset (T1IndexTriple A B))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : ∀ t ∈ ts, a6Order t = D)
    (hC : ∀ t ∈ ts, t1AmbientC t.C = C)
    (hH : ∀ t ∈ ts, t1AmbientH t.K = H) :
    (∑ t ∈ ts, a6DerivativeFourth A B t f) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare C H f := by
  classical
  rcases Finset.eq_empty_or_nonempty ts with hempty | ⟨t0, ht0⟩
  · rw [hempty, Finset.sum_empty]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (a7_pair_share_nonneg C H f)
  · have hCfield : ∀ t ∈ ts, t.C = t0.C := by
      intro t ht
      exact a7_ambientC_injective ((hC t ht).trans (hC t0 ht0).symm)
    have hKfield : ∀ t ∈ ts, t.K = t0.K := by
      intro t ht
      exact a7_ambientH_injective ((hH t ht).trans (hH t0 ht0).symm)
    have hsum := a7_saturated_same_field_fourth_sum_le t0.C t0.K ts f
      hsupport horder hCfield hKfield
    rw [hC t0 ht0, hH t0 ht0] at hsum
    exact hsum

/-- The order-`D` A6 weight times the W6 pool factor fits in the terminal
allowance. This is the numeric room for one carrier's parent-energy sum. It
does not identify mixed fourth moments with those parents. -/
theorem a7_saturated_pool_exponent_fits (D : Nat) (hD : 0 < D) :
    (2 : ℝ) ^ (24 * D * D) * (2 : ℝ) ^ (6 * D * D + 1) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
  let L := 24 * D * D + (6 * D * D + 1)
  have hL : (L : ℤ) ≤ (100 * D * D : ℤ) + 1 - 31 * (D : ℤ) := by
    have hLexp : (L : ℤ) = 30 * (D : ℤ) * D + 1 := by
      simp [L, Nat.cast_add, Nat.cast_mul]
      ring
    have hD1 : (1 : ℤ) ≤ D := by exact_mod_cast hD
    nlinarith [hLexp, hD1]
  have hflat : (2 : ℝ) ^ L =
      (2 : ℝ) ^ (24 * D * D) * (2 : ℝ) ^ (6 * D * D + 1) := by
    rw [← pow_add]
  rw [← hflat]
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

/-- Move a pullback onto a named ambient carrier.
The body is `Eq.rec`. Unfold it only after those equalities are `rfl`. -/
def a7CarrierParent {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (hC : t1AmbientC t.C = C) (hH : t1AmbientH t.K = H) :
    H →ₗ[F] (V d ⧸ C) :=
  hH ▸ hC ▸ t1PullbackMap t

/-- The transported parent is heterogeneously equal to the original pullback. -/
theorem a7_carrier_parent_spec {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (hC : t1AmbientC t.C = C) (hH : t1AmbientH t.K = H) :
    HEq (t1PullbackMap t) (a7CarrierParent C H t hC hH) := by
  subst hC
  subst hH
  unfold a7CarrierParent
  exact HEq.rfl

/-- At mixed order `D`, the output fourth moment is the squared energy of the
transported parent on the named carrier. -/
theorem a7_carrier_parent_fourth {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (hC : t1AmbientC t.C = C) (hH : t1AmbientH t.K = H)
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t = D) :
    a7MixedOutputFourth t T f =
      (typedW6OutputEnergy C H (a7CarrierParent C H t hC hH)
        (filteredCarrierFunction C H T f)) ^ 2 := by
  have hsq := a7_saturated_output_eq_energy_sq t T f hsupport horder
  have hE := a7_output_energy_carrier_cast (t1AmbientC t.C) C
    (t1AmbientH t.K) H hC hH (t1PullbackMap t)
    (a7CarrierParent C H t hC hH) (a7_carrier_parent_spec C H t hC hH) T f
  rw [hsq]
  exact congrArg (fun x => x ^ 2) hE

/-- Equal transported parents are one ordinary pair and one triple. -/
theorem a7_carrier_parent_unique {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    {A A' : Submodule F (V d)} {B B' : Submodule F (W n)}
    (t : T1IndexTriple A B) (s : T1IndexTriple A' B')
    (hCt : t1AmbientC t.C = C) (hHt : t1AmbientH t.K = H)
    (hCs : t1AmbientC s.C = C) (hHs : t1AmbientH s.K = H)
    (hφ : a7CarrierParent C H t hCt hHt = a7CarrierParent C H s hCs hHs) :
    A = A' ∧ B = B' ∧ HEq t s := by
  have ht := a7_carrier_parent_spec C H t hCt hHt
  have hs := a7_carrier_parent_spec C H s hCs hHs
  have hpull : HEq (t1PullbackMap t) (t1PullbackMap s) :=
    ht.trans ((heq_of_eq hφ).trans hs.symm)
  exact a7_global_parent_unique t s (hCt.trans hCs.symm) (hHt.trans hHs.symm) hpull

/-- Saturated output fourth moments from every ordinary pair, at one base and
one ambient carrier, inject into that carrier's parent-energy pool. Orders
below `D` are not included. -/
theorem a7_saturated_carrier_all_pairs_output_sum_le {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if a6Order t = D ∧ t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
          a7MixedOutputFourth t T f
        else 0) ≤
      ∑ Z : H →ₗ[F] (V d ⧸ C),
        (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)) ^ 2 := by
  classical
  let S := Σ p : dr6ActualNonzeroABPairs (n := n) (d := d),
    T1IndexTriple p.1.1 p.1.2
  let pred : S → Prop := fun u =>
    a6Order u.2 = D ∧ t1AmbientC u.2.C = C ∧ t1AmbientH u.2.K = H
  let ts : Finset S := Finset.univ.filter pred
  have hcond : ∀ w : {u : S // u ∈ ts}, pred w.1 :=
    fun w => (Finset.mem_filter.mp w.2).2
  let φ : {u : S // u ∈ ts} → (H →ₗ[F] (V d ⧸ C)) :=
    fun w => a7CarrierParent C H w.1.2 (hcond w).2.1 (hcond w).2.2
  let genergy : (H →ₗ[F] (V d ⧸ C)) → ℝ := fun Z =>
    (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)) ^ 2
  have hinj : Function.Injective φ := by
    intro w1 w2 hφ
    have huniq := a7_carrier_parent_unique C H w1.1.2 w2.1.2
      (hcond w1).2.1 (hcond w1).2.2 (hcond w2).2.1 (hcond w2).2.2 hφ
    apply Subtype.ext
    have hp : w1.1.1 = w2.1.1 := Subtype.ext (Prod.ext huniq.1 huniq.2.1)
    cases w1 with
    | mk u1 hu1 =>
      cases w2 with
      | mk u2 hu2 =>
        cases u1 with
        | mk p1 t1 =>
          cases u2 with
          | mk p2 t2 =>
            subst hp
            have ht : t1 = t2 := eq_of_heq huniq.2.2
            subst ht
            rfl
  have hterm : ∀ w : {u : S // u ∈ ts},
      a7MixedOutputFourth w.1.2 T f = genergy (φ w) := by
    intro w
    exact a7_carrier_parent_fourth C H w.1.2 (hcond w).2.1 (hcond w).2.2
      T f hsupport (hcond w).1
  have hsumφ : (∑ w ∈ ts.attach, a7MixedOutputFourth w.1.2 T f) =
      ∑ w ∈ ts.attach, genergy (φ w) :=
    Finset.sum_congr rfl (fun w _ => hterm w)
  have himage : (∑ Z ∈ ts.attach.image φ, genergy Z) =
      ∑ w ∈ ts.attach, genergy (φ w) :=
    Finset.sum_image (f := genergy) (hinj.injOn (s := (ts.attach : Set _)))
  have hrest : (∑ Z ∈ ts.attach.image φ, genergy Z) ≤ ∑ Z, genergy Z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun Z _ _ => sq_nonneg
        (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)))
  have hfilter : (∑ u ∈ ts, a7MixedOutputFourth u.2 T f) =
      ∑ u : S, if pred u then a7MixedOutputFourth u.2 T f else 0 :=
    Finset.sum_filter (s := (Finset.univ : Finset S))
      (f := fun u => a7MixedOutputFourth u.2 T f) pred
  have hsig :
      ((Finset.univ : Finset (dr6ActualNonzeroABPairs (n := n) (d := d))).sigma
        (fun _ => Finset.univ)) = (Finset.univ : Finset S) := by
    ext u
    simp
  have hsigma :
      (∑ u : S, if pred u then a7MixedOutputFourth u.2 T f else 0) =
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if pred ⟨p, t⟩ then a7MixedOutputFourth t T f else 0 := by
    have hsumσ := Finset.sum_sigma
      (s := (Finset.univ : Finset (dr6ActualNonzeroABPairs (n := n) (d := d))))
      (t := fun _ => (Finset.univ : Finset (T1IndexTriple _ _)))
      (f := fun u : S => if pred u then a7MixedOutputFourth u.2 T f else 0)
    rw [hsig] at hsumσ
    exact hsumσ
  have hattach : (∑ u ∈ ts, a7MixedOutputFourth u.2 T f) =
      ∑ w ∈ ts.attach, a7MixedOutputFourth w.1.2 T f :=
    (Finset.sum_attach (s := ts) (f := fun u => a7MixedOutputFourth u.2 T f)).symm
  calc
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if a6Order t = D ∧ t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
            a7MixedOutputFourth t T f else 0)
        = ∑ w ∈ ts.attach, a7MixedOutputFourth w.1.2 T f := by
          have hpred : ∀ p t, pred ⟨p, t⟩ =
              (a6Order t = D ∧ t1AmbientC t.C = C ∧ t1AmbientH t.K = H) := by
            intro p t
            rfl
          rw [← hsigma, ← hfilter, hattach]
    _ = ∑ w ∈ ts.attach, genergy (φ w) := hsumφ
    _ = ∑ Z ∈ ts.attach.image φ, genergy Z := himage.symm
    _ ≤ ∑ Z, genergy Z := hrest

/-- Saturated fourth moments from every ordinary pair, on one ambient carrier,
sum to at most the W6 pool factor times that carrier's pair share. -/
theorem a7_saturated_carrier_all_pairs_fourth_sum_le {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if a6Order t = D ∧ t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
          a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare C H f := by
  classical
  let card : ℝ := Fintype.card (V d →ₗ[F] W n)
  let cond : (p : dr6ActualNonzeroABPairs (n := n) (d := d)) →
      T1IndexTriple p.1.1 p.1.2 → Prop :=
    fun _ t => a6Order t = D ∧ t1AmbientC t.C = C ∧ t1AmbientH t.K = H
  have hT : ∀ T : V d →ₗ[F] W n,
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if cond p t then a7MixedOutputFourth t T f else 0) ≤
        (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f := by
    intro T
    exact le_trans
      (a7_saturated_carrier_all_pairs_output_sum_le C H T f hsupport)
      (a7_carrier_energy_sq_sum_le C H T f hsupport)
  have hif : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2),
      (if cond p t then
        (∑ T : V d →ₗ[F] W n, a7MixedOutputFourth t T f) / card else 0) =
        (∑ T : V d →ₗ[F] W n,
          if cond p t then a7MixedOutputFourth t T f else 0) / card := by
    intro p t
    by_cases hc : cond p t
    · simp [hc]
    · simp [hc]
  calc
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if cond p t then a6DerivativeFourth p.1.1 p.1.2 t f else 0)
        = ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              if cond p t then
                (∑ T : V d →ₗ[F] W n, a7MixedOutputFourth t T f) / card
              else 0 := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro t _
          by_cases hc : cond p t
          · rw [if_pos hc, if_pos hc, a7_mixed_fourth_output]
            rfl
          · rw [if_neg hc, if_neg hc]
    _ = ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          (∑ t : T1IndexTriple p.1.1 p.1.2,
            ∑ T : V d →ₗ[F] W n,
              if cond p t then a7MixedOutputFourth t T f else 0) / card := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.sum_congr rfl (fun t _ => hif p t), Finset.sum_div]
    _ = (∑ T : V d →ₗ[F] W n,
          ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              if cond p t then a7MixedOutputFourth t T f else 0) / card := by
          have hinner : ∀ p : dr6ActualNonzeroABPairs (n := n) (d := d),
              (∑ t : T1IndexTriple p.1.1 p.1.2,
                ∑ T : V d →ₗ[F] W n,
                  if cond p t then a7MixedOutputFourth t T f else 0) =
                ∑ T : V d →ₗ[F] W n,
                  ∑ t : T1IndexTriple p.1.1 p.1.2,
                    if cond p t then a7MixedOutputFourth t T f else 0 :=
            fun p => Finset.sum_comm
          have houter :
              (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
                ∑ t : T1IndexTriple p.1.1 p.1.2,
                  ∑ T : V d →ₗ[F] W n,
                    if cond p t then a7MixedOutputFourth t T f else 0) =
                ∑ T : V d →ₗ[F] W n,
                  ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
                    ∑ t : T1IndexTriple p.1.1 p.1.2,
                      if cond p t then a7MixedOutputFourth t T f else 0 := by
            rw [Finset.sum_congr rfl (fun p _ => hinner p)]
            exact Finset.sum_comm
          calc
            (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
                (∑ t : T1IndexTriple p.1.1 p.1.2,
                  ∑ T : V d →ₗ[F] W n,
                    if cond p t then a7MixedOutputFourth t T f else 0) / card) =
                (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
                  ∑ t : T1IndexTriple p.1.1 p.1.2,
                    ∑ T : V d →ₗ[F] W n,
                      if cond p t then a7MixedOutputFourth t T f else 0) / card := by
                  rw [← Finset.sum_div]
            _ = (∑ T : V d →ₗ[F] W n,
                  ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
                    ∑ t : T1IndexTriple p.1.1 p.1.2,
                      if cond p t then a7MixedOutputFourth t T f else 0) / card :=
                congrArg (fun s => s / card) houter
    _ ≤ (∑ T : V d →ₗ[F] W n,
          (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f) / card := by
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
          refine Finset.sum_le_sum ?_
          intro T _
          exact hT T
    _ = (2 : ℝ) ^ (6 * D * D + 1) *
          ((∑ T : V d →ₗ[F] W n, typedW6QComponent C H T f) / card) := by
          rw [← Finset.mul_sum, mul_div_assoc]
    _ = (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare C H f := by
          rw [a7PairShare, typedUniformMean]

/-- Order-`D` fourth moments from every ordinary pair sum to at most the W6
pool factor times unweighted `Q`. Each carrier is charged once. Orders below
`D` are not in this sum. -/
theorem a7_saturated_all_pairs_fourth_sum_le {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if a6Order t = D then a6DerivativeFourth p.1.1 p.1.2 t f else 0) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * a7HybridQ f := by
  classical
  let Qpair := Submodule F (V d) × Submodule F (W n)
  have hcarrier : ∀ q : Qpair,
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
            a6DerivativeFourth p.1.1 p.1.2 t f else 0) ≤
        (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare q.1 q.2 f :=
    fun q => a7_saturated_carrier_all_pairs_fourth_sum_le q.1 q.2 f hsupport
  have hsumq :
      (∑ q : Qpair,
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
              a6DerivativeFourth p.1.1 p.1.2 t f else 0) ≤
        (2 : ℝ) ^ (6 * D * D + 1) *
          ∑ q : Qpair, a7PairShare q.1 q.2 f := by
    calc
      _ ≤ ∑ q : Qpair, (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare q.1 q.2 f :=
        Finset.sum_le_sum (fun q _ => hcarrier q)
      _ = (2 : ℝ) ^ (6 * D * D + 1) * ∑ q : Qpair, a7PairShare q.1 q.2 f := by
        rw [← Finset.mul_sum]
  have hsingle : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2),
      (∑ q : Qpair,
        if a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
          a6DerivativeFourth p.1.1 p.1.2 t f else 0) =
        if a6Order t = D then a6DerivativeFourth p.1.1 p.1.2 t f else 0 := by
    intro p t
    let q0 : Qpair := ⟨t1AmbientC t.C, t1AmbientH t.K⟩
    have hrest : ∀ q ∈ Finset.univ, q ≠ q0 →
        (if a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
          a6DerivativeFourth p.1.1 p.1.2 t f else 0) = 0 := by
      intro q _ hne
      have hneg :
          ¬ (a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2) := by
        intro h
        exact hne (Prod.ext h.2.1.symm h.2.2.symm)
      simp [hneg]
    have hsum := Finset.sum_eq_single (s := Finset.univ) q0
      (f := fun q : Qpair =>
        if a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
          a6DerivativeFourth p.1.1 p.1.2 t f else 0)
      hrest (fun h => absurd (Finset.mem_univ q0) h)
    have hq0 :
        (if a6Order t = D ∧ t1AmbientC t.C = q0.1 ∧ t1AmbientH t.K = q0.2 then
          a6DerivativeFourth p.1.1 p.1.2 t f else 0) =
          if a6Order t = D then a6DerivativeFourth p.1.1 p.1.2 t f else 0 := by
      simp [q0]
    rw [hsum, hq0]
  have hgroup :
      (∑ q : Qpair,
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if a6Order t = D ∧ t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
              a6DerivativeFourth p.1.1 p.1.2 t f else 0) =
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if a6Order t = D then a6DerivativeFourth p.1.1 p.1.2 t f else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro t _
    exact hsingle p t
  have hexh := a7_pair_shares_exhaust f
  have hscaled := hsumq
  rw [hgroup] at hscaled
  rw [hexh] at hscaled
  exact hscaled

/-- The order-`D` part of the mixed sum is at most the terminal allowance
times unweighted `Q`. Orders strictly below `D` are not estimated here, so
this does not discharge `hS` when `D > 1`. -/
theorem a7_saturated_weighted_all_pairs_le {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hD : 0 < D) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if a6Order t = D then
          (2 : ℝ) ^ (24 * D * D) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) * a7HybridQ f := by
  classical
  have hsum := a7_saturated_all_pairs_fourth_sum_le f hsupport
  have hmul := mul_le_mul_of_nonneg_left hsum
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (24 * D * D))
  have hpull :
      (2 : ℝ) ^ (24 * D * D) *
        (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if a6Order t = D then a6DerivativeFourth p.1.1 p.1.2 t f else 0) =
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if a6Order t = D then
              (2 : ℝ) ^ (24 * D * D) * a6DerivativeFourth p.1.1 p.1.2 t f
            else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases hord : a6Order t = D
    · simp [hord]
    · simp [hord]
  rw [hpull] at hmul
  rw [← mul_assoc] at hmul
  have hfac := mul_le_mul_of_nonneg_right
    (a7_saturated_pool_exponent_fits D hD) (a7HybridQ_nonneg f)
  exact le_trans hmul hfac

/-- At degree one every positive mixed order is the saturated order or has
fourth moment zero. The share hypothesis is not used. -/
theorem a7_mixed_sum_degree_one {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 1 f) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : ℝ) ^ (24 * 1 * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      (2 : ℝ) ^ (100 * 1 * 1) * (2 : ℝ) ^ ((1 : ℤ) - 31 * 1) * a7HybridQ f := by
  classical
  have hsat := a7_saturated_weighted_all_pairs_le (D := 1) f hsupport Nat.one_pos
  have hterm : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2),
      (if 0 < a6Order t then
        (2 : ℝ) ^ (24 * 1 * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
      else 0) =
        if a6Order t = 1 then
          (2 : ℝ) ^ (24 * 1 * 1) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0 := by
    intro p t
    by_cases h1 : a6Order t = 1
    · simp [h1]
    · by_cases hpos : 0 < a6Order t
      · have hgt : 1 < a6Order t := by omega
        have hzero := a7_derivative_fourth_zero_of_high t f hsupport hgt
        simp [h1, hpos, hzero]
      · simp [h1, hpos]
  have heq :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t then
            (2 : ℝ) ^ (24 * 1 * a6Order t) *
              a6DerivativeFourth p.1.1 p.1.2 t f else 0) =
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if a6Order t = 1 then
              (2 : ℝ) ^ (24 * 1 * 1) * a6DerivativeFourth p.1.1 p.1.2 t f
            else 0 := by
    refine Finset.sum_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro t _
    exact hterm p t
  rw [heq]
  exact hsat

/-- Degree-one fourth moment bound. This is not manuscript A7 for a general
cutoff: orders strictly below a larger `D` are still open. -/
theorem a7_degree_one_fourth_bound {n d : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough 1 f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) ≤
      (2 : ℝ) ^ (100 * 1 * 1) * a7HybridQ f :=
  a7_positive_of_mixed_bound f hsupport Nat.one_pos
    (a7_mixed_sum_degree_one f hsupport)

/-- Rank support through `r` remains support through every larger cutoff. -/
theorem a7_support_mono {n d r D : Nat} (f : BinaryMatrix n d → Complex)
    (hr : r ≤ D) (hf : ComplexFourierSupportedThrough r f) :
    ComplexFourierSupportedThrough D f := by
  intro Y hY
  exact hf Y (lt_of_le_of_lt hr hY)

/-- The mixed derivative, read on the binary coordinates of its output carrier. -/
def a7OutputBinary {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :=
  let parent := a7MixedCoordinateParent t
  let coord := a7MixedCoordinate t T f
  let Cout := LinearMap.range parent.transpose.toLin'
  let Hout := LinearMap.ker parent.transpose.toLin'
  fun X =>
    actualW6Derivative parent 0 coord ((carrierMatrixEquiv Cout Hout).symm X)

/-- One base of a mixed fourth moment is the fourth moment of the output
binary function, and that function is supported through `D` minus the order. -/
theorem a7_output_binary_fourth {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) :
    a7MixedOutputFourth t T f =
        uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M) ^ 2) ∧
      ComplexFourierSupportedThrough (D - a6Order t) (a7OutputBinary t T f) := by
  classical
  let parent := a7MixedCoordinateParent t
  let coord := a7MixedCoordinate t T f
  let Cout := LinearMap.range parent.transpose.toLin'
  let Hout := LinearMap.ker parent.transpose.toLin'
  let deriv := actualW6Derivative parent 0 coord
  have hL4 := carrierMean_coordinate Cout Hout
    (fun M => Complex.normSq (deriv M) ^ 2)
  have hfour : a7MixedOutputFourth t T f =
      uniformMean (fun M =>
        Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M)) ^ 2) := by
    rw [a7_mixed_output_fourth_coordinate]
    change carrierMean Cout Hout (fun M => Complex.normSq (deriv M) ^ 2) =
      uniformMean (fun M =>
        Complex.normSq (deriv ((carrierMatrixEquiv Cout Hout).symm M)) ^ 2)
    exact hL4
  have hg : a7OutputBinary t T f =
      fun M => deriv ((carrierMatrixEquiv Cout Hout).symm M) := by
    unfold a7OutputBinary
    rfl
  have hsup :=
    (carrierFourier_support_iff_coordinate Cout Hout (D - a6Order t) deriv).mp
      (a7_mixed_output_coordinate_support t T f hsupport horder)
  refine ⟨?_, ?_⟩
  · rw [hfour, hg]
  · rw [hg]
    exact hsup

/-- If the remaining degree is at most one, the output fourth moment is at
most `2^{100}` times the output carrier's own unweighted `Q`. That output `Q`
is not a summand of the original `Q`. -/
theorem a7_low_output_fourth_le_output_q {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) (hdeg : D - a6Order t ≤ 1) :
    a7MixedOutputFourth t T f ≤
      (2 : ℝ) ^ (100 * 1 * 1) * a7HybridQ (a7OutputBinary t T f) := by
  obtain ⟨heq, hsup⟩ := a7_output_binary_fourth t T f hsupport horder
  rw [heq]
  exact a7_degree_one_fourth_bound (a7OutputBinary t T f)
    (a7_support_mono (a7OutputBinary t T f) hdeg hsup)

/-- The positive mixed sum is the order-`D` sum plus the strict lower-order
sum. Orders above `D` contribute zero. -/
theorem a7_mixed_sum_order_split {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hD : 0 < D) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) =
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if a6Order t = D then
            (2 : ℝ) ^ (24 * D * D) * a6DerivativeFourth p.1.1 p.1.2 t f
          else 0) +
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t ∧ a6Order t < D then
            (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
          else 0) := by
  classical
  have hterm : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2),
      (if 0 < a6Order t then
        (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
      else 0) =
        (if a6Order t = D then
          (2 : ℝ) ^ (24 * D * D) * a6DerivativeFourth p.1.1 p.1.2 t f else 0) +
        (if 0 < a6Order t ∧ a6Order t < D then
          (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) := by
    intro p t
    by_cases hEq : a6Order t = D
    · rw [hEq]
      have hlt : ¬ (0 < D ∧ D < D) := by
        intro h
        exact Nat.lt_irrefl D h.2
      rw [if_pos hD, if_pos rfl, if_neg hlt]
      exact (add_zero _).symm
    · by_cases hpos : 0 < a6Order t
      · by_cases hlt : a6Order t < D
        · simp [hEq, hpos, hlt]
        · have hgt : D < a6Order t := by omega
          have hzero := a7_derivative_fourth_zero_of_high t f hsupport hgt
          simp [hEq, hpos, hlt, hzero]
      · simp [hEq, hpos]
  have hsum :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t then
            (2 : ℝ) ^ (24 * D * a6Order t) *
              a6DerivativeFourth p.1.1 p.1.2 t f else 0) =
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            ((if a6Order t = D then
              (2 : ℝ) ^ (24 * D * D) * a6DerivativeFourth p.1.1 p.1.2 t f else 0) +
            (if 0 < a6Order t ∧ a6Order t < D then
              (2 : ℝ) ^ (24 * D * a6Order t) *
                a6DerivativeFourth p.1.1 p.1.2 t f else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro t _
    exact hterm p t
  rw [hsum]
  simp_rw [Finset.sum_add_distrib]

/-- The mixed sum is at most the terminal allowance times `Q`, plus the
strict lower-order sum. The lower-order sum is not bounded here: its output
degree is still positive, and its fourth moment is not a squared parent
energy. -/
theorem a7_mixed_sum_le_allowance_add_lower {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hD : 0 < D) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if 0 < a6Order t then
          (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
        else 0) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) * a7HybridQ f +
        (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if 0 < a6Order t ∧ a6Order t < D then
              (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
            else 0) := by
  have hsplit := a7_mixed_sum_order_split f hsupport hD
  have hsat := a7_saturated_weighted_all_pairs_le f hsupport hD
  rw [hsplit]
  exact add_le_add hsat (le_refl _)

/-- The squared `L2` energy of the output binary function is the squared W6
energy of this triple's pullback. This is the zero-order summand of the
output `Q`, for every mixed order. -/
theorem a7_output_binary_l2_sq {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2 =
      (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
        (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2 := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let parent := a7MixedCoordinateParent t
  let coord := a7MixedCoordinate t T f
  let Cout := LinearMap.range parent.transpose.toLin'
  let Hout := LinearMap.ker parent.transpose.toLin'
  let deriv := actualW6Derivative parent 0 coord
  have hE := typedW6OutputEnergy_coordinate C H X
    (filteredCarrierFunction C H T f)
  have henergy : typedW6OutputEnergy C H X (filteredCarrierFunction C H T f) =
      carrierMean Cout Hout (fun M => Complex.normSq (deriv M)) := by
    rw [hE]
    rfl
  have hL2 := carrierComplexEnergy_coordinate Cout Hout deriv
  have hg : a7OutputBinary t T f =
      fun M => deriv ((carrierMatrixEquiv Cout Hout).symm M) := by
    unfold a7OutputBinary
    rfl
  have hmean : uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M)) =
      typedW6OutputEnergy C H X (filteredCarrierFunction C H T f) := by
    rw [hg, ← hL2, ← henergy]
  exact congrArg (fun x => x ^ 2) hmean

/-- The zero-order summand of the output `Q` is that squared `L2` energy. -/
theorem a7_output_zero_share_eq_l2 {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex) :
    a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
        (a7OutputBinary t T f) =
      (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2 := by
  rw [a7PairShare]
  exact a7_zero_order_uniform (a7OutputBinary t T f)

/-- Squared pullback energies of every triple on one ambient carrier, from
every ordinary pair, inject into that carrier's parent-energy pool. The
order is unrestricted: this bounds squared `L2` energies, not fourth moments. -/
theorem a7_ambient_energy_sq_sum_le {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
      ∑ t : T1IndexTriple p.1.1 p.1.2,
        if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
          (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
            (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2
        else 0) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f := by
  classical
  let S := Σ p : dr6ActualNonzeroABPairs (n := n) (d := d),
    T1IndexTriple p.1.1 p.1.2
  let pred : S → Prop := fun u =>
    t1AmbientC u.2.C = C ∧ t1AmbientH u.2.K = H
  let ts : Finset S := Finset.univ.filter pred
  have hcond : ∀ w : {u : S // u ∈ ts}, pred w.1 :=
    fun w => (Finset.mem_filter.mp w.2).2
  let φ : {u : S // u ∈ ts} → (H →ₗ[F] (V d ⧸ C)) :=
    fun w => a7CarrierParent C H w.1.2 (hcond w).1 (hcond w).2
  let genergy : (H →ₗ[F] (V d ⧸ C)) → ℝ := fun Z =>
    (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)) ^ 2
  have hinj : Function.Injective φ := by
    intro w1 w2 hφ
    have huniq := a7_carrier_parent_unique C H w1.1.2 w2.1.2
      (hcond w1).1 (hcond w1).2 (hcond w2).1 (hcond w2).2 hφ
    apply Subtype.ext
    have hp : w1.1.1 = w2.1.1 := Subtype.ext (Prod.ext huniq.1 huniq.2.1)
    cases w1 with
    | mk u1 hu1 =>
      cases w2 with
      | mk u2 hu2 =>
        cases u1 with
        | mk p1 t1 =>
          cases u2 with
          | mk p2 t2 =>
            subst hp
            have ht : t1 = t2 := eq_of_heq huniq.2.2
            subst ht
            rfl
  have hterm : ∀ w : {u : S // u ∈ ts},
      (typedW6OutputEnergy (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K)
        (t1PullbackMap w.1.2)
        (filteredCarrierFunction (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K) T f)) ^ 2 =
        genergy (φ w) := by
    intro w
    exact congrArg (fun x => x ^ 2)
      (a7_output_energy_carrier_cast (t1AmbientC w.1.2.C) C
        (t1AmbientH w.1.2.K) H (hcond w).1 (hcond w).2 (t1PullbackMap w.1.2)
        (a7CarrierParent C H w.1.2 (hcond w).1 (hcond w).2)
        (a7_carrier_parent_spec C H w.1.2 (hcond w).1 (hcond w).2) T f)
  have hsumφ :
      (∑ w ∈ ts.attach,
        (typedW6OutputEnergy (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K)
          (t1PullbackMap w.1.2)
          (filteredCarrierFunction (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K) T f)) ^ 2) =
        ∑ w ∈ ts.attach, genergy (φ w) :=
    Finset.sum_congr rfl (fun w _ => hterm w)
  have himage : (∑ Z ∈ ts.attach.image φ, genergy Z) =
      ∑ w ∈ ts.attach, genergy (φ w) :=
    Finset.sum_image (f := genergy) (hinj.injOn (s := (ts.attach : Set _)))
  have hrest : (∑ Z ∈ ts.attach.image φ, genergy Z) ≤ ∑ Z, genergy Z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun Z _ _ => sq_nonneg
        (typedW6OutputEnergy C H Z (filteredCarrierFunction C H T f)))
  have hfilter :
      (∑ u ∈ ts,
        (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
          (t1PullbackMap u.2)
          (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2) =
        ∑ u : S, if pred u then
          (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
            (t1PullbackMap u.2)
            (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2
        else 0 :=
    Finset.sum_filter (s := (Finset.univ : Finset S))
      (f := fun u =>
        (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
          (t1PullbackMap u.2)
          (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2)
      pred
  have hsig :
      ((Finset.univ : Finset (dr6ActualNonzeroABPairs (n := n) (d := d))).sigma
        (fun _ => Finset.univ)) = (Finset.univ : Finset S) := by
    ext u
    simp
  have hsigma :
      (∑ u : S, if pred u then
        (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
          (t1PullbackMap u.2)
          (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2
      else 0) =
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if pred ⟨p, t⟩ then
              (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
                (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2
            else 0 := by
    have hsumσ := Finset.sum_sigma
      (s := (Finset.univ : Finset (dr6ActualNonzeroABPairs (n := n) (d := d))))
      (t := fun _ => (Finset.univ : Finset (T1IndexTriple _ _)))
      (f := fun u : S => if pred u then
        (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
          (t1PullbackMap u.2)
          (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2
      else 0)
    rw [hsig] at hsumσ
    exact hsumσ
  have hattach :
      (∑ u ∈ ts,
        (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
          (t1PullbackMap u.2)
          (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2) =
        ∑ w ∈ ts.attach,
          (typedW6OutputEnergy (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K)
            (t1PullbackMap w.1.2)
            (filteredCarrierFunction (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K) T f)) ^ 2 :=
    (Finset.sum_attach (s := ts)
      (f := fun u =>
        (typedW6OutputEnergy (t1AmbientC u.2.C) (t1AmbientH u.2.K)
          (t1PullbackMap u.2)
          (filteredCarrierFunction (t1AmbientC u.2.C) (t1AmbientH u.2.K) T f)) ^ 2)).symm
  have hsum :
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
            (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
              (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2
          else 0) ≤
        ∑ Z : H →ₗ[F] (V d ⧸ C), genergy Z := by
    calc
      _ = ∑ w ∈ ts.attach,
            (typedW6OutputEnergy (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K)
              (t1PullbackMap w.1.2)
              (filteredCarrierFunction (t1AmbientC w.1.2.C) (t1AmbientH w.1.2.K) T f)) ^ 2 := by
          have hpred : ∀ p (t : T1IndexTriple p.1.1 p.1.2), pred ⟨p, t⟩ =
              (t1AmbientC t.C = C ∧ t1AmbientH t.K = H) := by
            intro p t
            rfl
          rw [← hsigma, ← hfilter, hattach]
      _ = ∑ w ∈ ts.attach, genergy (φ w) := hsumφ
      _ = ∑ Z ∈ ts.attach.image φ, genergy Z := himage.symm
      _ ≤ ∑ Z, genergy Z := hrest
  exact le_trans hsum (a7_carrier_energy_sq_sum_le C H T f hsupport)

/-- Averaging the injected energies puts every output zero-order summand on
one carrier under the W6 pool factor times that carrier's original share. -/
theorem a7_output_zero_summand_carrier_le {n d D : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
            (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
          else 0) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare C H f := by
  classical
  have hT : ∀ T : V d →ₗ[F] W n,
      (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
            (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
          else 0) ≤
        (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f := by
    intro T
    have hsum := a7_ambient_energy_sq_sum_le C H T f hsupport
    have hrewrite :
        (∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
              (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
            else 0) =
          ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
                (typedW6OutputEnergy (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
                  (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)) ^ 2
              else 0 := by
      refine Finset.sum_congr rfl ?_
      intro p _
      refine Finset.sum_congr rfl ?_
      intro t _
      by_cases hc : t1AmbientC t.C = C ∧ t1AmbientH t.K = H
      · rw [if_pos hc, if_pos hc, a7_output_binary_l2_sq]
      · rw [if_neg hc, if_neg hc]
    rw [hrewrite]
    exact hsum
  have hcard : 0 < (Fintype.card (V d →ₗ[F] W n) : ℝ) := by
    have hpos : 0 < Fintype.card (V d →ₗ[F] W n) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast hpos
  unfold typedUniformMean a7PairShare
  have hsumle :
      (∑ T : V d →ₗ[F] W n,
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if t1AmbientC t.C = C ∧ t1AmbientH t.K = H then
              (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
            else 0) ≤
        ∑ T : V d →ₗ[F] W n,
          (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f :=
    Finset.sum_le_sum (fun T _ => hT T)
  calc
    _ ≤ (∑ T : V d →ₗ[F] W n,
          (2 : ℝ) ^ (6 * D * D + 1) * typedW6QComponent C H T f) /
        (Fintype.card (V d →ₗ[F] W n) : ℝ) :=
      div_le_div_of_nonneg_right hsumle (le_of_lt hcard)
    _ = (2 : ℝ) ^ (6 * D * D + 1) *
          ((∑ T : V d →ₗ[F] W n, typedW6QComponent C H T f) /
            (Fintype.card (V d →ₗ[F] W n) : ℝ)) := by
      rw [← Finset.mul_sum, mul_div_assoc]

/-- Summing carriers reindexes every output zero-order summand into the
original unweighted `Q`, with the W6 pool factor and no double charge. The
positive-order summands of an output `Q` are not included, and a
positive-degree fourth moment is not this squared energy. -/
theorem a7_output_zero_summand_le_q {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2) ≤
      (2 : ℝ) ^ (6 * D * D + 1) * a7HybridQ f := by
  classical
  let Qpair := Submodule F (V d) × Submodule F (W n)
  have hcarrier' : ∀ q : Qpair,
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
              (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
            else 0) ≤
        (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare q.1 q.2 f :=
    fun q => a7_output_zero_summand_carrier_le q.1 q.2 f hsupport
  have hsumq :
      (∑ q : Qpair,
        typedUniformMean (fun T : V d →ₗ[F] W n =>
          ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
                (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
              else 0)) ≤
        (2 : ℝ) ^ (6 * D * D + 1) *
          ∑ q : Qpair, a7PairShare q.1 q.2 f := by
    calc
      _ ≤ ∑ q : Qpair, (2 : ℝ) ^ (6 * D * D + 1) * a7PairShare q.1 q.2 f :=
        Finset.sum_le_sum (fun q _ => hcarrier' q)
      _ = (2 : ℝ) ^ (6 * D * D + 1) * ∑ q : Qpair, a7PairShare q.1 q.2 f := by
        rw [← Finset.mul_sum]
  have hexh := a7_pair_shares_exhaust f
  have hsingle : ∀ (p : dr6ActualNonzeroABPairs (n := n) (d := d))
      (t : T1IndexTriple p.1.1 p.1.2) (T : V d →ₗ[F] W n),
      (∑ q : Qpair,
        if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
          (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
        else 0) =
        (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2 := by
    intro p t T
    let q0 : Qpair := ⟨t1AmbientC t.C, t1AmbientH t.K⟩
    let val := (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
    have hrest : ∀ q ∈ Finset.univ, q ≠ q0 →
        (if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then val else 0) = 0 := by
      intro q _ hne
      have hneg : ¬ (t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2) := by
        intro h
        exact hne (Prod.ext h.1.symm h.2.symm)
      simp [hneg]
    have hsum := Finset.sum_eq_single (s := Finset.univ) q0
      (f := fun q : Qpair =>
        if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then val else 0)
      hrest (fun h => absurd (Finset.mem_univ q0) h)
    have hq0 : (if t1AmbientC t.C = q0.1 ∧ t1AmbientH t.K = q0.2 then val else 0) = val := by
      simp [q0]
    rw [hsum, hq0]
  have hgroup :
      (∑ q : Qpair,
        typedUniformMean (fun T : V d →ₗ[F] W n =>
          ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
                (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
              else 0)) =
        typedUniformMean (fun T : V d →ₗ[F] W n =>
          ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
            ∑ t : T1IndexTriple p.1.1 p.1.2,
              (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2) := by
    unfold typedUniformMean
    have hnum :
        (∑ q : Qpair,
          ∑ T : V d →ₗ[F] W n,
            ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
              ∑ t : T1IndexTriple p.1.1 p.1.2,
                if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
                  (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
                else 0) =
          ∑ T : V d →ₗ[F] W n,
            ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
              ∑ t : T1IndexTriple p.1.1 p.1.2,
                (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro T _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro p _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro t _
      exact hsingle p t T
    have hcard : (Fintype.card (V d →ₗ[F] W n) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (V d →ₗ[F] W n) ≠ 0)
    calc
      (∑ q : Qpair,
          (∑ T : V d →ₗ[F] W n,
            ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
              ∑ t : T1IndexTriple p.1.1 p.1.2,
                if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
                  (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
                else 0) /
            (Fintype.card (V d →ₗ[F] W n) : ℝ)) =
          (∑ q : Qpair,
            ∑ T : V d →ₗ[F] W n,
              ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
                ∑ t : T1IndexTriple p.1.1 p.1.2,
                  if t1AmbientC t.C = q.1 ∧ t1AmbientH t.K = q.2 then
                    (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2
                  else 0) /
            (Fintype.card (V d →ₗ[F] W n) : ℝ) := by
        rw [Finset.sum_div]
      _ = (∑ T : V d →ₗ[F] W n,
            ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
              ∑ t : T1IndexTriple p.1.1 p.1.2,
                (uniformMean (fun M => Complex.normSq (a7OutputBinary t T f M))) ^ 2) /
          (Fintype.card (V d →ₗ[F] W n) : ℝ) := by
        rw [hnum]
  rw [hexh] at hsumq
  rw [hgroup] at hsumq
  exact hsumq

/-- Orthogonality on one carrier: a hybrid filter keeps the selected Fourier
coefficients and drops the rest. This is the coefficient form of a positive-order
filter of a carrier function. It does not reindex that filter into the original
unweighted `Q`, and `a7_positive_of_overlapping_shares` still assumes `e`. -/
theorem a7_hybrid_filter_coefficient {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → Complex)
    (Y : B₂ →ₗ[F] (V d ⧸ A₂)) :
    complexCarrierFourierCoeff A₂ B₂
        (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g) Y =
      if Selected A₁₂ B₁₂ Y then complexCarrierFourierCoeff A₂ B₂ g Y else 0 := by
  classical
  set c : (B₂ →ₗ[F] (V d ⧸ A₂)) → Complex :=
    fun Z => complexCarrierFourierCoeff A₂ B₂ g Z
  have hfilter :
      complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g =
        fun M => ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
          if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0 := by
    funext M
    unfold complexCarrierHybridFilter
    rfl
  have hcardPos : 0 < Fintype.card ((V d ⧸ A₂) →ₗ[F] B₂) :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hcardR : (Fintype.card ((V d ⧸ A₂) →ₗ[F] B₂) : ℝ) ≠ 0 := by
    exact_mod_cast hcardPos.ne'
  have hcardC : (Fintype.card ((V d ⧸ A₂) →ₗ[F] B₂) : ℂ) ≠ 0 := by
    exact_mod_cast hcardPos.ne'
  have horth (Z : B₂ →ₗ[F] (V d ⧸ A₂)) :
      (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
        (traceCharacter Z M : ℂ) * (traceCharacter Y M : ℂ)) =
        if Z = Y then (Fintype.card ((V d ⧸ A₂) →ₗ[F] B₂) : ℂ) else 0 := by
    have ho := carrierCharacter_orthogonality A₂ B₂ Z Y
    unfold carrierMean at ho
    have hsumR :
        (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
          traceCharacter Z M * traceCharacter Y M) =
          (if Z = Y then (1 : ℝ) else 0) *
            (Fintype.card ((V d ⧸ A₂) →ₗ[F] B₂) : ℝ) :=
      (div_eq_iff hcardR).mp ho
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hsumR
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] at hcast
    by_cases hZ : Z = Y
    · simpa [hZ] using hcast
    · simpa [hZ] using hcast
  unfold complexCarrierFourierCoeff
  rw [hfilter]
  have hnum :
      (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
        (∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
          if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0) *
          (traceCharacter Y M : ℂ)) =
        (if Selected A₁₂ B₁₂ Y then c Y else 0) *
          (Fintype.card ((V d ⧸ A₂) →ₗ[F] B₂) : ℂ) := by
    have hcomm :
        (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
          (∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
            if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0) *
            (traceCharacter Y M : ℂ)) =
          ∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
            ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
              (if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0) *
                (traceCharacter Y M : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro M _
      exact Finset.sum_mul Finset.univ
        (fun Z => if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0)
        (traceCharacter Y M : ℂ)
    have hswap :
        (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
          ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
            (if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0) *
              (traceCharacter Y M : ℂ)) =
          ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
            ∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
              (if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0) *
                (traceCharacter Y M : ℂ) :=
      Finset.sum_comm
    have hinner :
        (∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
          ∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
            (if Selected A₁₂ B₁₂ Z then c Z * (traceCharacter Z M : ℂ) else 0) *
              (traceCharacter Y M : ℂ)) =
          ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
            if Selected A₁₂ B₁₂ Z then
              c Z * (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
                (traceCharacter Z M : ℂ) * (traceCharacter Y M : ℂ))
            else 0 := by
      refine Finset.sum_congr rfl ?_
      intro Z _
      by_cases hsel : Selected A₁₂ B₁₂ Z
      · simp only [if_pos hsel]
        conv_lhs =>
          arg 2
          ext M
          rw [mul_assoc]
        exact (Finset.mul_sum Finset.univ
          (fun M => (traceCharacter Z M : ℂ) * (traceCharacter Y M : ℂ)) (c Z)).symm
      · simp only [if_neg hsel]
        refine Finset.sum_eq_zero ?_
        intro M _
        exact zero_mul _
    rw [hcomm, hswap, hinner]
    have hsingle := Finset.sum_eq_single (s := Finset.univ) Y
      (f := fun Z : B₂ →ₗ[F] (V d ⧸ A₂) =>
        if Selected A₁₂ B₁₂ Z then
          c Z * (∑ M : (V d ⧸ A₂) →ₗ[F] B₂,
            (traceCharacter Z M : ℂ) * (traceCharacter Y M : ℂ))
        else 0)
      (fun Z _ hne => by
        by_cases hsel : Selected A₁₂ B₁₂ Z
        · rw [if_pos hsel, horth Z, if_neg hne]
          exact mul_zero _
        · rw [if_neg hsel])
      (fun hmiss => absurd (Finset.mem_univ Y) hmiss)
    rw [hsingle]
    by_cases hsel : Selected A₁₂ B₁₂ Y
    · rw [if_pos hsel, if_pos hsel, horth Y, if_pos rfl]
    · rw [if_neg hsel, if_neg hsel]
      exact (zero_mul _).symm
  rw [hnum]
  by_cases hsel : Selected A₁₂ B₁₂ Y
  · rw [if_pos hsel, if_pos hsel]
    exact mul_div_cancel_right₀ _ hcardC
  · rw [if_neg hsel, if_neg hsel]
    simp

/-- The `L2` energy of one carrier hybrid filter is the sum of the selected
squared coefficients. Squaring this sum is not an injection into original `Q`. -/
theorem a7_hybrid_filter_energy {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → Complex) :
    carrierMean A₂ B₂ (fun M =>
      Complex.normSq (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g M)) =
      ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
        if Selected A₁₂ B₁₂ Z then
          Complex.normSq (complexCarrierFourierCoeff A₂ B₂ g Z) else 0 := by
  classical
  rw [PvNP.RealizableHardness.ActualBinaryMatrixHC46A7CarrierParseval.complex_carrier_parseval
    A₂ B₂ (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g)]
  refine Finset.sum_congr rfl ?_
  intro Z _
  rw [a7_hybrid_filter_coefficient]
  by_cases hsel : Selected A₁₂ B₁₂ Z
  · rw [if_pos hsel, if_pos hsel]
  · rw [if_neg hsel, if_neg hsel]
    simp [Complex.normSq_zero]

/-- A carrier hybrid filter drops frequencies, so its `L2` energy is at most
the carrier energy of the unfiltered function. -/
theorem a7_hybrid_filter_energy_le_total {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂)) (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → Complex) :
    carrierMean A₂ B₂ (fun M =>
      Complex.normSq (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g M)) ≤
      carrierMean A₂ B₂ (fun M => Complex.normSq (g M)) := by
  classical
  rw [a7_hybrid_filter_energy]
  rw [PvNP.RealizableHardness.ActualBinaryMatrixHC46A7CarrierParseval.complex_carrier_parseval
    A₂ B₂ g]
  refine Finset.sum_le_sum ?_
  intro Z _
  by_cases hsel : Selected A₁₂ B₁₂ Z
  · rw [if_pos hsel]
  · rw [if_neg hsel]
    exact Complex.normSq_nonneg _

/-- One hybrid filter of a mixed derivative has squared `L2` energy at most
the same `2^{4k(D-order)}` multiple of that triple's original pair component
as the full derivative. This is one filter, not the sum of an output `Q`, and
it does not remove the share hypothesis. -/
theorem a7_one_hybrid_filter_sq_le_component {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D)
    (filterEnergy : ℝ)
    (hnn : 0 ≤ filterEnergy)
    (hle : filterEnergy ≤
      carrierMean
        (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
        (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (a7MixedCoordinateParent t) 0
            (a7MixedCoordinate t T f) M))) :
    filterEnergy ^ 2 ≤
      (2 : ℝ) ^ (4 * Module.finrank F (LinearMap.range (t1PullbackMap t)) *
        (D - a6Order t)) *
        typedW6QComponent (t1AmbientC t.C) (t1AmbientH t.K) T f := by
  have hfull := a7_output_energy_sq_le_component t T f hsupport horder
  have hfullNn : 0 ≤
      carrierMean
        (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
        (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (a7MixedCoordinateParent t) 0
            (a7MixedCoordinate t T f) M)) := by
    refine le_trans ?_ hle
    exact hnn
  have hsq : filterEnergy ^ 2 ≤
      (carrierMean
        (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
        (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
        (fun M => Complex.normSq
          (actualW6Derivative (a7MixedCoordinateParent t) 0
            (a7MixedCoordinate t T f) M))) ^ 2 := by
    have habs : |filterEnergy| ≤
        |carrierMean
          (LinearMap.range (a7MixedCoordinateParent t).transpose.toLin')
          (LinearMap.ker (a7MixedCoordinateParent t).transpose.toLin')
          (fun M => Complex.normSq
            (actualW6Derivative (a7MixedCoordinateParent t) 0
              (a7MixedCoordinate t T f) M))| := by
      rw [abs_of_nonneg hnn, abs_of_nonneg hfullNn]
      exact hle
    exact sq_le_sq.mpr habs
  exact le_trans hsq hfull

lemma a7_w6Gaussian_zero (n : Nat) : w6Gaussian n 0 = 1 := by
  unfold w6Gaussian w6FrameProduct
  simp

lemma a7_w6Gaussian_self (n : Nat) : w6Gaussian n n = 1 := by
  have hpos : 0 < w6FrameProduct n n := by
    unfold w6FrameProduct
    refine Finset.prod_pos ?_
    intro i _
    exact Nat.sub_pos_of_lt
      (Nat.pow_lt_pow_right (by decide : 1 < 2) i.isLt)
  unfold w6Gaussian
  rw [if_pos le_rfl, Nat.div_self hpos]

/-- One Gaussian factor times one graph power. The factor four appears only
when the chosen subspace is a proper positive-dimensional subspace. -/
lemma a7_gauss_graph_le (n m r : Nat) (hm : m ≤ n) :
    w6Gaussian n m * 2 ^ (r * (n - m)) ≤
      (if 0 < m ∧ m < n then 4 else 1) * 2 ^ ((m + r) * (n - m)) := by
  by_cases h0 : m = 0
  · subst m
    rw [a7_w6Gaussian_zero, if_neg (by
      intro h
      exact Nat.not_lt_zero 0 h.1)]
    simp
  · by_cases hfull : m = n
    · subst m
      rw [a7_w6Gaussian_self, if_neg (by
        intro h
        exact (lt_irrefl n) h.2)]
      simp
    · have hmid : 0 < m ∧ m < n := by
        constructor
        · omega
        · omega
      rw [if_pos hmid]
      have hg := w6_gaussian_le_four_pow hm
      have hsplit : m * (n - m) + r * (n - m) = (m + r) * (n - m) := by ring
      calc
        w6Gaussian n m * 2 ^ (r * (n - m)) ≤
            (4 * 2 ^ (m * (n - m))) * 2 ^ (r * (n - m)) :=
          Nat.mul_le_mul_right _ hg
        _ = 4 * (2 ^ (m * (n - m)) * 2 ^ (r * (n - m))) := by ring
        _ = 4 * 2 ^ ((m + r) * (n - m)) := by
          rw [← pow_add, hsplit]

/-- Manuscript A9 choice product. For final dimensions `a+b+k ≤ D` and an
initial subspace of dimensions `i ≤ a`, `j ≤ b`, the Gaussian-and-graph count
is at most `2^{3D(i+j+k)}`. This is the numeric bound. It does not yet identify
the product with a fiber of initial triples, so it does not charge `Q`. -/
theorem a7_a9_multiplicity_le (D i j k a b : Nat)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b) :
    w6Gaussian a i * w6Gaussian b j * 2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) ≤
      2 ^ (3 * D * (i + j + k)) := by
  let t := i + j + k
  have haD : a ≤ D := by omega
  have hbD : b ≤ D := by omega
  have hik : i + k ≤ t := by omega
  have hjk : j + k ≤ t := by omega
  have hai : a - i ≤ D := by omega
  have hbj : b - j ≤ D := by omega
  have he1 : (i + k) * (a - i) ≤ t * D := Nat.mul_le_mul hik hai
  have he2 : (j + k) * (b - j) ≤ t * D := Nat.mul_le_mul hjk hbj
  have hesum : (i + k) * (a - i) + (j + k) * (b - j) ≤ 2 * D * t := by
    have hadd : (i + k) * (a - i) + (j + k) * (b - j) ≤ t * D + t * D :=
      Nat.add_le_add he1 he2
    have htwo : t * D + t * D = 2 * D * t := by ring
    rwa [htwo] at hadd
  have hgi := a7_gauss_graph_le a i k hi
  have hgj := a7_gauss_graph_le b j k hj
  have hprod :
      w6Gaussian a i * 2 ^ (k * (a - i)) *
          (w6Gaussian b j * 2 ^ (k * (b - j))) ≤
        ((if 0 < i ∧ i < a then 4 else 1) * 2 ^ ((i + k) * (a - i))) *
          ((if 0 < j ∧ j < b then 4 else 1) * 2 ^ ((j + k) * (b - j))) :=
    Nat.mul_le_mul hgi hgj
  have hreorder :
      w6Gaussian a i * w6Gaussian b j * 2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) =
        w6Gaussian a i * 2 ^ (k * (a - i)) *
          (w6Gaussian b j * 2 ^ (k * (b - j))) := by ring
  rw [hreorder]
  have hpow : 2 ^ ((i + k) * (a - i)) * 2 ^ ((j + k) * (b - j)) =
      2 ^ ((i + k) * (a - i) + (j + k) * (b - j)) := by
    rw [← pow_add]
  by_cases hia : 0 < i ∧ i < a
  · by_cases hjb : 0 < j ∧ j < b
    · have hDt : 4 ≤ D * t := by
        rcases hia with ⟨hi0, hia'⟩
        rcases hjb with ⟨hj0, hjb'⟩
        have ha2 : 2 ≤ a := by omega
        have hb2 : 2 ≤ b := by omega
        have ht2 : 2 ≤ t := by omega
        have hD2 : 2 ≤ D := by
          have hab : a + b ≤ D := by omega
          exact le_trans ha2 (le_trans (Nat.le_add_right a b) hab)
        simpa using Nat.mul_le_mul hD2 ht2
      have hexp : 4 + 2 * D * t ≤ 3 * D * t := by
        calc
          4 + 2 * D * t ≤ D * t + 2 * D * t := Nat.add_le_add_right hDt _
          _ = 3 * D * t := by ring
      have h16 : (16 : Nat) * 2 ^ (2 * D * t) = 2 ^ (4 + 2 * D * t) := by
        have htwo : (16 : Nat) = 2 ^ 4 := by norm_num
        rw [htwo, ← pow_add]
      calc
        _ ≤ (4 * 2 ^ ((i + k) * (a - i))) *
            (4 * 2 ^ ((j + k) * (b - j))) := by
          simpa [hia, hjb] using hprod
        _ = 16 * (2 ^ ((i + k) * (a - i)) * 2 ^ ((j + k) * (b - j))) := by ring
        _ = 16 * 2 ^ ((i + k) * (a - i) + (j + k) * (b - j)) := by rw [hpow]
        _ ≤ 16 * 2 ^ (2 * D * t) := by
          exact Nat.mul_le_mul_left 16
            (pow_le_pow_right₀ (by decide : 1 ≤ 2) hesum)
        _ = 2 ^ (4 + 2 * D * t) := h16
        _ ≤ 2 ^ (3 * D * t) := pow_le_pow_right₀ (by decide : 1 ≤ 2) hexp
    · have hDt : 2 ≤ D * t := by
        rcases hia with ⟨hi0, hia'⟩
        have ha2 : 2 ≤ a := by omega
        have ht1 : 1 ≤ t := by omega
        have hD2 : 2 ≤ D := by
          have haD' : a ≤ D := by omega
          exact le_trans ha2 haD'
        simpa using Nat.mul_le_mul hD2 ht1
      have hexp : 2 + 2 * D * t ≤ 3 * D * t := by
        calc
          2 + 2 * D * t ≤ D * t + 2 * D * t := Nat.add_le_add_right hDt _
          _ = 3 * D * t := by ring
      have h4 : (4 : Nat) * 2 ^ (2 * D * t) = 2 ^ (2 + 2 * D * t) := by
        have htwo : (4 : Nat) = 2 ^ 2 := by norm_num
        rw [htwo, ← pow_add]
      calc
        _ ≤ (4 * 2 ^ ((i + k) * (a - i))) *
            (1 * 2 ^ ((j + k) * (b - j))) := by
          simpa [hia, hjb] using hprod
        _ = 4 * (2 ^ ((i + k) * (a - i)) * 2 ^ ((j + k) * (b - j))) := by ring
        _ = 4 * 2 ^ ((i + k) * (a - i) + (j + k) * (b - j)) := by rw [hpow]
        _ ≤ 4 * 2 ^ (2 * D * t) :=
          Nat.mul_le_mul_left 4 (pow_le_pow_right₀ (by decide : 1 ≤ 2) hesum)
        _ = 2 ^ (2 + 2 * D * t) := h4
        _ ≤ 2 ^ (3 * D * t) := pow_le_pow_right₀ (by decide : 1 ≤ 2) hexp
  · by_cases hjb : 0 < j ∧ j < b
    · have hDt : 2 ≤ D * t := by
        rcases hjb with ⟨hj0, hjb'⟩
        have hb2 : 2 ≤ b := by omega
        have ht1 : 1 ≤ t := by omega
        have hD2 : 2 ≤ D := by
          have hbD' : b ≤ D := by omega
          exact le_trans hb2 hbD'
        simpa using Nat.mul_le_mul hD2 ht1
      have hexp : 2 + 2 * D * t ≤ 3 * D * t := by
        calc
          2 + 2 * D * t ≤ D * t + 2 * D * t := Nat.add_le_add_right hDt _
          _ = 3 * D * t := by ring
      have h4 : (4 : Nat) * 2 ^ (2 * D * t) = 2 ^ (2 + 2 * D * t) := by
        have htwo : (4 : Nat) = 2 ^ 2 := by norm_num
        rw [htwo, ← pow_add]
      calc
        _ ≤ (1 * 2 ^ ((i + k) * (a - i))) *
            (4 * 2 ^ ((j + k) * (b - j))) := by
          simpa [hia, hjb] using hprod
        _ = 4 * (2 ^ ((i + k) * (a - i)) * 2 ^ ((j + k) * (b - j))) := by ring
        _ = 4 * 2 ^ ((i + k) * (a - i) + (j + k) * (b - j)) := by rw [hpow]
        _ ≤ 4 * 2 ^ (2 * D * t) :=
          Nat.mul_le_mul_left 4 (pow_le_pow_right₀ (by decide : 1 ≤ 2) hesum)
        _ = 2 ^ (2 + 2 * D * t) := h4
        _ ≤ 2 ^ (3 * D * t) := pow_le_pow_right₀ (by decide : 1 ≤ 2) hexp
    · calc
        _ ≤ (1 * 2 ^ ((i + k) * (a - i))) *
            (1 * 2 ^ ((j + k) * (b - j))) := by
          simpa [hia, hjb] using hprod
        _ = 2 ^ ((i + k) * (a - i) + (j + k) * (b - j)) := by
          rw [one_mul, one_mul, ← pow_add]
        _ ≤ 2 ^ (2 * D * t) := pow_le_pow_right₀ (by decide : 1 ≤ 2) hesum
        _ ≤ 2 ^ (3 * D * t) :=
          pow_le_pow_right₀ (by decide : 1 ≤ 2) (by
            have htwice : 2 * D * t ≤ 2 * D * t + D * t := Nat.le_add_right _ _
            have hthree : 2 * D * t + D * t = 3 * D * t := by ring
            rwa [hthree] at htwice)

/-- The A8 graph cost `2^{6Dk}` and the A9 multiplicity `2^{3Dt}` fit in the
overlap room `2^{9Dt}` once `k ≤ t`. -/
theorem a7_a8_a9_room (D t k : Nat) (hk : k ≤ t) :
    (2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t) ≤ (2 : ℝ) ^ (9 * D * t) := by
  have h6 : 6 * D * k ≤ 6 * D * t := Nat.mul_le_mul_left (6 * D) hk
  have hsum : 6 * D * k + 3 * D * t ≤ 9 * D * t := by
    calc
      6 * D * k + 3 * D * t ≤ 6 * D * t + 3 * D * t := Nat.add_le_add_right h6 _
      _ = 9 * D * t := by ring
  calc
    (2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t) =
        (2 : ℝ) ^ (6 * D * k + 3 * D * t) := by rw [← pow_add]
    _ ≤ (2 : ℝ) ^ (9 * D * t) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsum

/-- Weight, induction, A8, and A9 together stay under the terminal allowance.
The factors are numeric. They do not build the transport or remove the share
hypothesis. -/
theorem a7_a8_a9_exponent_fits (D t k : Nat) (ht : 0 < t) (hle : t ≤ D)
    (hk : k ≤ t) :
    (2 : ℝ) ^ (24 * D * t) *
        ((2 : ℝ) ^ (100 * (D - t) * (D - t)) *
          ((2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t))) ≤
      (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
  have hroom := a7_a8_a9_room D t k hk
  have hshare := a7_triple_share_exponent_fits D t ht hle
  have hle9 : (2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t) ≤
      (2 : ℝ) ^ (9 * D * t) := hroom
  have hnn : 0 ≤ (2 : ℝ) ^ (24 * D * t) *
      (2 : ℝ) ^ (100 * (D - t) * (D - t)) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hmul := mul_le_mul_of_nonneg_left hle9 hnn
  have hassoc :
      (2 : ℝ) ^ (24 * D * t) * ((2 : ℝ) ^ (100 * (D - t) * (D - t)) *
        ((2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t))) =
        (2 : ℝ) ^ (24 * D * t) * (2 : ℝ) ^ (100 * (D - t) * (D - t)) *
          ((2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t)) := by ring
  rw [hassoc]
  have hshare' :
      (2 : ℝ) ^ (24 * D * t) * (2 : ℝ) ^ (100 * (D - t) * (D - t)) *
          (2 : ℝ) ^ (9 * D * t) ≤
        (2 : ℝ) ^ (100 * D * D) * (2 : ℝ) ^ ((1 : ℤ) - 31 * D) := by
    simpa [mul_assoc] using hshare
  exact le_trans hmul hshare'

/-- Rank-k predecessors of one final frequency are exactly the idempotent
graphs on its image. This is the injection of that fiber into the choice set. -/
theorem a7_predecessor_choice_injective {n d : Nat}
    (Y : BinaryMatrix n d) (k : Nat) :
    Function.Injective (w6_rank_k_predecessor_equiv Y k) :=
  (w6_rank_k_predecessor_equiv Y k).injective

/-- The rank-k predecessor fiber of a frequency of rank at most `D` has size
at most `2^{3 D k}`. This is the fiber of one final frequency, not the set of
all initial triples, and it does not remove the share hypothesis. -/
theorem a7_predecessor_fiber_le {n d D k : Nat} (Y : BinaryMatrix n d)
    (hr : Y.rank ≤ D) :
    Fintype.card (W6RankKPredecessor Y k) ≤ 2 ^ (3 * D * k) := by
  rw [w6_card_rank_k_predecessors]
  by_cases hk : k ≤ Y.rank
  · by_cases hk0 : k = 0
    · subst hk0
      simp [a7_w6Gaussian_zero]
    · have hg := w6_gaussian_le_four_pow hk
      have hmul : w6Gaussian Y.rank k * 2 ^ (k * (Y.rank - k)) ≤
          (4 * 2 ^ (k * (Y.rank - k))) * 2 ^ (k * (Y.rank - k)) :=
        Nat.mul_le_mul_right _ hg
      have hfour : (4 * 2 ^ (k * (Y.rank - k))) * 2 ^ (k * (Y.rank - k)) =
          4 * 2 ^ (2 * (k * (Y.rank - k))) := by
        rw [mul_assoc, ← pow_add]
        congr 1
        rw [two_mul]
      have hpow4 : 4 * 2 ^ (2 * (k * (Y.rank - k))) =
          2 ^ (2 + 2 * (k * (Y.rank - k))) := by
        have htwo : (4 : Nat) = 2 ^ 2 := by norm_num
        rw [htwo, ← pow_add]
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hsub : Y.rank - k ≤ D - k := Nat.sub_le_sub_right hr k
      have hkr : k * (Y.rank - k) ≤ k * (D - k) := Nat.mul_le_mul_left k hsub
      have h2 : 2 * (k * (Y.rank - k)) ≤ 2 * (k * (D - k)) :=
        Nat.mul_le_mul_left 2 hkr
      have htwo_k : 2 ≤ 2 * k := by
        calc
          2 = 2 * 1 := by ring
          _ ≤ 2 * k := Nat.mul_le_mul_left 2 hk1
      have hDk : k * (D - k) + k ≤ k * D := by
        have hstep : D - k + 1 ≤ D := by omega
        have hmul : k * (D - k + 1) ≤ k * D := Nat.mul_le_mul_left k hstep
        have hident : k * (D - k) + k = k * (D - k + 1) := by ring
        rwa [hident]
      have hpack : 2 * (k * (D - k)) + 2 * k ≤ 2 * (k * D) := by
        simpa [Nat.mul_add] using Nat.mul_le_mul_left 2 hDk
      have hexp : 2 + 2 * (k * (Y.rank - k)) ≤ 3 * D * k := by
        have hleft : 2 + 2 * (k * (Y.rank - k)) ≤ 2 + 2 * (k * (D - k)) :=
          Nat.add_le_add_left h2 2
        have hmid : 2 + 2 * (k * (D - k)) ≤ 2 * k + 2 * (k * (D - k)) :=
          Nat.add_le_add_right htwo_k _
        have hswap : 2 * k + 2 * (k * (D - k)) =
            2 * (k * (D - k)) + 2 * k := by ring
        have hmid' : 2 + 2 * (k * (D - k)) ≤ 2 * (k * (D - k)) + 2 * k := by
          rwa [hswap] at hmid
        have htoD : 2 * (k * (D - k)) + 2 * k ≤ 2 * (D * k) := by
          simpa [Nat.mul_comm] using hpack
        have h3 : 2 * (D * k) ≤ 3 * D * k := by
          have h23 : (2 : Nat) ≤ 3 := by decide
          have hmul := Nat.mul_le_mul_right (D * k) h23
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
        exact le_trans hleft (le_trans hmid' (le_trans htoD h3))
      calc
        w6Gaussian Y.rank k * 2 ^ (k * (Y.rank - k)) ≤
            (4 * 2 ^ (k * (Y.rank - k))) * 2 ^ (k * (Y.rank - k)) := hmul
        _ = 4 * 2 ^ (2 * (k * (Y.rank - k))) := hfour
        _ = 2 ^ (2 + 2 * (k * (Y.rank - k))) := hpow4
        _ ≤ 2 ^ (3 * D * k) := pow_le_pow_right₀ (by decide : 1 ≤ 2) hexp
  · have hzero : w6Gaussian Y.rank k = 0 := by
      unfold w6Gaussian
      rw [if_neg hk]
    simp [hzero]

/-- Coordinate identification of a binary space with a rank-`k` factor times
a complement. -/
noncomputable def a9CoordEquiv (k m : Nat) :
    (Fin (k + m) → F) ≃ₗ[F] ((Fin k → F) × (Fin m → F)) :=
  (LinearEquiv.piCongrLeft F (fun _ => F) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin m) F F)

/-- The rank-`k` graph map, transported onto `⊤ → (W / ⊥)`. -/
noncomputable def a9SumTheta (k m r : Nat)
    (psi : (Fin m → F) →ₗ[F] (Fin k → F))
    (imGraph : (Fin k → F) →ₗ[F] (Fin r → F)) :
    (⊤ : Submodule F (V (k + m))) →ₗ[F]
      (W (k + r) ⧸ (⊥ : Submodule F (W (k + r)))) :=
  (Submodule.mkQ (⊥ : Submodule F (W (k + r)))).comp
    (((a9CoordEquiv k r).symm.toLinearMap.comp
      ((a9Determined psi imGraph).comp (a9CoordEquiv k m).toLinearMap)).comp
      (⊤ : Submodule F (V (k + m))).subtype)

theorem a9_top_ne_bot {d : Nat} (hd : 0 < d) :
    (⊤ : Submodule F (V d)) ≠ ⊥ := by
  intro htop
  let v : V d := fun i => if i = ⟨0, hd⟩ then 1 else 0
  have hv : v ≠ 0 := by
    intro h0
    have hcoord := congrFun h0 ⟨0, hd⟩
    simp [v] at hcoord
  have hmem : v ∈ (⊤ : Submodule F (V d)) := Submodule.mem_top
  rw [htop, Submodule.mem_bot] at hmem
  exact hv hmem

/-- One index of the positive-degree mixed sum on the coordinate pair
`(⊤, ⊥)`. The side condition is exactly the nonzero-pair test. -/
structure A7GraphSumTriple (k m r : Nat) where
  triple : T1IndexTriple (⊤ : Submodule F (V (k + m)))
    (⊥ : Submodule F (W (k + r)))
  nonzero : (⊤ : Submodule F (V (k + m))) ≠ ⊥ ∨
    (⊥ : Submodule F (W (k + r))) ≠ ⊤

/-- A coordinate graph pair is one index of the positive-degree mixed sum:
the pair `(⊤, ⊥)` is a nonzero pair, and the triple is the transported
rank-`k` map. -/
noncomputable def a9SumTriple (k m r : Nat) (hk : 0 < k)
    (psi : (Fin m → F) →ₗ[F] (Fin k → F))
    (imGraph : (Fin k → F) →ₗ[F] (Fin r → F)) :
    A7GraphSumTriple k m r where
  triple := t1MapToTriple (a9SumTheta k m r psi imGraph)
  nonzero := Or.inl (a9_top_ne_bot (Nat.lt_of_lt_of_le hk (Nat.le_add_right k m)))

theorem a9SumTheta_injective {k m r : Nat}
    (psi₁ psi₂ : (Fin m → F) →ₗ[F] (Fin k → F))
    (im₁ im₂ : (Fin k → F) →ₗ[F] (Fin r → F))
    (h : a9SumTheta k m r psi₁ im₁ = a9SumTheta k m r psi₂ im₂) :
    psi₁ = psi₂ ∧ im₁ = im₂ := by
  have hdet : a9Determined psi₁ im₁ = a9Determined psi₂ im₂ := by
    apply LinearMap.ext
    intro p
    let eDom := a9CoordEquiv k m
    let eCod := a9CoordEquiv k r
    let x : (⊤ : Submodule F (V (k + m))) := ⟨eDom.symm p, Submodule.mem_top⟩
    have hx := congrFun (congrArg DFunLike.coe h) x
    have hcalc : ∀ (psi : (Fin m → F) →ₗ[F] (Fin k → F))
        (imGraph : (Fin k → F) →ₗ[F] (Fin r → F)),
        a9SumTheta k m r psi imGraph x =
          Submodule.mkQ (⊥ : Submodule F (W (k + r)))
            (eCod.symm (a9Determined psi imGraph p)) := by
      intro psi imGraph
      simp [a9SumTheta, x, eDom, eCod, LinearMap.comp_apply]
    rw [hcalc psi₁ im₁, hcalc psi₂ im₂] at hx
    have hinjQ : Function.Injective
        (Submodule.mkQ (⊥ : Submodule F (W (k + r)))) := by
      rw [← Submodule.coe_quotEquivOfEqBot_symm
        (⊥ : Submodule F (W (k + r))) rfl]
      exact (Submodule.quotEquivOfEqBot
        (⊥ : Submodule F (W (k + r))) rfl).symm.injective
    exact eCod.symm.injective (hinjQ hx)
  exact a9Determined_injective psi₁ psi₂ im₁ im₂ hdet

theorem a9SumTriple_injective {k m r : Nat} (hk : 0 < k) :
    Function.Injective (fun p : ((Fin m → F) →ₗ[F] (Fin k → F)) ×
        ((Fin k → F) →ₗ[F] (Fin r → F)) =>
      a9SumTriple k m r hk p.1 p.2) := by
  rintro ⟨psi₁, im₁⟩ ⟨psi₂, im₂⟩ h
  have htri := congrArg (fun s : A7GraphSumTriple k m r => s.triple) h
  have htheta :
      a9SumTheta k m r psi₁ im₁ = a9SumTheta k m r psi₂ im₂ := by
    simpa [a9SumTriple, t1TripleToMap_mapToTriple] using congrArg t1TripleToMap htri
  have hgraphs := a9SumTheta_injective psi₁ psi₂ im₁ im₂ htheta
  exact Prod.ext hgraphs.1 hgraphs.2

/-- `T1IndexTriple` is the indexed triple on the manuscript carriers
`A` and `W/B`. The graph fiber `a9_fiber_triple` uses this same field
package on the two graph subspaces. -/
def a9Indexed_t1_equiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    A9IndexedTriple A (W n ⧸ B) ≃ T1IndexTriple A B where
  toFun t := ⟨t.C, t.K, t.xbar⟩
  invFun t := ⟨t.C, t.K, t.Xbar⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The proved A9 graph fiber has multiplicity at most `2^{3D(i+j+k)}`
when the final datum satisfies `a+b+k ≤ D`. This is the fiber cardinality,
not a fresh exponent estimate. It does not remove the share hypothesis. -/
theorem a9_fiber_multiplicity_le
    {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B]
    [AddCommGroup S] [Module F S] [Module.Free F S] [Module.Finite F S]
    [Fintype S]
    (D i j k a b : Nat)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    Fintype.card ((Σ U : W6Grass A i, S →ₗ[F] (A ⧸ U.1)) ×
        (Σ V : W6Grass B j, S →ₗ[F] (B ⧸ V.1))) ≤
      2 ^ (3 * D * (i + j + k)) := by
  rw [a9_inducing_card i j k a b hA hB hS]
  have hbound := a7_a9_multiplicity_le D i j k a b hfin hi hj
  calc
    w6Gaussian a i * 2 ^ (k * (a - i)) *
        (w6Gaussian b j * 2 ^ (k * (b - j))) =
      w6Gaussian a i * w6Gaussian b j * 2 ^ (k * (a - i)) *
        2 ^ (k * (b - j)) := by ring
    _ ≤ 2 ^ (3 * D * (i + j + k)) := hbound

/-- The coordinate graph pairs at `i = j = 0` are at most `2^{3Dk}`.
`a9SumTriple` sends those pairs into the positive-degree sum, and this
bound is `a9_fiber_multiplicity_le` on that slice. It does not remove
the share hypothesis. -/
theorem a9_sum_triple_multiplicity_le (D k m r : Nat)
    (hfin : m + r + k ≤ D) :
    Fintype.card ((Fin m → F) →ₗ[F] (Fin k → F)) *
        Fintype.card ((Fin k → F) →ₗ[F] (Fin r → F)) ≤
      2 ^ (3 * D * k) := by
  classical
  have hfinrank_pi : ∀ n : Nat, Module.finrank F (Fin n → F) = n :=
    fun n => by
      simpa using (Module.finrank_fin_fun (n := n) F)
  have hgauss : ∀ n : Nat, w6Gaussian n 0 = 1 := by
    intro n
    unfold w6Gaussian w6FrameProduct
    rw [if_pos (Nat.zero_le n)]
    simp
  have hhom : ∀ (a b : Nat),
      Fintype.card ((Fin a → F) →ₗ[F] (Fin b → F)) = 2 ^ (b * a) := by
    intro a b
    rw [Module.card_eq_pow_finrank (K := F)
        (V := (Fin a → F) →ₗ[F] (Fin b → F)),
      Module.finrank_linearMap, ZMod.card, hfinrank_pi a, hfinrank_pi b,
      Nat.mul_comm]
  have hpsi := hhom m k
  have him : Fintype.card ((Fin k → F) →ₗ[F] (Fin r → F)) = 2 ^ (k * r) := by
    rw [hhom k r, Nat.mul_comm]
  have hsig := a9_inducing_card (A := Fin m → F) (B := Fin r → F)
      (S := Fin k → F) 0 0 k m r (hfinrank_pi m) (hfinrank_pi r) (hfinrank_pi k)
  have hbound := a9_fiber_multiplicity_le (A := Fin m → F) (B := Fin r → F)
      (S := Fin k → F) D 0 0 k m r hfin (Nat.zero_le m) (Nat.zero_le r)
      (hfinrank_pi m) (hfinrank_pi r) (hfinrank_pi k)
  have hprod :
      Fintype.card ((Fin m → F) →ₗ[F] (Fin k → F)) *
          Fintype.card ((Fin k → F) →ₗ[F] (Fin r → F)) =
        w6Gaussian m 0 * 2 ^ (k * (m - 0)) *
          (w6Gaussian r 0 * 2 ^ (k * (r - 0))) := by
    rw [hpsi, him, hgauss m, hgauss r, Nat.sub_zero, Nat.sub_zero]
    simp
  rw [hprod, ← hsig]
  simpa [Nat.zero_add, Nat.add_zero] using hbound

/-- Graph cost `2^{6Dk}` times the proved fiber multiplicity is at most the
overlap room `2^{9Dt}` for `t = i+j+k`. The share function in
`a7_positive_of_overlapping_shares` is still required: this does not bound
an output `Q` by one original component. -/
theorem a9_fiber_graph_cost_le
    {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B]
    [AddCommGroup S] [Module F S] [Module.Free F S] [Module.Finite F S]
    [Fintype S]
    (D i j k a b : Nat)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    (Fintype.card ((Σ U : W6Grass A i, S →ₗ[F] (A ⧸ U.1)) ×
        (Σ V : W6Grass B j, S →ₗ[F] (B ⧸ V.1))) : ℝ) *
      (2 : ℝ) ^ (6 * D * k) ≤
      (2 : ℝ) ^ (9 * D * (i + j + k)) := by
  let t := i + j + k
  have hcard := a9_fiber_multiplicity_le D i j k a b hfin hi hj hA hB hS
  have hpow : (Fintype.card ((Σ U : W6Grass A i, S →ₗ[F] (A ⧸ U.1)) ×
        (Σ V : W6Grass B j, S →ₗ[F] (B ⧸ V.1))) : ℝ) ≤
      (2 : ℝ) ^ (3 * D * t) := by
    exact_mod_cast hcard
  have hk : k ≤ t := Nat.le_add_left k (i + j)
  have hroom := a7_a8_a9_room D t k hk
  have hnn : 0 ≤ (2 : ℝ) ^ (6 * D * k) := pow_nonneg (by norm_num) _
  calc
    (Fintype.card ((Σ U : W6Grass A i, S →ₗ[F] (A ⧸ U.1)) ×
        (Σ V : W6Grass B j, S →ₗ[F] (B ⧸ V.1))) : ℝ) *
        (2 : ℝ) ^ (6 * D * k) ≤
      (2 : ℝ) ^ (3 * D * t) * (2 : ℝ) ^ (6 * D * k) :=
        mul_le_mul_of_nonneg_right hpow hnn
    _ = (2 : ℝ) ^ (6 * D * k) * (2 : ℝ) ^ (3 * D * t) := by ring
    _ ≤ (2 : ℝ) ^ (9 * D * t) := hroom

/-- The general-subspace initial datum has the same cardinality as the
counted same-variance fiber, so the proved multiplicity applies. The kernel
graph runs out of the quotient. This does not remove the share hypothesis. -/
theorem a9_initial_datum_multiplicity_le
    {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B]
    [AddCommGroup S] [Module F S] [Module.Free F S] [Module.Finite F S]
    [Fintype S]
    (D i j k a b : Nat)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    Fintype.card (A9InitialDatum A B S i j) ≤ 2 ^ (3 * D * (i + j + k)) := by
  have hdatum := a9_initial_datum_card i j k a b hA hB hS
  have hfiber := a9_fiber_multiplicity_le D i j k a b hfin hi hj hA hB hS
  rw [a9_inducing_card i j k a b hA hB hS] at hfiber
  rwa [hdatum]

/-- Graph cost of the general-subspace datum is the proved fiber cost. -/
theorem a9_initial_datum_graph_cost_le
    {A B S : Type*} [AddCommGroup A] [Module F A]
    [Module.Free F A] [Module.Finite F A] [Fintype A]
    [AddCommGroup B] [Module F B] [Module.Free F B] [Module.Finite F B]
    [Fintype B]
    [AddCommGroup S] [Module F S] [Module.Free F S] [Module.Finite F S]
    [Fintype S]
    (D i j k a b : Nat)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a) (hB : Module.finrank F B = b)
    (hS : Module.finrank F S = k) :
    (Fintype.card (A9InitialDatum A B S i j) : ℝ) * (2 : ℝ) ^ (6 * D * k) ≤
      (2 : ℝ) ^ (9 * D * (i + j + k)) := by
  have hdatum := a9_initial_datum_card i j k a b hA hB hS
  have hcost := a9_fiber_graph_cost_le D i j k a b hfin hi hj hA hB hS
  have hfiber := a9_inducing_card i j k a b hA hB hS
  rw [hdatum]
  rw [hfiber] at hcost
  exact hcost

/-- The zero-order summand of one output `Q` injects into that triple's
original hybrid component. The factor `2^{4k(D-t)}` fits in the fiber room
`2^{9Dt}` because `k ≤ t`. Positive-order summands of the output `Q` are
not included, so this does not remove the share hypothesis. -/
theorem a7_output_zero_share_le_original_component {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) :
    a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
        (a7OutputBinary t T f) ≤
      (2 : ℝ) ^ (9 * D * a6Order t) *
        typedW6QComponent (t1AmbientC t.C) (t1AmbientH t.K) T f := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let parent := a7MixedCoordinateParent t
  let coord := a7MixedCoordinate t T f
  let Cout := LinearMap.range parent.transpose.toLin'
  let Hout := LinearMap.ker parent.transpose.toLin'
  let deriv := actualW6Derivative parent 0 coord
  have hE := typedW6OutputEnergy_coordinate C H X
    (filteredCarrierFunction C H T f)
  have henergy : typedW6OutputEnergy C H X (filteredCarrierFunction C H T f) =
      carrierMean Cout Hout (fun M => Complex.normSq (deriv M)) := by
    rw [hE]
    rfl
  have hsq := a7_output_energy_sq_le_component t T f hsupport horder
  have hexp : 4 * Module.finrank F (LinearMap.range X) * (D - a6Order t) ≤
      9 * D * a6Order t := by
    let k := Module.finrank F (LinearMap.range X)
    let ord := a6Order t
    have hk : k ≤ ord := by
      dsimp [k, ord, a6Order, C, H, X]
      exact Nat.le_add_left _ _
    have hsub : D - ord ≤ D := Nat.sub_le D ord
    calc
      4 * k * (D - ord) ≤ 4 * ord * (D - ord) :=
        Nat.mul_le_mul_right (D - ord) (Nat.mul_le_mul_left 4 hk)
      _ ≤ 4 * ord * D := Nat.mul_le_mul_left (4 * ord) hsub
      _ = 4 * (D * ord) := by ring
      _ ≤ 9 * (D * ord) := Nat.mul_le_mul_right (D * ord) (by decide : (4 : Nat) ≤ 9)
      _ = 9 * D * ord := by ring
  have hcomp : 0 ≤ typedW6QComponent C H T f := by
    unfold typedW6QComponent
    exact sq_nonneg _
  have hpow : (2 : ℝ) ^ (4 * Module.finrank F (LinearMap.range X) *
      (D - a6Order t)) ≤ (2 : ℝ) ^ (9 * D * a6Order t) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [a7_output_zero_share_eq_l2, a7_output_binary_l2_sq, henergy]
  exact le_trans hsq (mul_le_mul_of_nonneg_right hpow hcomp)

/-- One image graph, as a submodule of the coordinate carrier `V(k+a)`.
Transport uses the coordinate equivalence, not a chosen complement. This is
not a `T1IndexTriple` in the positive-degree sum, and it does not remove
the share hypothesis. -/
noncomputable def a9ImageCarrier (k a : Nat) {i : Nat}
    (g : Σ U : W6Grass (V a) i, (Fin k → F) →ₗ[F] ((V a) ⧸ U.1)) :
    Submodule F (V (k + a)) :=
  Submodule.map (a9CoordEquiv k a).symm.toLinearMap (a9GraphPreimage g.1.1 g.2)

theorem a9ImageCarrier_preimage (k a : Nat) {i : Nat}
    (g : Σ U : W6Grass (V a) i, (Fin k → F) →ₗ[F] ((V a) ⧸ U.1)) :
    Submodule.map (a9CoordEquiv k a).toLinearMap (a9ImageCarrier k a g) =
      a9GraphPreimage g.1.1 g.2 := by
  unfold a9ImageCarrier
  rw [← Submodule.map_comp]
  have hid : (a9CoordEquiv k a).toLinearMap.comp
      (a9CoordEquiv k a).symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact (a9CoordEquiv k a).apply_symm_apply x
  rw [hid, Submodule.map_id]

theorem a9ImageCarrier_injective (k a i : Nat) :
    Function.Injective (a9ImageCarrier (k := k) (a := a) (i := i)) := by
  intro g₁ g₂ h
  have hpre : a9GraphPreimage g₁.1.1 g₁.2 = a9GraphPreimage g₂.1.1 g₂.2 := by
    rw [← a9ImageCarrier_preimage k a g₁, ← a9ImageCarrier_preimage k a g₂, h]
  have hU := a9_preimage_subspace_inverse g₁.1.1 g₂.1.1 g₁.2 g₂.2 hpre
  rcases g₁ with ⟨U₁, phi₁⟩
  rcases g₂ with ⟨U₂, phi₂⟩
  have hUs : U₁ = U₂ := Subtype.ext hU
  subst hUs
  have hphi := a9_preimage_graphs_inverse U₁.1 phi₁ phi₂ hpre
  cases hphi
  rfl

/-- The ambient hybrid filter keeps the selected Fourier coefficients and
drops the others. -/
theorem a7_ambient_hybrid_fourierCoeff {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : BinaryMatrix n d → ℝ) (Y : BinaryMatrix n d) :
    fourierCoeff (ambientHybridFilter A B g) Y =
      if Selected A B Y.transpose.toLin' then fourierCoeff g Y else 0 := by
  classical
  have hcard : (Fintype.card (BinaryMatrix n d) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (BinaryMatrix n d) ≠ 0)
  have horth : ∀ Z : BinaryMatrix n d,
      (∑ M : BinaryMatrix n d, character Z M * character Y M) =
        (if Y = Z then (1 : ℝ) else 0) *
          (Fintype.card (BinaryMatrix n d) : ℝ) := by
    intro Z
    have ho := character_orthogonality Y Z
    unfold uniformMean at ho
    have hcomm : (∑ M : BinaryMatrix n d, character Y M * character Z M) =
        ∑ M : BinaryMatrix n d, character Z M * character Y M := by
      apply Finset.sum_congr rfl
      intro M _
      ring
    rw [hcomm] at ho
    exact (div_eq_iff hcard).mp ho
  change uniformMean (fun M => ambientHybridFilter A B g M * character Y M) =
    if Selected A B Y.transpose.toLin' then fourierCoeff g Y else 0
  unfold uniformMean ambientHybridFilter
  have hnum :
      (∑ M : BinaryMatrix n d,
        (∑ Z : BinaryMatrix n d,
          if Selected A B Z.transpose.toLin' then
            fourierCoeff g Z * character Z M else 0) * character Y M) =
        (if Selected A B Y.transpose.toLin' then fourierCoeff g Y else 0) *
          (Fintype.card (BinaryMatrix n d) : ℝ) := by
    have hcomm :
        (∑ M : BinaryMatrix n d,
          (∑ Z : BinaryMatrix n d,
            if Selected A B Z.transpose.toLin' then
              fourierCoeff g Z * character Z M else 0) * character Y M) =
          ∑ Z : BinaryMatrix n d,
            ∑ M : BinaryMatrix n d,
              (if Selected A B Z.transpose.toLin' then
                fourierCoeff g Z * character Z M else 0) * character Y M := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    have hinner :
        (∑ Z : BinaryMatrix n d,
          ∑ M : BinaryMatrix n d,
            (if Selected A B Z.transpose.toLin' then
              fourierCoeff g Z * character Z M else 0) * character Y M) =
          ∑ Z : BinaryMatrix n d,
            if Selected A B Z.transpose.toLin' then
              fourierCoeff g Z *
                (∑ M : BinaryMatrix n d, character Z M * character Y M)
            else 0 := by
      refine Finset.sum_congr rfl ?_
      intro Z _
      by_cases hsel : Selected A B Z.transpose.toLin'
      · simp only [if_pos hsel]
        simp_rw [mul_assoc]
        exact (Finset.mul_sum Finset.univ
          (fun M => character Z M * character Y M) (fourierCoeff g Z)).symm
      · simp only [if_neg hsel]
        refine Finset.sum_eq_zero ?_
        intro M _
        exact zero_mul _
    rw [hcomm, hinner]
    have hsingle :
        (∑ Z : BinaryMatrix n d,
          if Selected A B Z.transpose.toLin' then
            fourierCoeff g Z *
              (∑ M : BinaryMatrix n d, character Z M * character Y M)
          else 0) =
          if Selected A B Y.transpose.toLin' then
            fourierCoeff g Y *
              (∑ M : BinaryMatrix n d, character Y M * character Y M)
          else 0 := by
      refine Finset.sum_eq_single Y ?_ ?_
      · intro Z _ hne
        by_cases hsel : Selected A B Z.transpose.toLin'
        · rw [if_pos hsel, horth Z, if_neg (Ne.symm hne)]
          simp
        · rw [if_neg hsel]
      · intro hmiss
        exact absurd (Finset.mem_univ Y) hmiss
    rw [hsingle]
    by_cases hsel : Selected A B Y.transpose.toLin'
    · rw [if_pos hsel, if_pos hsel, horth Y, if_pos rfl]
      ring
    · rw [if_neg hsel, if_neg hsel]
      exact (zero_mul _).symm
  rw [hnum]
  exact mul_div_cancel_right₀ _ hcard

/-- One ambient hybrid filter has `L2` energy at most the full energy,
because it keeps a subset of the Fourier coefficients. This is one filter.
`a7HybridQ` sums one square per subspace pair, so this does not remove the
share hypothesis. -/
theorem a7_ambient_hybrid_energy_le {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : BinaryMatrix n d → ℝ) :
    uniformMean (fun M => (ambientHybridFilter A B g M) ^ 2) ≤
      uniformMean (fun M => g M ^ 2) := by
  classical
  rw [fourier_parseval, fourier_parseval]
  refine Finset.sum_le_sum ?_
  intro Y _
  rw [a7_ambient_hybrid_fourierCoeff]
  by_cases hsel : Selected A B Y.transpose.toLin'
  · simp [hsel]
  · simp [hsel, sq_nonneg]

/-- Initial graph data for one fixed final `(A, B, Y)`. The image graphs
live in `A` and the kernel graphs live in `W/B`; the rank-`k` space is
`range Y`. Reading `a9InitialMap` recovers both graphs, and its rank equals
the rank of `Y`. -/
theorem a9_final_inducing_rank {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Y : W n →ₗ[F] V d) {i j : Nat}
    (datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) :
    Module.finrank F (LinearMap.range (a9InitialMap datum)) =
      Module.finrank F (LinearMap.range Y) := by
  haveI : Module.Finite F (LinearMap.range Y) := inferInstance
  exact a9InitialMap_rank datum

theorem a9_final_inducing_graphs_inverse {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Y : W n →ₗ[F] V d) {i j : Nat}
    (U : W6Grass A i) (V : W6Grass (W n ⧸ B) j)
    (im₁ im₂ : (LinearMap.range Y) →ₗ[F] (A ⧸ U.1))
    (ker₁ ker₂ : ((W n ⧸ B) ⧸ V.1) →ₗ[F] (LinearMap.range Y))
    (h : a9Determined ker₁ im₁ = a9Determined ker₂ im₂) :
    ker₁ = ker₂ ∧ im₁ = im₂ :=
  a9InitialMap_graphs_inverse U V im₁ im₂ ker₁ ker₂ h

/-- The initial graph fiber of one fixed final has the proved multiplicity
`2^{3D(i+j+k)}` whenever `a+b+k ≤ D`. This cites
`a9_initial_datum_multiplicity_le`. It does not remove the share hypothesis. -/
theorem a9_final_inducing_multiplicity {n d : Nat}
    (D i j k a b : Nat)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k) :
    Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) ≤
      2 ^ (3 * D * (i + j + k)) := by
  classical
  haveI : Module.Finite F A := inferInstance
  haveI : Module.Free F A := Module.Free.of_basis (Module.finBasis F A)
  haveI : Module.Finite F (W n ⧸ B) := inferInstance
  haveI : Module.Free F (W n ⧸ B) :=
    Module.Free.of_basis (Module.finBasis F (W n ⧸ B))
  haveI : Module.Finite F (LinearMap.range Y) := inferInstance
  haveI : Module.Free F (LinearMap.range Y) :=
    Module.Free.of_basis (Module.finBasis F (LinearMap.range Y))
  exact a9_initial_datum_multiplicity_le D i j k a b hfin hi hj hA hB hY

/-- Graph cost of that same final fiber is the proved bound
`2^{6Dk}` times the multiplicity, which is at most `2^{9D(i+j+k)}`. -/
theorem a9_final_inducing_graph_cost {n d : Nat}
    (D i j k a b : Nat)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k) :
    (Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) : ℝ) *
        (2 : ℝ) ^ (6 * D * k) ≤
      (2 : ℝ) ^ (9 * D * (i + j + k)) := by
  classical
  haveI : Module.Finite F A := inferInstance
  haveI : Module.Free F A := Module.Free.of_basis (Module.finBasis F A)
  haveI : Module.Finite F (W n ⧸ B) := inferInstance
  haveI : Module.Free F (W n ⧸ B) :=
    Module.Free.of_basis (Module.finBasis F (W n ⧸ B))
  haveI : Module.Finite F (LinearMap.range Y) := inferInstance
  haveI : Module.Free F (LinearMap.range Y) :=
    Module.Free.of_basis (Module.finBasis F (LinearMap.range Y))
  exact a9_initial_datum_graph_cost_le D i j k a b hfin hi hj hA hB hY

/-- Embed a subspace of `range Y` as the selected pair `(A, Y⁻¹(A))`. -/
def a7RangeSubspaceAmbient {n d : Nat} (Y : W n →ₗ[F] V d)
    (A : Submodule F (LinearMap.range Y)) : Submodule F (V d) :=
  A.map (LinearMap.range Y).subtype

def a7RangeSubspaceKernel {n d : Nat} (Y : W n →ₗ[F] V d)
    (A : Submodule F (LinearMap.range Y)) : Submodule F (W n) :=
  Submodule.comap Y (a7RangeSubspaceAmbient Y A)

theorem a7_range_subspace_selected {n d : Nat} (Y : W n →ₗ[F] V d)
    (A : Submodule F (LinearMap.range Y)) :
    Selected (a7RangeSubspaceAmbient Y A) (a7RangeSubspaceKernel Y A) Y := by
  constructor
  · intro v hv
    rcases hv with ⟨a, _, rfl⟩
    exact a.property
  · intro w hw
    simpa [a7RangeSubspaceKernel, a7RangeSubspaceAmbient] using hw

theorem a7_range_subspace_ambient_injective {n d : Nat} (Y : W n →ₗ[F] V d) :
    Function.Injective (a7RangeSubspaceAmbient Y) := by
  intro A₁ A₂ h
  ext x
  constructor
  · intro hx
    have hmem : (x : V d) ∈ a7RangeSubspaceAmbient Y A₂ := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    rcases hmem with ⟨y, hy, heq⟩
    have hxy : x = y := Subtype.ext heq.symm
    simpa [hxy] using hy
  · intro hx
    have hmem : (x : V d) ∈ a7RangeSubspaceAmbient Y A₁ := by
      rw [h]
      exact ⟨x, hx, rfl⟩
    rcases hmem with ⟨y, hy, heq⟩
    have hxy : x = y := Subtype.ext heq.symm
    simpa [hxy] using hy

/-- Distinct subspaces of the image give distinct selected pairs. -/
def a7SelectedOfRangeSubspace {n d : Nat} (Y : W n →ₗ[F] V d)
    (A : Submodule F (LinearMap.range Y)) :
    {p : Submodule F (V d) × Submodule F (W n) // Selected p.1 p.2 Y} :=
  ⟨(a7RangeSubspaceAmbient Y A, a7RangeSubspaceKernel Y A),
    a7_range_subspace_selected Y A⟩

theorem a7SelectedOfRangeSubspace_injective {n d : Nat} (Y : W n →ₗ[F] V d) :
    Function.Injective (a7SelectedOfRangeSubspace Y) := by
  intro A₁ A₂ h
  have hamb := congrArg (fun p => p.1.1) h
  exact a7_range_subspace_ambient_injective Y hamb

/-- The 12-planes in a 24-dimensional image already outnumber the slack
`2^{9*25 - 4*24}` left after the zero-order factor `2^{4k(D-t)}` at
`D = 25`, `t = 1`, `k = 1`. Charging every selected pair the full
zero-order share does not fit in `2^{9Dt}`. This does not evaluate
`a7HybridQ` of `a7OutputBinary`, and it does not remove the share. -/
theorem a7_middle_grassmannian_exceeds_share_slack :
    2 ^ (9 * 25 - 4 * 24) < w6Gaussian 24 12 := by
  decide

theorem a7_selected_pairs_exceed_share_slack {n d : Nat}
    (Y : W n →ₗ[F] V d)
    (hY : Module.finrank F (LinearMap.range Y) = 24) :
    2 ^ (9 * 25 - 4 * 24) <
      Fintype.card {p : Submodule F (V d) × Submodule F (W n) //
        Selected p.1 p.2 Y} := by
  classical
  haveI : Fintype (LinearMap.range Y) := Fintype.ofFinite _
  haveI : Module.Finite F (LinearMap.range Y) := inferInstance
  haveI : Module.Free F (LinearMap.range Y) :=
    Module.Free.of_basis (Module.finBasis F (LinearMap.range Y))
  have hgrass : Fintype.card (W6Grass (LinearMap.range Y) 12) =
      w6Gaussian 24 12 := by
    rw [w6_card_grass, hY]
  let emb : W6Grass (LinearMap.range Y) 12 →
      {p : Submodule F (V d) × Submodule F (W n) // Selected p.1 p.2 Y} :=
    fun A => a7SelectedOfRangeSubspace Y A.1
  have hinj : Function.Injective emb := by
    intro A₁ A₂ h
    have hA := a7SelectedOfRangeSubspace_injective Y h
    exact Subtype.ext hA
  have hcard : Fintype.card (W6Grass (LinearMap.range Y) 12) ≤
      Fintype.card {p : Submodule F (V d) × Submodule F (W n) //
        Selected p.1 p.2 Y} :=
    Fintype.card_le_of_injective emb hinj
  have hlt := a7_middle_grassmannian_exceeds_share_slack
  exact lt_of_lt_of_le hlt (by rw [← hgrass]; exact hcard)

theorem a9_coord_quot_finrank {n i : Nat} (U : W6Grass (V n) i) :
    Module.finrank F ((V n) ⧸ U.1) = n - i := by
  have hsum := U.1.finrank_quotient_add_finrank
  have hE : Module.finrank F (V n) = n := by
    simpa using (Module.finrank_fin_fun (n := n) F)
  rw [U.2, hE] at hsum
  simpa [Nat.add_sub_cancel] using congrArg (fun t => t - i) hsum

noncomputable def a9QuotToFin {n i : Nat} (U : W6Grass (V n) i) :
    ((V n) ⧸ U.1) ≃ₗ[F] (Fin (n - i) → F) :=
  haveI : Module.Finite F ((V n) ⧸ U.1) := inferInstance
  haveI : Module.Free F ((V n) ⧸ U.1) :=
    Module.Free.of_basis (Module.finBasis F ((V n) ⧸ U.1))
  (Module.finBasis F ((V n) ⧸ U.1)).equivFun.trans
    (LinearEquiv.piCongrLeft F (fun _ => F)
      (Equiv.cast (congrArg Fin (a9_coord_quot_finrank U))))

noncomputable def a9FinalDomEquiv {b j k : Nat} (B0 : W6Grass (V b) j) :
    ((V k) × ((V b) ⧸ B0.1)) ≃ₗ[F] (V (k + (b - j))) :=
  (LinearEquiv.prodCongr (LinearEquiv.refl F (V k)) (a9QuotToFin B0)).trans
    (a9CoordEquiv k (b - j)).symm

noncomputable def a9FinalCodEquiv {a i k : Nat} (A0 : W6Grass (V a) i) :
    ((V k) × ((V a) ⧸ A0.1)) ≃ₗ[F] (V (k + (a - i))) :=
  (LinearEquiv.prodCongr (LinearEquiv.refl F (V k)) (a9QuotToFin A0)).trans
    (a9CoordEquiv k (a - i)).symm

/-- The project-then-lift map of one coordinate datum, as a sum-index map
`⊤ → W/⊥`. -/
noncomputable def a9FinalTheta {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    (⊤ : Submodule F (V (k + (b - j)))) →ₗ[F]
      (W (k + (a - i)) ⧸ (⊥ : Submodule F (W (k + (a - i))))) :=
  (Submodule.mkQ (⊥ : Submodule F (W (k + (a - i))))).comp
    ((a9FinalCodEquiv d.A0).toLinearMap.comp
      ((a9InitialMap d).comp
        ((a9FinalDomEquiv d.B0).symm.toLinearMap.comp
          (⊤ : Submodule F (V (k + (b - j)))).subtype)))

theorem a9FinalTheta_graphs_inverse {a b k i j : Nat}
    (A0 : W6Grass (V a) i) (B0 : W6Grass (V b) j)
    (im₁ im₂ : (V k) →ₗ[F] ((V a) ⧸ A0.1))
    (ker₁ ker₂ : ((V b) ⧸ B0.1) →ₗ[F] (V k))
    (h : a9FinalTheta ⟨A0, B0, im₁, ker₁⟩ =
      a9FinalTheta ⟨A0, B0, im₂, ker₂⟩) :
    ker₁ = ker₂ ∧ im₁ = im₂ := by
  have hmap : a9InitialMap ⟨A0, B0, im₁, ker₁⟩ =
      a9InitialMap ⟨A0, B0, im₂, ker₂⟩ := by
    apply LinearMap.ext
    intro p
    let eDom := a9FinalDomEquiv (k := k) B0
    let eCod := a9FinalCodEquiv (k := k) A0
    let x : (⊤ : Submodule F (V (k + (b - j)))) := ⟨eDom p, Submodule.mem_top⟩
    have hx := congrFun (congrArg DFunLike.coe h) x
    have hcalc : ∀ (im : (V k) →ₗ[F] ((V a) ⧸ A0.1))
        (ker : ((V b) ⧸ B0.1) →ₗ[F] (V k)),
        a9FinalTheta ⟨A0, B0, im, ker⟩ x =
          Submodule.mkQ (⊥ : Submodule F (W (k + (a - i))))
            (eCod (a9InitialMap ⟨A0, B0, im, ker⟩ p)) := by
      intro im ker
      simp [a9FinalTheta, x, eDom, eCod, LinearMap.comp_apply]
    rw [hcalc im₁ ker₁, hcalc im₂ ker₂] at hx
    have hinjQ : Function.Injective
        (Submodule.mkQ (⊥ : Submodule F (W (k + (a - i))))) := by
      rw [← Submodule.coe_quotEquivOfEqBot_symm
        (⊥ : Submodule F (W (k + (a - i)))) rfl]
      exact (Submodule.quotEquivOfEqBot
        (⊥ : Submodule F (W (k + (a - i)))) rfl).symm.injective
    exact eCod.injective (hinjQ hx)
  exact a9InitialMap_graphs_inverse A0 B0 im₁ im₂ ker₁ ker₂
    (by simpa [a9InitialMap] using hmap)

/-- One coordinate initial datum, as a nonzero pair plus a `T1IndexTriple`.
`A7GraphSumTriple` is an index of the positive-degree mixed sum. The
subspaces travel with the index, so distinct data stay distinct. This does
not bound `a7HybridQ` of an output, and it does not remove the share. -/
structure A9EmbeddedSumFiber (a b k i j : Nat) where
  A0 : W6Grass (V a) i
  B0 : W6Grass (V b) j
  index : A7GraphSumTriple k (b - j) (a - i)

noncomputable def a9EmbedSumFiber {a b k i j : Nat} (hk : 0 < k)
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    A9EmbeddedSumFiber a b k i j where
  A0 := d.A0
  B0 := d.B0
  index := {
    triple := t1MapToTriple (a9FinalTheta d)
    nonzero := Or.inl (a9_top_ne_bot
      (Nat.lt_of_lt_of_le hk (Nat.le_add_right k (b - j)))) }

theorem a9EmbedSumFiber_injective {a b k i j : Nat} (hk : 0 < k) :
    Function.Injective (a9EmbedSumFiber (a := a) (b := b) (k := k)
      (i := i) (j := j) hk) := by
  intro d₁ d₂ h
  have hA : d₁.A0 = d₂.A0 := congrArg A9EmbeddedSumFiber.A0 h
  have hB : d₁.B0 = d₂.B0 := congrArg A9EmbeddedSumFiber.B0 h
  have hidx := congrArg A9EmbeddedSumFiber.index h
  cases d₁ with
  | mk A1 B1 im₁ ker₁ =>
    cases d₂ with
    | mk A2 B2 im₂ ker₂ =>
      subst hA
      subst hB
      have htri := congrArg A7GraphSumTriple.triple hidx
      have htheta : a9FinalTheta ⟨A1, B1, im₁, ker₁⟩ =
          a9FinalTheta ⟨A1, B1, im₂, ker₂⟩ := by
        simpa [a9EmbedSumFiber, t1TripleToMap_mapToTriple] using
          congrArg t1TripleToMap htri
      have hgraphs := a9FinalTheta_graphs_inverse A1 B1 im₁ im₂ ker₁ ker₂ htheta
      cases hgraphs.1
      cases hgraphs.2
      rfl

/-- The transported sum-index map has rank `k`, the same rank as the
coordinate project-then-lift map. The two outer arrows are linear
equivalences, so they do not change the rank. This does not bound
`a7HybridQ` of an output, and it does not remove the share. -/
theorem a9FinalTheta_rank {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    Module.finrank F (LinearMap.range (a9FinalTheta d)) = k := by
  classical
  let eDom := a9FinalDomEquiv (k := k) d.B0
  let eCod := a9FinalCodEquiv (k := k) d.A0
  let right := eDom.symm.toLinearMap.comp
    (⊤ : Submodule F (V (k + (b - j)))).subtype
  let eQ : (W (k + (a - i))) ≃ₗ[F]
      (W (k + (a - i)) ⧸ (⊥ : Submodule F (W (k + (a - i))))) :=
    (Submodule.quotEquivOfEqBot
      (⊥ : Submodule F (W (k + (a - i)))) rfl).symm
  have hmk : eQ.toLinearMap =
      Submodule.mkQ (⊥ : Submodule F (W (k + (a - i)))) :=
    Submodule.coe_quotEquivOfEqBot_symm
      (⊥ : Submodule F (W (k + (a - i)))) rfl
  have hsurj : Function.Surjective right := by
    intro y
    obtain ⟨x, hx⟩ := eDom.symm.surjective y
    use ⟨x, Submodule.mem_top⟩
    simpa [right, LinearMap.comp_apply] using hx
  have htheta : a9FinalTheta d =
      eQ.toLinearMap.comp (eCod.toLinearMap.comp
        ((a9InitialMap d).comp right)) := by
    rw [hmk]
    rfl
  have hrangemid : LinearMap.range ((a9InitialMap d).comp right) =
      LinearMap.range (a9InitialMap d) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hcod : LinearMap.range (eCod.toLinearMap.comp
        ((a9InitialMap d).comp right)) =
      Submodule.map eCod.toLinearMap (LinearMap.range (a9InitialMap d)) := by
    rw [LinearMap.range_comp, hrangemid]
  have hq : LinearMap.range (eQ.toLinearMap.comp (eCod.toLinearMap.comp
        ((a9InitialMap d).comp right))) =
      Submodule.map eQ.toLinearMap
        (Submodule.map eCod.toLinearMap (LinearMap.range (a9InitialMap d))) := by
    rw [LinearMap.range_comp, hcod]
  rw [htheta, hq, LinearEquiv.finrank_map_eq eQ, LinearEquiv.finrank_map_eq eCod]
  have hrank := a9InitialMap_rank d
  have hk : Module.finrank F (V k) = k := by
    simpa using (Module.finrank_fin_fun (n := k) F)
  rw [hrank, hk]

/-- The half-dimensional Grassmannian of a 38-dimensional binary space is
larger than the order-one room `2^{9*40}`. -/
theorem a7_gaussian_38_19_gt_order_one :
    2 ^ (9 * 40) < w6Gaussian 38 19 := by
  decide

private lemma a7_carrierMean_const {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) (c : ℝ) :
    carrierMean A B (fun _ : (V d ⧸ A) →ₗ[F] B => c) = c := by
  unfold carrierMean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpos : 0 < Fintype.card ((V d ⧸ A) →ₗ[F] B) :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  exact mul_div_cancel_left₀ c (by exact_mod_cast (Nat.ne_of_gt hpos))

private lemma a7_sign_normSq (x : ℝ) (hx : x = 1 ∨ x = -1) :
    Complex.normSq (x : ℂ) = 1 := by
  rcases hx with rfl | rfl <;> simp [Complex.normSq_ofReal]

private lemma a7_sign_mul (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- One subspace pair contributes `1` to the unweighted `Q` of a character
exactly when it selects that character, and contributes `0` otherwise. -/
theorem a7_character_qComponent {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Y : BinaryMatrix n d) :
    typedW6QComponent A B T (fun M => (character Y M : ℂ)) =
      if Selected A B Y.transpose.toLin' then 1 else 0 := by
  classical
  unfold typedW6QComponent
  have hpt : ∀ M : (V d ⧸ A) →ₗ[F] B,
      Complex.normSq (filteredCarrierFunction A B T
        (fun X => (character Y X : ℂ)) M) =
        if Selected A B Y.transpose.toLin' then 1 else 0 := by
    intro M
    rw [filteredCarrierFunction_character]
    by_cases hsel : Selected A B Y.transpose.toLin'
    · simp only [hsel, if_pos]
      let phase := traceCharacter Y.transpose.toLin' T
      let induced :=
        traceCharacter (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M
      have hphase : phase = 1 ∨ phase = -1 := by
        unfold phase traceCharacter
        by_cases h0 : tracePair Y.transpose.toLin' T = 0 <;> simp [h0]
      have hind : induced = 1 ∨ induced = -1 := by
        unfold induced traceCharacter
        by_cases h0 :
            tracePair (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M = 0 <;>
          simp [h0]
      exact a7_sign_normSq _ (a7_sign_mul _ _ hphase hind)
    · simp [hsel, Complex.normSq_zero]
  simp only [hpt]
  rw [a7_carrierMean_const]
  by_cases hsel : Selected A B Y.transpose.toLin'
  · simp [hsel]
  · simp [hsel]

/-- Unweighted `Q` of one character equals the number of subspace pairs that
select it. Each selecting pair contributes its full squared carrier energy. -/
theorem a7_character_hybrid_q {n d : Nat} (Y : BinaryMatrix n d) :
    a7HybridQ (fun M => (character Y M : ℂ)) =
      (Fintype.card {p : Submodule F (V d) × Submodule F (W n) //
        Selected p.1 p.2 Y.transpose.toLin'} : ℝ) := by
  classical
  unfold a7HybridQ
  have hmean : ∀ p : Submodule F (V d) × Submodule F (W n),
      typedUniformMean (fun T : V d →ₗ[F] W n =>
        typedW6QComponent p.1 p.2 T (fun M => (character Y M : ℂ))) =
        if Selected p.1 p.2 Y.transpose.toLin' then 1 else 0 := by
    intro p
    unfold typedUniformMean
    simp_rw [a7_character_qComponent]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpos : 0 < Fintype.card (V d →ₗ[F] W n) :=
      Fintype.card_pos_iff.mpr ⟨0⟩
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.ne_of_gt hpos))
  simp_rw [hmean]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Fintype.card_subtype]

/-- A squared character has mean `1`. -/
theorem a7_character_energy {n d : Nat} (Y : BinaryMatrix n d) :
    uniformMean (fun M => Complex.normSq ((character Y M : ℂ))) = 1 := by
  have hpt : ∀ M, Complex.normSq ((character Y M : ℂ)) = 1 := by
    intro M
    unfold character
    by_cases h : pairing Y M = 0
    · simp [h, Complex.normSq_ofReal]
    · simp [h, Complex.normSq_ofReal]
  simp_rw [hpt]
  exact uniformMean_const 1

/-- Every `a`-plane of the image gives a distinct selected pair. -/
theorem a7_selected_card_ge_grass {n d r a : Nat}
    (Y : W n →ₗ[F] V d)
    (hY : Module.finrank F (LinearMap.range Y) = r) :
    w6Gaussian r a ≤
      Fintype.card {p : Submodule F (V d) × Submodule F (W n) //
        Selected p.1 p.2 Y} := by
  classical
  haveI : Fintype (LinearMap.range Y) := Fintype.ofFinite _
  haveI : Module.Finite F (LinearMap.range Y) := inferInstance
  haveI : Module.Free F (LinearMap.range Y) :=
    Module.Free.of_basis (Module.finBasis F (LinearMap.range Y))
  have hgrass : Fintype.card (W6Grass (LinearMap.range Y) a) =
      w6Gaussian r a := by
    rw [w6_card_grass, hY]
  let emb : W6Grass (LinearMap.range Y) a →
      {p : Submodule F (V d) × Submodule F (W n) // Selected p.1 p.2 Y} :=
    fun A => a7SelectedOfRangeSubspace Y A.1
  have hinj : Function.Injective emb := by
    intro A₁ A₂ h
    exact Subtype.ext (a7SelectedOfRangeSubspace_injective Y h)
  have hle := Fintype.card_le_of_injective emb hinj
  rwa [hgrass] at hle

/-- A rank-38 character has unweighted `Q` larger than `2^{9*40}` times its
squared `L2` energy. The energy is `1`, and `Q` equals the selected-pair
count, which is at least the 19-planes of the image. This is an evaluation
of `a7HybridQ`. It does not identify the character with `a7OutputBinary`,
and it does not remove the share hypothesis. -/
theorem a7_rank38_character_q_exceeds_order_one {n d : Nat}
    (Y : BinaryMatrix n d)
    (hY : Module.finrank F (LinearMap.range Y.transpose.toLin') = 38) :
    (2 : ℝ) ^ (9 * 40) *
        (uniformMean (fun M => Complex.normSq ((character Y M : ℂ)))) ^ 2 <
      a7HybridQ (fun M => (character Y M : ℂ)) := by
  have henergy := a7_character_energy Y
  have hcard := a7_selected_card_ge_grass (a := 19) Y.transpose.toLin' hY
  have hgauss := a7_gaussian_38_19_gt_order_one
  have hnat : 2 ^ (9 * 40) <
      Fintype.card {p : Submodule F (V d) × Submodule F (W n) //
        Selected p.1 p.2 Y.transpose.toLin'} :=
    lt_of_lt_of_le hgauss hcard
  rw [a7_character_hybrid_q, henergy, one_pow, mul_one]
  exact_mod_cast hnat

theorem a7_precedes_zero {n d : Nat} (Y : BinaryMatrix n d) :
    w6Precedes (0 : BinaryMatrix n d) Y := by
  unfold w6Precedes
  simp [Matrix.rank_zero, sub_zero]

theorem a7_zero_filter {n d : Nat} (f : BinaryMatrix n d → Complex) :
    w6PredecessorFilter (0 : BinaryMatrix n d) f = f := by
  funext M
  unfold w6PredecessorFilter
  have hsum : (∑ Y : BinaryMatrix n d,
      if w6Precedes (0 : BinaryMatrix n d) Y then
        complexFourierCoeff f Y * (character Y M : Complex) else 0) =
      ∑ Y : BinaryMatrix n d, complexFourierCoeff f Y * (character Y M : Complex) := by
    refine Finset.sum_congr rfl ?_
    intro Y _
    simp [a7_precedes_zero]
  rw [hsum]
  exact complexFourierInversion f M

theorem a7_zero_derivative_apply {n d : Nat} (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ LinearMap.range ((0 : BinaryMatrix n d).transpose.toLin')) →ₗ[F]
      LinearMap.ker ((0 : BinaryMatrix n d).transpose.toLin')) :
    actualW6Derivative (0 : BinaryMatrix n d) 0 f M =
      f (LinearMap.toMatrix'
        ((LinearMap.ker ((0 : BinaryMatrix n d).transpose.toLin')).subtype.comp
          (M.comp (LinearMap.range
            ((0 : BinaryMatrix n d).transpose.toLin')).mkQ))) := by
  unfold actualW6Derivative complexAmbientAffineRestrict
  rw [a7_zero_filter]
  simp

theorem a7_pairing_trace {n d : Nat} (Y M : BinaryMatrix n d) :
    pairing Y M = (Y.transpose * M).trace := by
  classical
  simp only [pairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Conjugation by a row matrix and a column matrix preserves the trace pairing. -/
theorem a7_pairing_conj {n d : Nat}
    (P : Matrix (Fin n) (Fin n) F) (Q : Matrix (Fin d) (Fin d) F)
    (Z X : BinaryMatrix n d) :
    pairing Z (P * X * Q) = pairing (P.transpose * Z * Q.transpose) X := by
  rw [a7_pairing_trace, a7_pairing_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

def a7BasisVec (i : Fin 40) : V 40 :=
  fun j => if j = i then 1 else 0

theorem a7BasisVec_ne_zero (i : Fin 40) : a7BasisVec i ≠ 0 := by
  intro h
  have hc := congrFun h i
  simp [a7BasisVec] at hc

def a7Line : Submodule F (V 40) := F ∙ a7BasisVec 0

theorem a7Line_finrank : Module.finrank F a7Line = 1 :=
  finrank_span_singleton (a7BasisVec_ne_zero 0)

noncomputable def a7Incl39 : (Fin 39 → F) →ₗ[F] (V 40) where
  toFun v i := if h : i.val < 39 then v ⟨i.val, h⟩ else 0
  map_add' x y := by
    ext i
    by_cases h : i.val < 39 <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : i.val < 39 <;> simp [h]

noncomputable def a7Proj39 : (V 40) →ₗ[F] (Fin 39 → F) :=
  LinearMap.pi fun i : Fin 39 =>
    LinearMap.proj (Fin.castLE (by decide : 39 ≤ 40) i)

theorem a7_proj_incl : a7Proj39.comp a7Incl39 = LinearMap.id := by
  ext v i
  simp [a7Proj39, a7Incl39, LinearMap.pi_apply, Fin.castLE]

/-- A rank-39 coordinate projection on a 40-dimensional binary space. -/
noncomputable def a7Freq40 : (W 40) →ₗ[F] (V 40) :=
  a7Incl39.comp a7Proj39

theorem a7Freq40_rank : Module.finrank F (LinearMap.range a7Freq40) = 39 := by
  have hsurj : Function.Surjective a7Proj39 := by
    intro v
    refine ⟨a7Incl39 v, ?_⟩
    have h := congrFun (congrArg DFunLike.coe a7_proj_incl) v
    simpa [LinearMap.comp_apply] using h
  have hinj : Function.Injective a7Incl39 := by
    intro x y hxy
    ext i
    have hc := congrFun hxy ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    simp [a7Incl39] at hc
    exact hc
  have hrange : LinearMap.range a7Freq40 = LinearMap.range a7Incl39 := by
    unfold a7Freq40
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  rw [hrange, LinearMap.finrank_range_of_inj hinj]
  simpa using (Module.finrank_fin_fun (n := 39) F)

theorem a7Line_le_range : a7Line ≤ LinearMap.range a7Freq40 := by
  rw [a7Line]
  refine Submodule.span_le.mpr ?_
  intro v hv
  have hv' : v = a7BasisVec 0 := by simpa using hv
  rw [hv']
  refine ⟨a7BasisVec 0, ?_⟩
  ext i
  by_cases hi : i.val < 39
  · simp [a7Freq40, a7Incl39, a7Proj39, a7BasisVec, LinearMap.pi_apply,
      Fin.castLE, hi]
  · have hne : i ≠ 0 := by
      intro heq
      have : i.val = 0 := by simp [heq]
      omega
    simp [a7Freq40, a7Incl39, a7Proj39, a7BasisVec, LinearMap.pi_apply, hi, hne]

/-- Quotienting the rank-39 image by the line drops the rank by one. -/
theorem a7_induced_rank :
    Module.finrank F (LinearMap.range (a7Line.mkQ.comp a7Freq40)) = 38 := by
  classical
  let S := LinearMap.range a7Freq40
  let f := a7Line.mkQ.comp S.subtype
  have hle : a7Line ≤ S := a7Line_le_range
  have hrange : LinearMap.range (a7Line.mkQ.comp a7Freq40) = LinearMap.range f := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨⟨a7Freq40 w, LinearMap.mem_range_self _ w⟩, rfl⟩
    · rintro _ ⟨⟨_, hy⟩, rfl⟩
      rcases hy with ⟨w, rfl⟩
      exact ⟨w, rfl⟩
  have hmap : Submodule.map S.subtype (LinearMap.ker f) = a7Line := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hzero : a7Line.mkQ (S.subtype y) = 0 := by
        simpa [f] using hy
      exact (Submodule.Quotient.mk_eq_zero a7Line).mp hzero
    · intro hx
      refine ⟨⟨x, hle hx⟩, ?_, rfl⟩
      simp [f, hx]
  have hkerFin : Module.finrank F (LinearMap.ker f) = 1 := by
    rw [← Submodule.finrank_map_subtype_eq S (LinearMap.ker f), hmap]
    exact a7Line_finrank
  have hadd := LinearMap.finrank_range_add_finrank_ker f
  have hS : Module.finrank F S = 39 := by
    simpa [S] using a7Freq40_rank
  have hsum : Module.finrank F (LinearMap.range f) + 1 = 39 := by
    simpa [hkerFin, hS] using hadd
  rw [hrange]
  omega

/-- The matrix whose transpose realizes `a7Freq40`. -/
noncomputable def a7FreqMatrix : BinaryMatrix 40 40 :=
  (LinearMap.toMatrix' a7Freq40).transpose

theorem a7FreqMatrix_toLin : a7FreqMatrix.transpose.toLin' = a7Freq40 := by
  simp [a7FreqMatrix, Matrix.transpose_transpose, Matrix.toLin'_toMatrix']

theorem a7FreqMatrix_rank : a7FreqMatrix.rank = 39 := by
  rw [← Matrix.rank_transpose, a7FreqMatrix]
  rw [Matrix.transpose_transpose]
  rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix' a7Freq40)
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_toMatrix']
  exact a7Freq40_rank

/-- The character of that rank-39 matrix. -/
def a7Char (M : BinaryMatrix 40 40) : ℂ :=
  (character a7FreqMatrix M : ℂ)

theorem a7Char_supported : ComplexFourierSupportedThrough 40 a7Char := by
  intro Y hY
  have hne : Y ≠ a7FreqMatrix := by
    intro h
    rw [h, a7FreqMatrix_rank] at hY
    omega
  change complexFourierCoeff (fun M => (character a7FreqMatrix M : ℂ)) Y = 0
  rw [complexFourierCoeff_character, if_neg hne]

theorem a7Freq40_selected : Selected a7Line (⊤ : Submodule F (W 40)) a7Freq40 :=
  ⟨a7Line_le_range, fun _ _ => Submodule.mem_top⟩

/-- The zero map on the line, as a positive-order index triple over `(line, ⊤)`. -/
noncomputable def a7OrderOneTriple :
    T1IndexTriple a7Line (⊤ : Submodule F (W 40)) :=
  t1MapToTriple (0 : a7Line →ₗ[F] (W 40 ⧸ (⊤ : Submodule F (W 40))))

theorem a7OrderOne_C : t1AmbientC a7OrderOneTriple.C = a7Line := by
  simp [a7OrderOneTriple, t1MapToTriple, t1AmbientC, LinearMap.ker_zero,
    Submodule.map_top, Submodule.range_subtype]

theorem a7OrderOne_K : a7OrderOneTriple.K = ⊥ := by
  simp [a7OrderOneTriple, t1MapToTriple, LinearMap.range_zero]

theorem a7OrderOne_H : t1AmbientH a7OrderOneTriple.K = ⊤ := by
  rw [a7OrderOne_K]
  ext w
  simp [t1AmbientH, Submodule.mem_comap, Submodule.mem_bot, Submodule.mkQ_apply]

theorem a7OrderOne_Ctop : a7OrderOneTriple.C = ⊤ := by
  simp [a7OrderOneTriple, t1MapToTriple, LinearMap.ker_zero]

/-- The pullback lands in the image of a map out of the zero quotient `line/⊤`,
so its rank is zero. The order is therefore `1`. -/
theorem a7OrderOne_pullback_rank :
    Module.finrank F (LinearMap.range (t1PullbackMap a7OrderOneTriple)) = 0 := by
  have hdom : Module.finrank F (a7Line ⧸ (⊤ : Submodule F a7Line)) = 0 := by
    have hsum := (⊤ : Submodule F a7Line).finrank_quotient_add_finrank
    rw [finrank_top] at hsum
    omega
  have hle : LinearMap.range (t1PullbackMap a7OrderOneTriple) ≤
      LinearMap.range (t1AQuotientToAmbient a7OrderOneTriple.C) := by
    rw [t1PullbackMap]
    exact LinearMap.range_comp_le_range _ _
  have hzero : Module.finrank F
      (LinearMap.range (t1AQuotientToAmbient a7OrderOneTriple.C)) = 0 := by
    rw [a7OrderOne_Ctop]
    exact Nat.eq_zero_of_le_zero
      (by simpa [hdom] using
        (LinearMap.finrank_range_le (t1AQuotientToAmbient (⊤ : Submodule F a7Line))))
  have hinj : Function.Injective (Submodule.inclusion hle) :=
    Submodule.inclusion_injective hle
  exact Nat.eq_zero_of_le_zero
    (by simpa [hzero] using (LinearMap.finrank_le_finrank_of_injective hinj))

theorem a7OrderOne_quot_finrank :
    Module.finrank F (W 40 ⧸ (⊤ : Submodule F (W 40))) = 0 := by
  have hsum := (⊤ : Submodule F (W 40)).finrank_quotient_add_finrank
  rw [finrank_top] at hsum
  omega

theorem a7OrderOne_order : a6Order a7OrderOneTriple = 1 := by
  have hpull : Module.finrank F (LinearMap.range (t1PullbackMap a7OrderOneTriple)) = 0 :=
    a7OrderOne_pullback_rank
  have hC : Module.finrank F (t1AmbientC a7OrderOneTriple.C) = 1 := by
    rw [a7OrderOne_C, a7Line_finrank]
  have hH : Module.finrank F (W 40 ⧸ t1AmbientH a7OrderOneTriple.K) = 0 := by
    rw [a7OrderOne_H, a7OrderOne_quot_finrank]
  unfold a6Order
  rw [hC, hH, hpull]

/-- The original component of this character on the order-one carrier is `1`. -/
theorem a7OrderOne_component :
    typedW6QComponent (t1AmbientC a7OrderOneTriple.C)
      (t1AmbientH a7OrderOneTriple.K) (0 : V 40 →ₗ[F] W 40) a7Char = 1 := by
  rw [a7OrderOne_C, a7OrderOne_H]
  unfold a7Char
  rw [a7_character_qComponent, a7FreqMatrix_toLin, if_pos a7Freq40_selected]

theorem a7OrderOne_pullback_bot : t1PullbackMap a7OrderOneTriple = 0 := by
  have hbot : LinearMap.range (t1PullbackMap a7OrderOneTriple) = ⊥ := by
    refine (Submodule.eq_of_le_of_finrank_eq bot_le ?_).symm
    rw [finrank_bot, a7OrderOne_pullback_rank]
  ext x
  have hmem := LinearMap.mem_range_self (t1PullbackMap a7OrderOneTriple) x
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

theorem a7OrderOne_parent : a7MixedCoordinateParent a7OrderOneTriple = 0 := by
  unfold a7MixedCoordinateParent
  rw [a7OrderOne_pullback_bot, map_zero]

/-- The quotient of the rank-39 map by the line, on the order-one carrier. -/
noncomputable def a7OrderPhi :
    (t1AmbientH a7OrderOneTriple.K) →ₗ[F]
      (V 40 ⧸ t1AmbientC a7OrderOneTriple.C) :=
  (t1AmbientC a7OrderOneTriple.C).mkQ.comp
    (a7Freq40.comp (t1AmbientH a7OrderOneTriple.K).subtype)

theorem a7OrderPhi_rank : Module.finrank F (LinearMap.range a7OrderPhi) = 38 := by
  have hsurj : Function.Surjective (⊤ : Submodule F (W 40)).subtype := by
    intro w
    exact ⟨⟨w, Submodule.mem_top⟩, rfl⟩
  have hinduced : Module.finrank F (LinearMap.range
      (a7Line.mkQ.comp (a7Freq40.comp (⊤ : Submodule F (W 40)).subtype))) = 38 := by
    have hrange : LinearMap.range
        (a7Line.mkQ.comp (a7Freq40.comp (⊤ : Submodule F (W 40)).subtype)) =
        LinearMap.range (a7Line.mkQ.comp a7Freq40) := by
      have hsub : LinearMap.range
          (a7Freq40.comp (⊤ : Submodule F (W 40)).subtype) =
          LinearMap.range a7Freq40 := by
        rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
      rw [LinearMap.range_comp, hsub, ← LinearMap.range_comp]
    rw [hrange, a7_induced_rank]
  unfold a7OrderPhi
  rw [a7OrderOne_C, a7OrderOne_H]
  exact hinduced

noncomputable def a7OrderMatrix :=
  carrierFrequencyEquiv (t1AmbientC a7OrderOneTriple.C)
    (t1AmbientH a7OrderOneTriple.K) a7OrderPhi

theorem a7OrderMatrix_rank : a7OrderMatrix.rank = 38 := by
  rw [a7OrderMatrix, carrierFrequency_rank, a7OrderPhi_rank]

/-- Characters agree when their trace pairings agree. -/
theorem a7_character_of_pairing {n d : Nat} {Y Z : BinaryMatrix n d}
    (h : ∀ M, pairing Y M = pairing Z M) :
    (fun M => (character Y M : ℂ)) = fun M => (character Z M : ℂ) := by
  funext M
  simp [character, h M]

theorem a7_character_conj {n d : Nat}
    (P : Matrix (Fin n) (Fin n) F) (Q : Matrix (Fin d) (Fin d) F)
    (Z : BinaryMatrix n d) :
    (fun X => (character Z (P * X * Q) : ℂ)) =
      fun X => (character (P.transpose * Z * Q.transpose) X : ℂ) := by
  funext X
  have h := a7_pairing_conj P Q Z X
  simp [character, h]

/-- Rectangular row and column factors obey the same trace identity. -/
theorem a7_pairing_conj_rect {n n' d d' : Nat}
    (P : Matrix (Fin n) (Fin n') F) (Q : Matrix (Fin d') (Fin d) F)
    (Z : BinaryMatrix n d) (X : BinaryMatrix n' d') :
    pairing Z (P * X * Q) = pairing (P.transpose * Z * Q.transpose) X := by
  rw [a7_pairing_trace, a7_pairing_trace]
  have hright : (P.transpose * Z * Q.transpose).transpose * X =
      Q * Z.transpose * P * X := by
    simp [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hright]
  have hleft : Z.transpose * (P * X * Q) = Z.transpose * P * X * Q := by
    simp [Matrix.mul_assoc]
  rw [hleft]
  have hcycle : (Z.transpose * P * X * Q).trace =
      (Q * (Z.transpose * P * X)).trace := by
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (Z.transpose * P * X) Q)
  rw [hcycle]
  simp [Matrix.mul_assoc]

theorem a7_character_conj_rect {n n' d d' : Nat}
    (P : Matrix (Fin n) (Fin n') F) (Q : Matrix (Fin d') (Fin d) F)
    (Z : BinaryMatrix n d) :
    (fun X : BinaryMatrix n' d' => (character Z (P * X * Q) : ℂ)) =
      fun X => (character (P.transpose * Z * Q.transpose) X : ℂ) := by
  funext X
  have h := a7_pairing_conj_rect P Q Z X
  simp [character, h]

/-- Matrix rank is the dimension of the image of the transposed standard map. -/
theorem a7_transpose_finrank {n d : Nat} (Y : BinaryMatrix n d) :
    Module.finrank F (LinearMap.range Y.transpose.toLin') = Y.rank := by
  rw [← Matrix.rank_transpose]
  rw [Matrix.rank_eq_finrank_range_toLin Y.transpose
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin']

/-- The mixed coordinate of the order-one character is the rank-38 quotient
character. This is the carrier reading, before the zero-parent derivative. -/
theorem a7OrderOne_mixed_character :
    a7MixedCoordinate a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char =
      fun K => (character a7OrderMatrix K : ℂ) := by
  funext K
  unfold a7MixedCoordinate a7OrderMatrix a7OrderPhi
  rw [show a7Char = fun M => (character a7FreqMatrix M : ℂ) from rfl]
  have hsel : Selected (t1AmbientC a7OrderOneTriple.C)
      (t1AmbientH a7OrderOneTriple.K) a7Freq40 := by
    rw [a7OrderOne_C, a7OrderOne_H]
    exact a7Freq40_selected
  rw [filteredCarrierFunction_character, a7FreqMatrix_toLin, if_pos hsel]
  have hphase : traceCharacter a7Freq40 (0 : V 40 →ₗ[F] W 40) = 1 := by
    unfold traceCharacter tracePair
    simp
  rw [hphase, one_mul]
  have htrace := carrierFrequency_tracePair
    (t1AmbientC a7OrderOneTriple.C) (t1AmbientH a7OrderOneTriple.K)
    ((t1AmbientC a7OrderOneTriple.C).mkQ.comp
      (a7Freq40.comp (t1AmbientH a7OrderOneTriple.K).subtype))
    ((carrierMatrixEquiv (t1AmbientC a7OrderOneTriple.C)
      (t1AmbientH a7OrderOneTriple.K)).symm K)
  simp [traceCharacter, character, htrace]

/-- The zero parent's transpose is the zero map, so its kernel is the whole
output coordinate space. -/
theorem a7OrderOne_output_ker :
    LinearMap.ker (a7MixedCoordinateParent a7OrderOneTriple).transpose.toLin' = ⊤ := by
  rw [a7OrderOne_parent]
  refine le_antisymm le_top ?_
  intro w _
  rw [LinearMap.mem_ker]
  simp [Matrix.transpose_zero]

/-- The zero parent's transpose is the zero map, so its range is zero. -/
theorem a7OrderOne_output_range :
    LinearMap.range (a7MixedCoordinateParent a7OrderOneTriple).transpose.toLin' = ⊥ := by
  rw [a7OrderOne_parent]
  rw [LinearMap.range_eq_bot]
  ext w
  simp [Matrix.transpose_zero]

abbrev a7OrderCout :=
  LinearMap.range (a7MixedCoordinateParent a7OrderOneTriple).transpose.toLin'

abbrev a7OrderHout :=
  LinearMap.ker (a7MixedCoordinateParent a7OrderOneTriple).transpose.toLin'

theorem a7OrderCout_bot : a7OrderCout = ⊥ := by
  unfold a7OrderCout
  exact a7OrderOne_output_range

theorem a7OrderHout_top : a7OrderHout = ⊤ := by
  unfold a7OrderHout
  exact a7OrderOne_output_ker

/-- The zero parent makes the output the mixed character read on the standard
matrix of the derivative carrier. -/
theorem a7OrderOne_output_eval :
    a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char =
      fun X =>
        a7MixedCoordinate a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char
          (LinearMap.toMatrix'
            (a7OrderHout.subtype.comp
              (((carrierMatrixEquiv a7OrderCout a7OrderHout).symm X).comp
                a7OrderCout.mkQ))) := by
  funext X
  simp only [a7OutputBinary]
  unfold actualW6Derivative complexAmbientAffineRestrict
  have hfilter :
      w6PredecessorFilter (a7MixedCoordinateParent a7OrderOneTriple)
        (a7MixedCoordinate a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) =
      a7MixedCoordinate a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char := by
    rw [a7OrderOne_parent]
    exact a7_zero_filter _
  rw [hfilter]
  simp only [zero_add]

def a7OrderIsoL :=
  a7OrderHout.subtype.comp (codomainBasis a7OrderHout).equivFun.symm.toLinearMap

def a7OrderIsoR :=
  (domainBasis a7OrderCout).equivFun.toLinearMap.comp a7OrderCout.mkQ

/-- The rank-38 quotient character, conjugated onto the zero-parent output
coordinates. The factors are the fixed bases of that output carrier. -/
def a7OrderOneOutputMatrix :=
  (LinearMap.toMatrix' a7OrderIsoL).transpose * a7OrderMatrix *
    (LinearMap.toMatrix' a7OrderIsoR).transpose

/-- The order-one output is the character of that conjugated matrix. -/
theorem a7OrderOne_output_character :
    a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char =
      fun X => (character a7OrderOneOutputMatrix X : ℂ) := by
  funext X
  rw [congrFun a7OrderOne_output_eval X, a7OrderOne_mixed_character]
  let M := (carrierMatrixEquiv a7OrderCout a7OrderHout).symm X
  have hlin := carrierMatrix_toLin a7OrderCout a7OrderHout M
  have hXM : carrierMatrixEquiv a7OrderCout a7OrderHout M = X :=
    (carrierMatrixEquiv a7OrderCout a7OrderHout).apply_symm_apply X
  rw [hXM] at hlin
  have hM : M =
      (codomainBasis a7OrderHout).equivFun.symm.toLinearMap.comp
        (X.toLin'.comp (domainBasis a7OrderCout).equivFun.toLinearMap) := by
    refine LinearMap.ext ?_
    intro v
    have hpt := congrFun (congrArg DFunLike.coe hlin)
      ((domainBasis a7OrderCout).equivFun v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] at hpt
    exact ((LinearEquiv.symm_apply_eq
      ((codomainBasis a7OrderHout).equivFun)).mpr hpt).symm
  have hmap : a7OrderHout.subtype.comp (M.comp a7OrderCout.mkQ) =
      a7OrderIsoL.comp (X.toLin'.comp a7OrderIsoR) := by
    rw [hM]
    refine LinearMap.ext ?_
    intro v
    simp only [a7OrderIsoL, a7OrderIsoR, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap]
  have hmat : LinearMap.toMatrix'
      (a7OrderHout.subtype.comp
        (((carrierMatrixEquiv a7OrderCout a7OrderHout).symm X).comp
          a7OrderCout.mkQ)) =
      LinearMap.toMatrix' a7OrderIsoL * X * LinearMap.toMatrix' a7OrderIsoR := by
    have hMeq : (carrierMatrixEquiv a7OrderCout a7OrderHout).symm X = M := rfl
    rw [hMeq, hmap]
    rw [LinearMap.toMatrix'_comp]
    rw [LinearMap.toMatrix'_comp]
    rw [LinearMap.toMatrix'_toLin']
    rw [← Matrix.mul_assoc]
  rw [hmat]
  unfold a7OrderOneOutputMatrix
  exact congrFun (a7_character_conj_rect (LinearMap.toMatrix' a7OrderIsoL)
    (LinearMap.toMatrix' a7OrderIsoR) a7OrderMatrix) X

/-- Conjugation by the output-carrier bases preserves rank 38. -/
theorem a7OrderOneOutputMatrix_rank :
    Module.finrank F (LinearMap.range a7OrderOneOutputMatrix.transpose.toLin') = 38 := by
  have hsubSurj : Function.Surjective a7OrderHout.subtype := by
    intro w
    have hw : w ∈ a7OrderHout := by
      unfold a7OrderHout
      rw [a7OrderOne_output_ker]
      exact Submodule.mem_top
    exact ⟨⟨w, hw⟩, rfl⟩
  have hbijL : Function.Bijective a7OrderIsoL := by
    have hcomp : a7OrderIsoL =
        a7OrderHout.subtype.comp
          (codomainBasis a7OrderHout).equivFun.symm.toLinearMap := by
      unfold a7OrderIsoL
      rfl
    rw [hcomp, LinearMap.coe_comp]
    exact Function.Bijective.comp
      ⟨Submodule.injective_subtype a7OrderHout, hsubSurj⟩
      (codomainBasis a7OrderHout).equivFun.symm.bijective
  have hinjQ : Function.Injective a7OrderCout.mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
    exact a7OrderCout_bot
  have hsurjQ : Function.Surjective a7OrderCout.mkQ := by
    intro z
    obtain ⟨v, hv⟩ := Quotient.exists_rep z
    refine ⟨v, ?_⟩
    rw [Submodule.mkQ_apply]
    exact hv
  have hbijR : Function.Bijective a7OrderIsoR := by
    have hcomp : a7OrderIsoR =
        (domainBasis a7OrderCout).equivFun.toLinearMap.comp a7OrderCout.mkQ := by
      unfold a7OrderIsoR
      rfl
    rw [hcomp, LinearMap.coe_comp]
    exact Function.Bijective.comp
      (domainBasis a7OrderCout).equivFun.bijective
      ⟨hinjQ, hsurjQ⟩
  let eL := LinearEquiv.ofBijective a7OrderIsoL hbijL
  let eR := LinearEquiv.ofBijective a7OrderIsoR hbijR
  have hEL : eL.toLinearMap = a7OrderIsoL := by
    ext x
    simp [eL, LinearEquiv.ofBijective_apply]
  have hER : eR.toLinearMap = a7OrderIsoR := by
    ext x
    simp [eR, LinearEquiv.ofBijective_apply]
  have hYt : a7OrderOneOutputMatrix.transpose =
      LinearMap.toMatrix' a7OrderIsoR * a7OrderMatrix.transpose *
        LinearMap.toMatrix' a7OrderIsoL := by
    unfold a7OrderOneOutputMatrix
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hto : a7OrderOneOutputMatrix.transpose.toLin' =
      eR.toLinearMap.comp
        (a7OrderMatrix.transpose.toLin'.comp eL.toLinearMap) := by
    rw [hEL, hER, hYt, Matrix.toLin'_mul, Matrix.toLin'_mul]
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    rw [LinearMap.comp_assoc]
  have hsurjL : Function.Surjective eL.toLinearMap := eL.surjective
  have hmid : LinearMap.range
      (a7OrderMatrix.transpose.toLin'.comp eL.toLinearMap) =
      LinearMap.range a7OrderMatrix.transpose.toLin' := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurjL, Submodule.map_top]
  have hr : LinearMap.range a7OrderOneOutputMatrix.transpose.toLin' =
      Submodule.map eR.toLinearMap
        (LinearMap.range a7OrderMatrix.transpose.toLin') := by
    rw [hto, LinearMap.range_comp, hmid]
  rw [hr, LinearEquiv.finrank_map_eq eR, a7_transpose_finrank, a7OrderMatrix_rank]

/-- One original component does not absorb the order-one output. The output
is a rank-38 character, its original component is `1`, and its unweighted `Q`
is strictly larger than `2^{9*40*order}` times that component. The share
hypothesis stays. -/
theorem a7OrderOne_output_q_exceeds_component :
    (2 : ℝ) ^ (9 * 40 * a6Order a7OrderOneTriple) *
      typedW6QComponent (t1AmbientC a7OrderOneTriple.C)
        (t1AmbientH a7OrderOneTriple.K) (0 : V 40 →ₗ[F] W 40) a7Char <
    a7HybridQ (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) := by
  have h := a7_rank38_character_q_exceeds_order_one a7OrderOneOutputMatrix
    a7OrderOneOutputMatrix_rank
  rw [a7_character_energy a7OrderOneOutputMatrix, one_pow, mul_one] at h
  rw [a7OrderOne_order, Nat.mul_one, a7OrderOne_component, mul_one,
    a7OrderOne_output_character]
  exact h

/-- Every frequency is selected by the zero-order pair `(⊥, ⊤)`. -/
theorem a7_bot_top_selected {n d : Nat} (Y : W n →ₗ[F] V d) :
    Selected (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) Y :=
  ⟨bot_le, fun _ _ => Submodule.mem_top⟩

/-- One subspace pair contributes `1` or `0` to the pair share of a character. -/
theorem a7_character_pair_share {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) (Y : BinaryMatrix n d) :
    a7PairShare A B (fun M => (character Y M : ℂ)) =
      if Selected A B Y.transpose.toLin' then 1 else 0 := by
  classical
  unfold a7PairShare typedUniformMean
  simp_rw [a7_character_qComponent]
  by_cases hsel : Selected A B Y.transpose.toLin'
  · simp only [hsel, if_pos]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpos : 0 < Fintype.card (V d →ₗ[F] W n) :=
      Fintype.card_pos_iff.mpr ⟨0⟩
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.ne_of_gt hpos))
  · simp [hsel, Finset.sum_const_zero, zero_div]

/-- The zero-order output term of the order-one triple is `1`. -/
theorem a7OrderOne_zero_output_share_eq_one :
    a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
      (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) = 1 := by
  rw [a7OrderOne_output_character, a7_character_pair_share,
    if_pos (a7_bot_top_selected _)]

/-- That one output term lands in the original component. The factor is the
room already proved for the zero-order output share. -/
theorem a7OrderOne_zero_output_share_lands :
    a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
      (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) ≤
      (2 : ℝ) ^ (9 * 40 * a6Order a7OrderOneTriple) *
        typedW6QComponent (t1AmbientC a7OrderOneTriple.C)
          (t1AmbientH a7OrderOneTriple.K) (0 : V 40 →ₗ[F] W 40) a7Char :=
  a7_output_zero_share_le_original_component a7OrderOneTriple
    (0 : V 40 →ₗ[F] W 40) a7Char a7Char_supported
    (by rw [a7OrderOne_order]; decide)

/-- After that zero-order term is paid, the other output terms still exceed
what the same original component has left. Those terms are not injected.
The share hypothesis stays. -/
theorem a7OrderOne_remaining_output_exceeds_leftover :
    a7HybridQ (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) -
        a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
          (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) >
      (2 : ℝ) ^ (9 * 40 * a6Order a7OrderOneTriple) *
        typedW6QComponent (t1AmbientC a7OrderOneTriple.C)
          (t1AmbientH a7OrderOneTriple.K) (0 : V 40 →ₗ[F] W 40) a7Char -
        a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
          (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) :=
  sub_lt_sub_right a7OrderOne_output_q_exceeds_component _

/-- Equal submodules are the same module. The underlying vector is unchanged. -/
noncomputable def a7SubCast {M : Type*} [AddCommGroup M] [Module F M]
    {A B : Submodule F M} (h : A = B) : A ≃ₗ[F] B :=
  LinearEquiv.ofLinear
    (Submodule.inclusion (le_of_eq h))
    (Submodule.inclusion (le_of_eq h.symm))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [LinearMap.comp_apply, Submodule.inclusion_apply, Submodule.inclusion_apply]
      simp)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [LinearMap.comp_apply, Submodule.inclusion_apply, Submodule.inclusion_apply]
      simp)

/-- Conjugation by linear equivalences preserves hybrid selection. -/
theorem a7_selected_conj_iff
    {D C D' C' : Type*}
    [AddCommGroup D] [Module F D] [AddCommGroup C] [Module F C]
    [AddCommGroup D'] [Module F D'] [AddCommGroup C'] [Module F C']
    (eD : D ≃ₗ[F] D') (eC : C ≃ₗ[F] C')
    (Y : D →ₗ[F] C) (A : Submodule F C) (B : Submodule F D) :
    Selected (A.map eC.toLinearMap) (B.map eD.toLinearMap)
        (eC.toLinearMap.comp (Y.comp eD.symm.toLinearMap)) ↔
      Selected A B Y := by
  let Z := eC.toLinearMap.comp (Y.comp eD.symm.toLinearMap)
  constructor
  · intro h
    constructor
    · intro a ha
      have hmem : eC a ∈ LinearMap.range Z :=
        h.1 (Submodule.mem_map_of_mem ha)
      rcases hmem with ⟨w', hw'⟩
      have ha' : Y (eD.symm w') = a := by
        apply eC.injective
        simpa [Z, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hw'
      exact ⟨eD.symm w', ha'⟩
    · intro w hw
      have hZw : Z (eD w) ∈ A.map eC.toLinearMap := by
        refine ⟨Y w, hw, ?_⟩
        simp [Z, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.apply_symm_apply]
      rcases Submodule.mem_map.mp (h.2 (eD w) hZw) with ⟨b, hb, hbval⟩
      have hbEq : b = w := by
        apply eD.injective
        simpa [LinearEquiv.coe_toLinearMap] using hbval
      exact hbEq ▸ hb
  · intro h
    constructor
    · intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      rcases h.1 ha with ⟨w, hw⟩
      refine ⟨eD w, ?_⟩
      simp [Z, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hw]
    · intro w' hw'
      rcases Submodule.mem_map.mp hw' with ⟨a, ha, heq⟩
      have hYa : Y (eD.symm w') = a := by
        apply eC.injective
        simpa [Z, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using heq.symm
      have hw : eD.symm w' ∈ B := h.2 (eD.symm w') (by
        rw [hYa]
        exact ha)
      exact Submodule.mem_map.mpr ⟨eD.symm w', hw, by
        simp [LinearEquiv.coe_toLinearMap]⟩

private theorem a7_map_symm_map
    {D D' : Type*} [AddCommGroup D] [Module F D]
    [AddCommGroup D'] [Module F D']
    (e : D ≃ₗ[F] D') (B : Submodule F D) :
    (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
  rw [← Submodule.map_comp]
  have hid : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp [LinearEquiv.coe_toLinearMap]
  rw [hid, Submodule.map_id]

private theorem a7_map_map_symm
    {D D' : Type*} [AddCommGroup D] [Module F D]
    [AddCommGroup D'] [Module F D']
    (e : D ≃ₗ[F] D') (B : Submodule F D') :
    (B.map e.symm.toLinearMap).map e.toLinearMap = B := by
  rw [← Submodule.map_comp]
  have hid : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp [LinearEquiv.coe_toLinearMap]
  rw [hid, Submodule.map_id]

/-- Selected pairs travel with the conjugated map, in both directions. -/
noncomputable def a7SelectedTransport
    {D C D' C' : Type*}
    [AddCommGroup D] [Module F D] [AddCommGroup C] [Module F C]
    [AddCommGroup D'] [Module F D'] [AddCommGroup C'] [Module F C']
    (eD : D ≃ₗ[F] D') (eC : C ≃ₗ[F] C') (Y : D →ₗ[F] C) :
    {p : Submodule F C × Submodule F D // Selected p.1 p.2 Y} ≃
      {p : Submodule F C' × Submodule F D' //
        Selected p.1 p.2
          (eC.toLinearMap.comp (Y.comp eD.symm.toLinearMap))} where
  toFun p := ⟨(p.1.1.map eC.toLinearMap, p.1.2.map eD.toLinearMap),
    (a7_selected_conj_iff eD eC Y p.1.1 p.1.2).2 p.2⟩
  invFun p := ⟨(p.1.1.map eC.symm.toLinearMap, p.1.2.map eD.symm.toLinearMap), by
    have himgA : (p.1.1.map eC.symm.toLinearMap).map eC.toLinearMap = p.1.1 :=
      a7_map_map_symm eC p.1.1
    have himgB : (p.1.2.map eD.symm.toLinearMap).map eD.toLinearMap = p.1.2 :=
      a7_map_map_symm eD p.1.2
    have hsel :=
      (a7_selected_conj_iff eD eC Y
        (p.1.1.map eC.symm.toLinearMap) (p.1.2.map eD.symm.toLinearMap)).1
        (by
          rw [himgA, himgB]
          exact p.2)
    exact hsel⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact a7_map_symm_map eC p.1.1
    · exact a7_map_symm_map eD p.1.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact a7_map_map_symm eC p.1.1
    · exact a7_map_map_symm eD p.1.2

private noncomputable def a7NestedLift {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (hsel : Selected A₂ B₂ Y)
    (p : {p : Submodule F (V d ⧸ A₂) × Submodule F B₂ //
        Selected p.1 p.2 (induced A₂ B₂ Y)}) :
    {p : {q : Submodule F (V d) × Submodule F (W n) //
        A₂ ≤ q.1 ∧ q.2 ≤ B₂} //
      Selected p.1.1 p.1.2 Y} :=
  let A₁ := Submodule.comap A₂.mkQ p.1.1
  let B₁ := Submodule.map B₂.subtype p.1.2
  let hA : A₂ ≤ A₁ := by
    intro a ha
    rw [Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero A₂).mpr ha]
    exact p.1.1.zero_mem
  let hB : B₁ ≤ B₂ := by
    intro x hx
    rcases hx with ⟨b, -, rfl⟩
    exact b.2
  let hAmap : A₁.map A₂.mkQ = p.1.1 :=
    Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)
  let hBcom : B₁.comap B₂.subtype = p.1.2 :=
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype B₂) p.1.2
  have hinduced : Selected (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
      (induced A₂ B₂ Y) := by
    rw [hAmap, hBcom]
    exact p.2
  ⟨⟨(A₁, B₁), hA, hB⟩,
    (selected_nested_iff A₂ A₁ B₁ B₂ hA hB Y).2 ⟨hsel, hinduced⟩⟩

private noncomputable def a7NestedDrop {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (p : {p : {q : Submodule F (V d) × Submodule F (W n) //
        A₂ ≤ q.1 ∧ q.2 ≤ B₂} //
      Selected p.1.1 p.1.2 Y}) :
    {p : Submodule F (V d ⧸ A₂) × Submodule F B₂ //
        Selected p.1 p.2 (induced A₂ B₂ Y)} :=
  ⟨(p.1.1.1.map A₂.mkQ, p.1.1.2.comap B₂.subtype),
    ((selected_nested_iff A₂ p.1.1.1 p.1.1.2 B₂ p.1.2.1 p.1.2.2 Y).1 p.2).2⟩

private theorem a7NestedDrop_lift {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (hsel : Selected A₂ B₂ Y)
    (p : {p : Submodule F (V d ⧸ A₂) × Submodule F B₂ //
        Selected p.1 p.2 (induced A₂ B₂ Y)}) :
    a7NestedDrop A₂ B₂ Y (a7NestedLift A₂ B₂ Y hsel p) = p := by
  unfold a7NestedLift a7NestedDrop
  dsimp
  apply Subtype.ext
  apply Prod.ext
  · exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)
  · exact Submodule.comap_map_eq_of_injective
      (Submodule.injective_subtype B₂) p.1.2

private theorem a7NestedLift_drop {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (hsel : Selected A₂ B₂ Y)
    (p : {p : {q : Submodule F (V d) × Submodule F (W n) //
        A₂ ≤ q.1 ∧ q.2 ≤ B₂} //
      Selected p.1.1 p.1.2 Y}) :
    a7NestedLift A₂ B₂ Y hsel (a7NestedDrop A₂ B₂ Y p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · show Submodule.comap A₂.mkQ (p.1.1.1.map A₂.mkQ) = p.1.1.1
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ]
    exact sup_eq_left.mpr p.1.2.1
  · show Submodule.map B₂.subtype (p.1.1.2.comap B₂.subtype) = p.1.1.2
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_subtype]
      exact p.1.2.2)

/-- A selected induced pair is one original pair above the carrier. -/
noncomputable def a7NestedSelectedEquiv {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (hsel : Selected A₂ B₂ Y) :
    {p : Submodule F (V d ⧸ A₂) × Submodule F B₂ //
        Selected p.1 p.2 (induced A₂ B₂ Y)} ≃
      {p : {q : Submodule F (V d) × Submodule F (W n) //
          A₂ ≤ q.1 ∧ q.2 ≤ B₂} //
        Selected p.1.1 p.1.2 Y} where
  toFun := a7NestedLift A₂ B₂ Y hsel
  invFun := a7NestedDrop A₂ B₂ Y
  left_inv := a7NestedDrop_lift A₂ B₂ Y hsel
  right_inv := a7NestedLift_drop A₂ B₂ Y hsel

/-- Nested original pair shares of one character equal the number of selected
induced pairs. Each selected induced pair lands in one original pair, and the
zero-order carrier pair is the outer pair itself. -/
theorem a7_character_nested_share_eq {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : BinaryMatrix n d)
    (hsel : Selected A₂ B₂ Y.transpose.toLin') :
    (∑ p : {q : Submodule F (V d) × Submodule F (W n) //
        A₂ ≤ q.1 ∧ q.2 ≤ B₂},
      a7PairShare p.1.1 p.1.2 (fun M => (character Y M : ℂ))) =
      (Fintype.card {p : Submodule F (V d ⧸ A₂) × Submodule F B₂ //
        Selected p.1 p.2 (induced A₂ B₂ Y.transpose.toLin')} : ℝ) := by
  classical
  let nested := {q : Submodule F (V d) × Submodule F (W n) //
    A₂ ≤ q.1 ∧ q.2 ≤ B₂}
  let inducedSel := {p : Submodule F (V d ⧸ A₂) × Submodule F B₂ //
    Selected p.1 p.2 (induced A₂ B₂ Y.transpose.toLin')}
  let nestedSel := {p : nested // Selected p.1.1 p.1.2 Y.transpose.toLin'}
  have hpair : ∀ p : nested,
      a7PairShare p.1.1 p.1.2 (fun M => (character Y M : ℂ)) =
        if Selected p.1.1 p.1.2 Y.transpose.toLin' then 1 else 0 :=
    fun p => a7_character_pair_share p.1.1 p.1.2 Y
  simp_rw [hpair]
  have hsum : (∑ p : nested,
      if Selected p.1.1 p.1.2 Y.transpose.toLin' then (1 : ℝ) else 0) =
      (Fintype.card nestedSel : ℝ) := by
    have hfilter := Finset.sum_filter (s := Finset.univ)
      (p := fun p : nested => Selected p.1.1 p.1.2 Y.transpose.toLin')
      (f := fun _ => (1 : ℝ))
    rw [← hfilter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact congrArg (fun n : Nat => (n : ℝ))
      (Fintype.card_subtype
        (fun p : nested => Selected p.1.1 p.1.2 Y.transpose.toLin')).symm
  have hcard : Fintype.card nestedSel = Fintype.card inducedSel :=
    Fintype.card_congr (a7NestedSelectedEquiv A₂ B₂ Y.transpose.toLin' hsel).symm
  rw [hsum, hcard]

/-- Those nested shares are a subset of the original pair shares, so their sum
is at most the character's unweighted `Q`. -/
theorem a7_character_nested_share_le_q {n d : Nat}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (Y : BinaryMatrix n d) :
    (∑ p : {q : Submodule F (V d) × Submodule F (W n) //
        A₂ ≤ q.1 ∧ q.2 ≤ B₂},
      a7PairShare p.1.1 p.1.2 (fun M => (character Y M : ℂ))) ≤
      a7HybridQ (fun M => (character Y M : ℂ)) := by
  classical
  let nested := {q : Submodule F (V d) × Submodule F (W n) //
    A₂ ≤ q.1 ∧ q.2 ≤ B₂}
  let ambient := Submodule F (V d) × Submodule F (W n)
  let emb : nested → ambient := fun p => p.1
  have hinj : ∀ x ∈ (Finset.univ : Finset nested),
      ∀ y ∈ (Finset.univ : Finset nested), emb x = emb y → x = y := by
    intro x _ y _ h
    exact Subtype.ext h
  have himage : (∑ p : nested,
      a7PairShare (emb p).1 (emb p).2 (fun M => (character Y M : ℂ))) =
      ∑ q ∈ (Finset.univ : Finset nested).image emb,
        a7PairShare q.1 q.2 (fun M => (character Y M : ℂ)) := by
    symm
    exact Finset.sum_image hinj
  have hsub : (Finset.univ : Finset nested).image emb ⊆ Finset.univ :=
    Finset.subset_univ _
  have hnn : ∀ q : ambient, q ∈ Finset.univ →
      q ∉ (Finset.univ : Finset nested).image emb →
      0 ≤ a7PairShare q.1 q.2 (fun M => (character Y M : ℂ)) := by
    intro q _ _
    exact a7_pair_share_nonneg q.1 q.2 _
  have hle : (∑ q ∈ (Finset.univ : Finset nested).image emb,
      a7PairShare q.1 q.2 (fun M => (character Y M : ℂ))) ≤
      ∑ q : ambient, a7PairShare q.1 q.2 (fun M => (character Y M : ℂ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hexh := a7_pair_shares_exhaust (fun M => (character Y M : ℂ))
  have hemb : ∀ p : nested, a7PairShare (emb p).1 (emb p).2
      (fun M => (character Y M : ℂ)) =
      a7PairShare p.1.1 p.1.2 (fun M => (character Y M : ℂ)) :=
    fun _ => rfl
  simp_rw [hemb] at himage
  rw [himage]
  exact hle.trans (le_of_eq hexh)

theorem a7OrderIsoL_bijective : Function.Bijective a7OrderIsoL := by
  have hsubSurj : Function.Surjective a7OrderHout.subtype := by
    intro w
    have hw : w ∈ a7OrderHout := by
      unfold a7OrderHout
      rw [a7OrderOne_output_ker]
      exact Submodule.mem_top
    exact ⟨⟨w, hw⟩, rfl⟩
  have hcomp : a7OrderIsoL =
      a7OrderHout.subtype.comp
        (codomainBasis a7OrderHout).equivFun.symm.toLinearMap := by
    unfold a7OrderIsoL
    rfl
  rw [hcomp, LinearMap.coe_comp]
  exact Function.Bijective.comp
    ⟨Submodule.injective_subtype a7OrderHout, hsubSurj⟩
    (codomainBasis a7OrderHout).equivFun.symm.bijective

theorem a7OrderIsoR_bijective : Function.Bijective a7OrderIsoR := by
  have hinjQ : Function.Injective a7OrderCout.mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
    exact a7OrderCout_bot
  have hsurjQ : Function.Surjective a7OrderCout.mkQ := by
    intro z
    obtain ⟨v, hv⟩ := Quotient.exists_rep z
    refine ⟨v, ?_⟩
    rw [Submodule.mkQ_apply]
    exact hv
  have hcomp : a7OrderIsoR =
      (domainBasis a7OrderCout).equivFun.toLinearMap.comp a7OrderCout.mkQ := by
    unfold a7OrderIsoR
    rfl
  rw [hcomp, LinearMap.coe_comp]
  exact Function.Bijective.comp
    (domainBasis a7OrderCout).equivFun.bijective
    ⟨hinjQ, hsurjQ⟩

/-- The output character is the rank-38 quotient map read through the output
carrier bases. -/
theorem a7OrderOne_output_toLin :
    a7OrderOneOutputMatrix.transpose.toLin' =
      (LinearEquiv.ofBijective a7OrderIsoR a7OrderIsoR_bijective).toLinearMap.comp
        (a7OrderMatrix.transpose.toLin'.comp
          (LinearEquiv.ofBijective a7OrderIsoL a7OrderIsoL_bijective).toLinearMap) := by
  let eL := LinearEquiv.ofBijective a7OrderIsoL a7OrderIsoL_bijective
  let eR := LinearEquiv.ofBijective a7OrderIsoR a7OrderIsoR_bijective
  have hEL : eL.toLinearMap = a7OrderIsoL := by
    ext x
    simp [eL, LinearEquiv.ofBijective_apply]
  have hER : eR.toLinearMap = a7OrderIsoR := by
    ext x
    simp [eR, LinearEquiv.ofBijective_apply]
  have hYt : a7OrderOneOutputMatrix.transpose =
      LinearMap.toMatrix' a7OrderIsoR * a7OrderMatrix.transpose *
        LinearMap.toMatrix' a7OrderIsoL := by
    unfold a7OrderOneOutputMatrix
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hEL, hER, hYt, Matrix.toLin'_mul, Matrix.toLin'_mul]
  rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  rw [LinearMap.comp_assoc]

/-- Equal maps have the same number of selected pairs. The cast does not
unfold the maps. -/
private theorem a7_selected_card_eq
    {D C : Type*} [AddCommGroup D] [Module F D] [AddCommGroup C] [Module F C]
    {Y Z : D →ₗ[F] C} (h : Y = Z)
    [Fintype {p : Submodule F C × Submodule F D // Selected p.1 p.2 Y}]
    [Fintype {p : Submodule F C × Submodule F D // Selected p.1 p.2 Z}] :
    Fintype.card {p : Submodule F C × Submodule F D // Selected p.1 p.2 Y} =
      Fintype.card {p : Submodule F C × Submodule F D // Selected p.1 p.2 Z} :=
  Fintype.card_congr (Equiv.cast (congrArg
    (fun f : D →ₗ[F] C =>
      {p : Submodule F C × Submodule F D // Selected p.1 p.2 f}) h))

/-- The order-one quotient map is the induced frequency of the rank-39
character on `(line, ⊤)`. -/
theorem a7OrderPhi_eq_induced_conj :
    (Submodule.quotEquivOfEq (t1AmbientC a7OrderOneTriple.C) a7Line
        a7OrderOne_C).toLinearMap.comp
      (a7OrderPhi.comp (a7SubCast a7OrderOne_H).symm.toLinearMap) =
      induced a7Line (⊤ : Submodule F (W 40)) a7Freq40 := by
  let C := t1AmbientC a7OrderOneTriple.C
  let H := t1AmbientH a7OrderOneTriple.K
  let eH : H ≃ₗ[F] (⊤ : Submodule F (W 40)) := a7SubCast a7OrderOne_H
  let eQ : (V 40 ⧸ C) ≃ₗ[F] (V 40 ⧸ a7Line) :=
    Submodule.quotEquivOfEq C a7Line a7OrderOne_C
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have hvec : (H.subtype (eH.symm w) : W 40) = w.1 := by
    change (eH.symm w).1 = w.1
    simp [eH, a7SubCast, LinearEquiv.symm_apply_eq, Submodule.inclusion_apply]
  unfold a7OrderPhi induced
  simp only [LinearMap.comp_apply]
  rw [hvec]
  have hsub : ((⊤ : Submodule F (W 40)).subtype w : W 40) = w.1 := rfl
  rw [hsub]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact Submodule.quotEquivOfEq_mk C a7Line a7OrderOne_C (a7Freq40 w.1)

/-- Unweighted `Q` of the order-one output equals the sum of the original
character's pair shares over every pair above `(line, ⊤)`. The pullback has
rank `0`, so this is the manuscript sum in (A8) and the graph cost is `1`.
Each selected output pair lands in one of those original pairs. The sum is at
most the original unweighted `Q`. It is not the refuted bound by one
component, and the share hypothesis remains for a general input. -/
theorem a7OrderOne_nested_sum :
    (∑ p : {q : Submodule F (V 40) × Submodule F (W 40) //
        a7Line ≤ q.1 ∧ q.2 ≤ ⊤},
      a7PairShare p.1.1 p.1.2 (fun M => (character a7FreqMatrix M : ℂ))) =
      (Fintype.card {p : Submodule F (V 40 ⧸ a7Line) ×
          Submodule F (⊤ : Submodule F (W 40)) //
        Selected p.1 p.2 (induced a7Line ⊤ a7Freq40)} : ℝ) := by
  have h := a7_character_nested_share_eq a7Line (⊤ : Submodule F (W 40)) a7FreqMatrix
    (by rw [a7FreqMatrix_toLin]; exact a7Freq40_selected)
  rw [a7FreqMatrix_toLin] at h
  exact h

theorem a7OrderOne_output_selected_card :
    Fintype.card {p : Submodule F (V _) × Submodule F (W _) //
        Selected p.1 p.2 a7OrderOneOutputMatrix.transpose.toLin'} =
      Fintype.card {p : Submodule F (V 40 ⧸ a7Line) ×
          Submodule F (⊤ : Submodule F (W 40)) //
        Selected p.1 p.2 (induced a7Line ⊤ a7Freq40)} := by
  classical
  let C := t1AmbientC a7OrderOneTriple.C
  let H := t1AmbientH a7OrderOneTriple.K
  let eH : H ≃ₗ[F] (⊤ : Submodule F (W 40)) := a7SubCast a7OrderOne_H
  let eQ : (V 40 ⧸ C) ≃ₗ[F] (V 40 ⧸ a7Line) :=
    Submodule.quotEquivOfEq C a7Line a7OrderOne_C
  let eDom := (codomainBasis H).equivFun
  let eCod := (domainBasis C).equivFun
  let eL := LinearEquiv.ofBijective a7OrderIsoL a7OrderIsoL_bijective
  let eR := LinearEquiv.ofBijective a7OrderIsoR a7OrderIsoR_bijective
  have hphi := a7OrderPhi_eq_induced_conj
  have hcoord := carrierFrequency_toLin C H a7OrderPhi
  have hto := a7OrderOne_output_toLin
  have hinduced : Fintype.card {p : Submodule F (V 40 ⧸ C) × Submodule F H //
      Selected p.1 p.2 a7OrderPhi} =
      Fintype.card {p : Submodule F (V 40 ⧸ a7Line) ×
          Submodule F (⊤ : Submodule F (W 40)) //
        Selected p.1 p.2 (induced a7Line ⊤ a7Freq40)} := by
    have htransport := Fintype.card_congr (a7SelectedTransport eH eQ a7OrderPhi)
    exact htransport.trans (a7_selected_card_eq hphi)
  have hcoord' : eCod.toLinearMap.comp (a7OrderPhi.comp eDom.symm.toLinearMap) =
      a7OrderMatrix.transpose.toLin' := by
    rw [a7OrderMatrix]
    exact hcoord.symm
  have hphiCoord : Fintype.card {p : Submodule F (V 40 ⧸ C) × Submodule F H //
      Selected p.1 p.2 a7OrderPhi} =
      Fintype.card {p : Submodule F (Fin (Module.finrank F (V 40 ⧸ C)) → F) ×
          Submodule F (Fin (Module.finrank F H) → F) //
        Selected p.1 p.2 a7OrderMatrix.transpose.toLin'} :=
    (Fintype.card_congr (a7SelectedTransport eDom eCod a7OrderPhi)).trans
      (a7_selected_card_eq hcoord')
  have hpre : eR.toLinearMap.comp
      (a7OrderMatrix.transpose.toLin'.comp eL.symm.symm.toLinearMap) =
      eR.toLinearMap.comp
        (a7OrderMatrix.transpose.toLin'.comp eL.toLinearMap) := by
    rw [LinearEquiv.symm_symm]
  have houtput : Fintype.card {p : Submodule F (Fin (Module.finrank F (V 40 ⧸ C)) → F) ×
      Submodule F (Fin (Module.finrank F H) → F) //
      Selected p.1 p.2 a7OrderMatrix.transpose.toLin'} =
      Fintype.card {p : Submodule F (V _) × Submodule F (W _) //
        Selected p.1 p.2 a7OrderOneOutputMatrix.transpose.toLin'} :=
    (Fintype.card_congr
      (a7SelectedTransport eL.symm eR a7OrderMatrix.transpose.toLin')).trans
      ((a7_selected_card_eq hpre).trans (a7_selected_card_eq hto.symm))
  exact (hinduced.symm.trans (hphiCoord.trans houtput)).symm

theorem a7OrderOne_output_q_eq_nested_shares :
    a7HybridQ (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) =
      ∑ p : {q : Submodule F (V 40) × Submodule F (W 40) //
          a7Line ≤ q.1 ∧ q.2 ≤ ⊤},
        a7PairShare p.1.1 p.1.2 a7Char := by
  have hfun : ∀ (A : Submodule F (V 40)) (B : Submodule F (W 40)),
      a7PairShare A B a7Char =
        a7PairShare A B (fun M => (character a7FreqMatrix M : ℂ)) := by
    intro A B
    rfl
  have hsum : (∑ p : {q : Submodule F (V 40) × Submodule F (W 40) //
      a7Line ≤ q.1 ∧ q.2 ≤ ⊤}, a7PairShare p.1.1 p.1.2 a7Char) =
      ∑ p : {q : Submodule F (V 40) × Submodule F (W 40) //
        a7Line ≤ q.1 ∧ q.2 ≤ ⊤},
        a7PairShare p.1.1 p.1.2 (fun M => (character a7FreqMatrix M : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro p _
    exact hfun p.1.1 p.1.2
  have hcard : a7HybridQ
      (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) =
      (Fintype.card {p : Submodule F (V _) × Submodule F (W _) //
        Selected p.1 p.2 a7OrderOneOutputMatrix.transpose.toLin'} : ℝ) := by
    rw [a7OrderOne_output_character, a7_character_hybrid_q]
  rw [hcard, a7OrderOne_output_selected_card, ← a7OrderOne_nested_sum, hsum]

/-- The same sum is at most the original character's unweighted `Q`. -/
theorem a7OrderOne_output_q_le_original_q :
    a7HybridQ (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) ≤
      a7HybridQ a7Char := by
  rw [a7OrderOne_output_q_eq_nested_shares]
  have hsum : (∑ p : {q : Submodule F (V 40) × Submodule F (W 40) //
      a7Line ≤ q.1 ∧ q.2 ≤ ⊤}, a7PairShare p.1.1 p.1.2 a7Char) =
      ∑ p : {q : Submodule F (V 40) × Submodule F (W 40) //
        a7Line ≤ q.1 ∧ q.2 ≤ ⊤},
        a7PairShare p.1.1 p.1.2 (fun M => (character a7FreqMatrix M : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro p _
    rfl
  rw [hsum]
  exact a7_character_nested_share_le_q a7Line (⊤ : Submodule F (W 40)) a7FreqMatrix

/-- The original pair `(line, ⊤)` contributes `1`, the zero-order output term. -/
theorem a7OrderOne_line_share :
    a7PairShare a7Line (⊤ : Submodule F (W 40)) a7Char = 1 := by
  unfold a7Char
  rw [a7_character_pair_share, a7FreqMatrix_toLin, if_pos a7Freq40_selected]

/-- After the zero-order output term is removed, the remaining output mass
equals the sum of the other original pair shares above `(line, ⊤)`. Those
pairs are not the one component that the order-one excess already exhausts.
The factor is `1`. The share hypothesis remains. -/
theorem a7OrderOne_positive_output_eq_other_shares :
    a7HybridQ (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) -
        a7PairShare (⊥ : Submodule F (V _)) (⊤ : Submodule F (W _))
          (a7OutputBinary a7OrderOneTriple (0 : V 40 →ₗ[F] W 40) a7Char) =
      ∑ p : {q : {r : Submodule F (V 40) × Submodule F (W 40) //
          a7Line ≤ r.1 ∧ r.2 ≤ ⊤} // q.1 ≠ ⟨a7Line, ⊤⟩},
        a7PairShare p.1.1.1 p.1.1.2 a7Char := by
  classical
  let nested := {r : Submodule F (V 40) × Submodule F (W 40) //
    a7Line ≤ r.1 ∧ r.2 ≤ ⊤}
  let p0 : nested := ⟨(a7Line, ⊤), le_rfl, le_top⟩
  let f : nested → ℝ := fun p => a7PairShare p.1.1 p.1.2 a7Char
  have hsum := a7OrderOne_output_q_eq_nested_shares
  have hzero := a7OrderOne_zero_output_share_eq_one
  have hline := a7OrderOne_line_share
  have hsplit : (∑ p : nested, f p) =
      f p0 + ∑ p : {p : nested // p.1 ≠ (a7Line, ⊤)}, f p.1 := by
    let t : Finset nested := Finset.univ.filter (fun p => p.1 ≠ (a7Line, ⊤))
    have hnot : p0 ∉ t := by
      simp [t, p0]
    have huniv : insert p0 t = Finset.univ := by
      ext x
      constructor
      · intro _
        exact Finset.mem_univ x
      · intro _
        by_cases hx : x.1 = (a7Line, ⊤)
        · have hx0 : x = p0 := Subtype.ext hx
          exact hx0 ▸ Finset.mem_insert_self p0 t
        · exact Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
    have hinsert := Finset.sum_insert (f := f) hnot
    rw [← huniv, hinsert]
    refine congrArg (fun s => f p0 + s) ?_
    symm
    refine Finset.sum_bij
      (fun (p : {p : nested // p.1 ≠ (a7Line, ⊤)})
        (_ : p ∈ Finset.univ) => p.1) ?_ ?_ ?_ ?_
    · intro p _
      simpa [t] using p.2
    · intro p _ q _ h
      exact Subtype.ext h
    · intro b hb
      have hb' : b.1 ≠ (a7Line, ⊤) := by
        simpa [t] using hb
      exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
    · intro p _
      rfl
  have hp0 : f p0 = 1 := by
    simp [f, p0, hline]
  rw [hsum, hzero, hsplit, hp0]
  ring

/-- A zero parent matrix has full kernel. -/
theorem a7_zero_matrix_parent_ker {n0 d0 : Nat} :
    LinearMap.ker ((0 : BinaryMatrix n0 d0).transpose.toLin') = ⊤ := by
  refine le_antisymm le_top ?_
  intro w _
  rw [LinearMap.mem_ker]
  simp [Matrix.transpose_zero]

/-- A zero parent matrix has zero range. -/
theorem a7_zero_matrix_parent_range {n0 d0 : Nat} :
    LinearMap.range ((0 : BinaryMatrix n0 d0).transpose.toLin') = ⊥ := by
  rw [LinearMap.range_eq_bot]
  ext w
  simp [Matrix.transpose_zero]

abbrev a7ZeroCout (n0 d0 : Nat) :=
  LinearMap.range ((0 : BinaryMatrix n0 d0).transpose.toLin')

abbrev a7ZeroHout (n0 d0 : Nat) :=
  LinearMap.ker ((0 : BinaryMatrix n0 d0).transpose.toLin')

theorem a7ZeroCout_bot (n0 d0 : Nat) : a7ZeroCout n0 d0 = ⊥ :=
  a7_zero_matrix_parent_range

theorem a7ZeroHout_top (n0 d0 : Nat) : a7ZeroHout n0 d0 = ⊤ :=
  a7_zero_matrix_parent_ker

def a7ZeroIsoL (n0 d0 : Nat) :=
  (a7ZeroHout n0 d0).subtype.comp
    (codomainBasis (a7ZeroHout n0 d0)).equivFun.symm.toLinearMap

def a7ZeroIsoR (n0 d0 : Nat) :=
  (domainBasis (a7ZeroCout n0 d0)).equivFun.toLinearMap.comp
    (a7ZeroCout n0 d0).mkQ

theorem a7ZeroIsoL_bijective (n0 d0 : Nat) : Function.Bijective (a7ZeroIsoL n0 d0) := by
  have hsubSurj : Function.Surjective (a7ZeroHout n0 d0).subtype := by
    intro w
    have hw : w ∈ a7ZeroHout n0 d0 := by
      rw [a7ZeroHout_top]
      exact Submodule.mem_top
    exact ⟨⟨w, hw⟩, rfl⟩
  have hcomp : a7ZeroIsoL n0 d0 =
      (a7ZeroHout n0 d0).subtype.comp
        (codomainBasis (a7ZeroHout n0 d0)).equivFun.symm.toLinearMap := rfl
  rw [hcomp, LinearMap.coe_comp]
  exact Function.Bijective.comp
    ⟨Submodule.injective_subtype (a7ZeroHout n0 d0), hsubSurj⟩
    (codomainBasis (a7ZeroHout n0 d0)).equivFun.symm.bijective

theorem a7ZeroIsoR_bijective (n0 d0 : Nat) : Function.Bijective (a7ZeroIsoR n0 d0) := by
  have hinjQ : Function.Injective (a7ZeroCout n0 d0).mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ, a7ZeroCout_bot]
  have hsurjQ : Function.Surjective (a7ZeroCout n0 d0).mkQ := by
    intro z
    obtain ⟨v, hv⟩ := Quotient.exists_rep z
    refine ⟨v, ?_⟩
    rw [Submodule.mkQ_apply]
    exact hv
  have hcomp : a7ZeroIsoR n0 d0 =
      (domainBasis (a7ZeroCout n0 d0)).equivFun.toLinearMap.comp
        (a7ZeroCout n0 d0).mkQ := rfl
  rw [hcomp, LinearMap.coe_comp]
  exact Function.Bijective.comp
    (domainBasis (a7ZeroCout n0 d0)).equivFun.bijective
    ⟨hinjQ, hsurjQ⟩

/-- The zero-parent output matrix is the carrier character conjugated by the
output bases. -/
def a7ZeroConjMatrix {n0 d0 : Nat} (Z : BinaryMatrix n0 d0) :=
  (LinearMap.toMatrix' (a7ZeroIsoL n0 d0)).transpose * Z *
    (LinearMap.toMatrix' (a7ZeroIsoR n0 d0)).transpose

/-- Reading a character through the zero parent returns the conjugated character. -/
theorem a7_zero_derivative_character {n0 d0 : Nat} (Z : BinaryMatrix n0 d0) :
    (fun X =>
      actualW6Derivative (0 : BinaryMatrix n0 d0) 0
        (fun K => (character Z K : ℂ))
        ((carrierMatrixEquiv (a7ZeroCout n0 d0) (a7ZeroHout n0 d0)).symm X)) =
      fun X => (character (a7ZeroConjMatrix Z) X : ℂ) := by
  funext X
  let Cout := a7ZeroCout n0 d0
  let Hout := a7ZeroHout n0 d0
  have hderiv := a7_zero_derivative_apply (fun K => (character Z K : ℂ))
    ((carrierMatrixEquiv Cout Hout).symm X)
  rw [hderiv]
  let M := (carrierMatrixEquiv Cout Hout).symm X
  have hlin := carrierMatrix_toLin Cout Hout M
  have hXM : carrierMatrixEquiv Cout Hout M = X :=
    (carrierMatrixEquiv Cout Hout).apply_symm_apply X
  rw [hXM] at hlin
  have hM : M =
      (codomainBasis Hout).equivFun.symm.toLinearMap.comp
        (X.toLin'.comp (domainBasis Cout).equivFun.toLinearMap) := by
    refine LinearMap.ext ?_
    intro v
    have hpt := congrFun (congrArg DFunLike.coe hlin)
      ((domainBasis Cout).equivFun v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] at hpt
    exact ((LinearEquiv.symm_apply_eq ((codomainBasis Hout).equivFun)).mpr hpt).symm
  have hmap : Hout.subtype.comp (M.comp Cout.mkQ) =
      (a7ZeroIsoL n0 d0).comp (X.toLin'.comp (a7ZeroIsoR n0 d0)) := by
    rw [hM]
    rfl
  have hmat : LinearMap.toMatrix' (Hout.subtype.comp
      (((carrierMatrixEquiv Cout Hout).symm X).comp Cout.mkQ)) =
      LinearMap.toMatrix' (a7ZeroIsoL n0 d0) * X *
        LinearMap.toMatrix' (a7ZeroIsoR n0 d0) := by
    have hMeq : (carrierMatrixEquiv Cout Hout).symm X = M := rfl
    rw [hMeq, hmap, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin', ← Matrix.mul_assoc]
  rw [hmat]
  unfold a7ZeroConjMatrix
  exact congrFun (a7_character_conj_rect (LinearMap.toMatrix' (a7ZeroIsoL n0 d0))
    (LinearMap.toMatrix' (a7ZeroIsoR n0 d0)) Z) X

theorem a7_zero_conj_toLin {n0 d0 : Nat} (Z : BinaryMatrix n0 d0) :
    (a7ZeroConjMatrix Z).transpose.toLin' =
      (LinearEquiv.ofBijective (a7ZeroIsoR n0 d0) (a7ZeroIsoR_bijective n0 d0)).toLinearMap.comp
        (Z.transpose.toLin'.comp
          (LinearEquiv.ofBijective (a7ZeroIsoL n0 d0) (a7ZeroIsoL_bijective n0 d0)).toLinearMap) := by
  let eL := LinearEquiv.ofBijective (a7ZeroIsoL n0 d0) (a7ZeroIsoL_bijective n0 d0)
  let eR := LinearEquiv.ofBijective (a7ZeroIsoR n0 d0) (a7ZeroIsoR_bijective n0 d0)
  have hEL : eL.toLinearMap = a7ZeroIsoL n0 d0 := by
    ext x
    simp [eL, LinearEquiv.ofBijective_apply]
  have hER : eR.toLinearMap = a7ZeroIsoR n0 d0 := by
    ext x
    simp [eR, LinearEquiv.ofBijective_apply]
  have hYt : (a7ZeroConjMatrix Z).transpose =
      LinearMap.toMatrix' (a7ZeroIsoR n0 d0) * Z.transpose *
        LinearMap.toMatrix' (a7ZeroIsoL n0 d0) := by
    unfold a7ZeroConjMatrix
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hEL, hER, hYt, Matrix.toLin'_mul, Matrix.toLin'_mul]
  rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  rw [LinearMap.comp_assoc]

/-- A zero pullback has the zero coordinate parent. -/
theorem a7_pullback_zero_parent {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (hpull : t1PullbackMap t = 0) :
    a7MixedCoordinateParent t = 0 := by
  unfold a7MixedCoordinateParent
  rw [hpull]
  exact map_zero _

/-- At base zero, a selected character is the induced carrier character. -/
theorem a7_rank_zero_mixed_character {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (Y : BinaryMatrix n d)
    (hsel : Selected (t1AmbientC t.C) (t1AmbientH t.K) Y.transpose.toLin') :
    a7MixedCoordinate t (0 : V d →ₗ[F] W n) (fun M => (character Y M : ℂ)) =
      fun K => (character (carrierFrequencyEquiv (t1AmbientC t.C) (t1AmbientH t.K)
        (induced (t1AmbientC t.C) (t1AmbientH t.K) Y.transpose.toLin')) K : ℂ) := by
  funext K
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  unfold a7MixedCoordinate
  rw [filteredCarrierFunction_character, if_pos hsel]
  have hphase : traceCharacter Y.transpose.toLin' (0 : V d →ₗ[F] W n) = 1 := by
    unfold traceCharacter tracePair
    simp
  rw [hphase, one_mul]
  change (traceCharacter (induced C H Y.transpose.toLin')
      ((carrierMatrixEquiv C H).symm K) : ℂ) =
    (character (carrierFrequencyEquiv C H
      (induced C H Y.transpose.toLin')) K : ℂ)
  rw [carrierFrequency_character]
  exact congrArg
    (fun M => (character (carrierFrequencyEquiv C H
      (induced C H Y.transpose.toLin')) M : ℂ))
    ((carrierMatrixEquiv C H).apply_symm_apply K)

/-- Selected-pair count is unchanged by the zero-parent conjugation. -/
theorem a7_zero_conj_selected_card {n0 d0 : Nat} (Z : BinaryMatrix n0 d0) :
    Fintype.card {p : Submodule F (V _) × Submodule F (W _) //
        Selected p.1 p.2 (a7ZeroConjMatrix Z).transpose.toLin'} =
      Fintype.card {p : Submodule F (V d0) × Submodule F (W n0) //
        Selected p.1 p.2 Z.transpose.toLin'} := by
  classical
  let eL := LinearEquiv.ofBijective (a7ZeroIsoL n0 d0) (a7ZeroIsoL_bijective n0 d0)
  let eR := LinearEquiv.ofBijective (a7ZeroIsoR n0 d0) (a7ZeroIsoR_bijective n0 d0)
  have hto := a7_zero_conj_toLin Z
  have hpre : eR.toLinearMap.comp
      (Z.transpose.toLin'.comp eL.symm.symm.toLinearMap) =
      eR.toLinearMap.comp (Z.transpose.toLin'.comp eL.toLinearMap) := by
    rw [LinearEquiv.symm_symm]
  exact
    ((Fintype.card_congr
      (a7SelectedTransport eL.symm eR Z.transpose.toLin')).trans
      ((a7_selected_card_eq hpre).trans (a7_selected_card_eq hto.symm))).symm

/-- The coordinate reading of an induced map has the same selected-pair count. -/
theorem a7_induced_coordinate_selected_card {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Y : H →ₗ[F] (V d ⧸ C)) :
    Fintype.card {p : Submodule F (V _) × Submodule F (W _) //
        Selected p.1 p.2
          (carrierFrequencyEquiv C H Y).transpose.toLin'} =
      Fintype.card {p : Submodule F (V d ⧸ C) × Submodule F H //
        Selected p.1 p.2 Y} := by
  classical
  let eDom := (codomainBasis H).equivFun
  let eCod := (domainBasis C).equivFun
  have hcoord := carrierFrequency_toLin C H Y
  have hcoord' : eCod.toLinearMap.comp (Y.comp eDom.symm.toLinearMap) =
      (carrierFrequencyEquiv C H Y).transpose.toLin' := hcoord.symm
  exact ((Fintype.card_congr (a7SelectedTransport eDom eCod Y)).trans
    (a7_selected_card_eq hcoord')).symm

/-- The zero-parent reading does not change the unweighted `Q` of a character. -/
theorem a7_zero_derivative_q {n0 d0 : Nat} (Z : BinaryMatrix n0 d0) :
    a7HybridQ (fun X =>
        actualW6Derivative (0 : BinaryMatrix n0 d0) 0
          (fun K => (character Z K : ℂ))
          ((carrierMatrixEquiv (a7ZeroCout n0 d0) (a7ZeroHout n0 d0)).symm X)) =
      a7HybridQ (fun K => (character Z K : ℂ)) := by
  have hfun := a7_zero_derivative_character Z
  rw [hfun]
  have hleft := a7_character_hybrid_q (a7ZeroConjMatrix Z)
  have hright := a7_character_hybrid_q Z
  rw [hleft, a7_zero_conj_selected_card Z, hright]

/-- Every rank-zero output of a selected character has unweighted `Q` equal to
the sum of the original character's pair shares over the pairs above that
carrier. The pullback rank is `0`, so the manuscript (A8) graph cost is `1`
and each selected output pair lands in one of those original pairs. Positive
pullback rank and a general complex input remain open, so this does not delete
the share hypothesis. -/
theorem a7_rank_zero_output_q_eq_nested {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (Y : BinaryMatrix n d)
    (hpull : t1PullbackMap t = 0)
    (hsel : Selected (t1AmbientC t.C) (t1AmbientH t.K) Y.transpose.toLin') :
    a7HybridQ (a7OutputBinary t (0 : V d →ₗ[F] W n)
        (fun M => (character Y M : ℂ))) =
      ∑ p : {q : Submodule F (V d) × Submodule F (W n) //
          t1AmbientC t.C ≤ q.1 ∧ q.2 ≤ t1AmbientH t.K},
        a7PairShare p.1.1 p.1.2 (fun M => (character Y M : ℂ)) := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let phi := induced C H Y.transpose.toLin'
  let Z := carrierFrequencyEquiv C H phi
  have hparent := a7_pullback_zero_parent t hpull
  have hmixed := a7_rank_zero_mixed_character t Y hsel
  let charY := fun M => (character Y M : ℂ)
  let coord := a7MixedCoordinate t (0 : V d →ₗ[F] W n) charY
  let evalQ {a b : Nat} (P : BinaryMatrix a b) (g : BinaryMatrix a b → ℂ) : ℝ :=
    a7HybridQ
      (n := Module.finrank F (LinearMap.ker P.transpose.toLin'))
      (d := Module.finrank F (V b ⧸ LinearMap.range P.transpose.toLin'))
      (fun X =>
        actualW6Derivative (n := a) (d := b) P (0 : V b →ₗ[F] W a) g
          ((carrierMatrixEquiv (n := a) (d := b)
            (LinearMap.range P.transpose.toLin')
            (LinearMap.ker P.transpose.toLin')).symm X))
  have hdef : a7HybridQ (a7OutputBinary t (0 : V d →ₗ[F] W n) charY) =
      evalQ (a7MixedCoordinateParent t) coord := by
    unfold a7OutputBinary evalQ
    rfl
  have hP : evalQ (a7MixedCoordinateParent t) coord = evalQ 0 coord :=
    congrArg (fun P => evalQ P coord) hparent
  have hg : evalQ 0 coord = evalQ 0 (fun K => (character Z K : ℂ)) :=
    congrArg (evalQ 0) hmixed
  have hder : evalQ 0 (fun K => (character Z K : ℂ)) =
      a7HybridQ (fun K => (character Z K : ℂ)) :=
    a7_zero_derivative_q Z
  have hlink : a7HybridQ (a7OutputBinary t (0 : V d →ₗ[F] W n) charY) =
      a7HybridQ (fun K => (character Z K : ℂ)) :=
    hdef.trans (hP.trans (hg.trans hder))
  rw [hlink, a7_character_hybrid_q Z,
    a7_induced_coordinate_selected_card C H phi]
  exact (a7_character_nested_share_eq C H Y hsel).symm

/-- The predecessor filter of one character keeps that character exactly when
the parent precedes it. -/
theorem a7_predecessor_filter_character {n d : Nat}
    (X Z : BinaryMatrix n d) :
    w6PredecessorFilter X (fun M => (character Z M : ℂ)) =
      if w6Precedes X Z then fun M => (character Z M : ℂ) else 0 := by
  classical
  funext M
  unfold w6PredecessorFilter
  simp_rw [complexFourierCoeff_character]
  by_cases h : w6Precedes X Z
  · simp only [h, if_true]
    have hterm : ∀ Y : BinaryMatrix n d,
        (if w6Precedes X Y then
          (if Y = Z then (1 : ℂ) else 0) * (character Y M : ℂ) else 0) =
          if Y = Z then (character Z M : ℂ) else 0 := by
      intro Y
      by_cases hY : Y = Z
      · simp [hY, h]
      · simp [hY]
    simp_rw [hterm]
    simp
  · simp only [h, if_false]
    apply Finset.sum_eq_zero
    intro Y _
    by_cases hY : Y = Z
    · simp [hY, h]
    · simp [hY]

/-- At base zero, the derivative of a character is that character on the
parent's affine slice when the parent precedes it, and is zero otherwise. -/
theorem a7_derivative_character_apply {n d : Nat}
    (X Z : BinaryMatrix n d)
    (M : (V d ⧸ LinearMap.range X.transpose.toLin') →ₗ[F]
      LinearMap.ker X.transpose.toLin') :
    actualW6Derivative X (0 : V d →ₗ[F] W n)
        (fun K => (character Z K : ℂ)) M =
      if w6Precedes X Z then
        (character Z (LinearMap.toMatrix'
          ((LinearMap.ker X.transpose.toLin').subtype.comp
            (M.comp (LinearMap.range X.transpose.toLin').mkQ))) : ℂ)
      else 0 := by
  unfold actualW6Derivative complexAmbientAffineRestrict
  rw [a7_predecessor_filter_character]
  by_cases h : w6Precedes X Z
  · simp [h, zero_add]
  · simp [h]

/-- The trace pairing of a map against an affine slice is the pairing of the
induced carrier map. This is the positive-rank form of the rank-zero
character transport. -/
theorem a7_tracePair_induced {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (M : (V d ⧸ C) →ₗ[F] H) :
    tracePair Y (H.subtype.comp (M.comp C.mkQ)) =
      tracePair (C.mkQ.comp (Y.comp H.subtype)) M :=
  tracePair_carrier C H Y M

/-- A preceding selected character, read on the parent's affine slice, is the
induced carrier character. -/
theorem a7_derivative_character_induced {n d : Nat}
    (X Z : BinaryMatrix n d)
    (hprec : w6Precedes X Z)
    (M : (V d ⧸ LinearMap.range X.transpose.toLin') →ₗ[F]
      LinearMap.ker X.transpose.toLin') :
    actualW6Derivative X (0 : V d →ₗ[F] W n)
        (fun K => (character Z K : ℂ)) M =
      (traceCharacter (induced (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin') Z.transpose.toLin') M : ℂ) := by
  rw [a7_derivative_character_apply, if_pos hprec]
  let affine := (LinearMap.ker X.transpose.toLin').subtype.comp
    (M.comp (LinearMap.range X.transpose.toLin').mkQ)
  have hlin : (LinearMap.toMatrix' affine).toLin' = affine :=
    Matrix.toLin'_toMatrix' affine
  have hchar : character Z (LinearMap.toMatrix' affine) =
      traceCharacter Z.transpose.toLin' affine := by
    have h :=
      (PvNP.RealizableHardness.BinaryMatrixA1CharacterBridge.traceCharacter_eq_matrix_character
        Z (LinearMap.toMatrix' affine)).symm
    rw [hlin] at h
    exact h
  rw [hchar]
  have htrace := a7_tracePair_induced
    (LinearMap.range X.transpose.toLin')
    (LinearMap.ker X.transpose.toLin')
    Z.transpose.toLin' M
  unfold traceCharacter
  rw [show tracePair Z.transpose.toLin' affine =
      tracePair (induced (LinearMap.range X.transpose.toLin')
        (LinearMap.ker X.transpose.toLin') Z.transpose.toLin') M from by
    simpa [affine, induced] using htrace]

/-- The coordinate reading of a preceding character derivative is the induced
carrier character. -/
theorem a7_preceding_derivative_coordinate {n d : Nat}
    (X Z : BinaryMatrix n d) (hprec : w6Precedes X Z) :
    (fun Xout =>
      actualW6Derivative X (0 : V d →ₗ[F] W n)
        (fun K => (character Z K : ℂ))
        ((carrierMatrixEquiv
            (LinearMap.range X.transpose.toLin')
            (LinearMap.ker X.transpose.toLin')).symm Xout)) =
      fun Xout =>
        (character (carrierFrequencyEquiv
            (LinearMap.range X.transpose.toLin')
            (LinearMap.ker X.transpose.toLin')
            (induced (LinearMap.range X.transpose.toLin')
              (LinearMap.ker X.transpose.toLin') Z.transpose.toLin')) Xout : ℂ) := by
  funext Xout
  let C := LinearMap.range X.transpose.toLin'
  let H := LinearMap.ker X.transpose.toLin'
  let phi := induced C H Z.transpose.toLin'
  rw [a7_derivative_character_induced X Z hprec]
  have htrace := carrierFrequency_character C H phi
    ((carrierMatrixEquiv C H).symm Xout)
  have happ := (carrierMatrixEquiv C H).apply_symm_apply Xout
  exact congrArg (fun r : ℝ => (r : ℂ))
    (htrace.trans (congrArg (character (carrierFrequencyEquiv C H phi)) happ))

/-- At positive or zero parent rank, a preceding selected character has output
`Q` equal to the sum of its original pair shares above the parent's
range and kernel. Each selected output pair is one of those original pairs.
A general complex input remains open, and summing the equality over every
triple still needs the A9 overlap, so this does not delete the share
hypothesis. -/
theorem a7_preceding_character_q_eq_nested {n d : Nat}
    (X Z : BinaryMatrix n d) (hprec : w6Precedes X Z)
    (hsel : Selected (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin') Z.transpose.toLin') :
    a7HybridQ (fun Xout =>
        actualW6Derivative X (0 : V d →ₗ[F] W n)
          (fun K => (character Z K : ℂ))
          ((carrierMatrixEquiv
              (LinearMap.range X.transpose.toLin')
              (LinearMap.ker X.transpose.toLin')).symm Xout)) =
      ∑ p : {q : Submodule F (V d) × Submodule F (W n) //
          LinearMap.range X.transpose.toLin' ≤ q.1 ∧
            q.2 ≤ LinearMap.ker X.transpose.toLin'},
        a7PairShare p.1.1 p.1.2 (fun M => (character Z M : ℂ)) := by
  let C := LinearMap.range X.transpose.toLin'
  let H := LinearMap.ker X.transpose.toLin'
  let phi := induced C H Z.transpose.toLin'
  have hfun := a7_preceding_derivative_coordinate X Z hprec
  have hq := a7_character_hybrid_q
    (carrierFrequencyEquiv C H phi)
  have hcard := a7_induced_coordinate_selected_card C H phi
  have hnest := a7_character_nested_share_eq C H Z hsel
  rw [hfun, hq, hcard]
  exact hnest.symm

/-- One final pair above a preceding parent is a single nonnegative term of
that parent's nested sum, hence at most the parent's output `Q`. -/
theorem a7_preceding_one_pair_le_output {n d : Nat}
    (X Z : BinaryMatrix n d) (hprec : w6Precedes X Z)
    (hsel : Selected (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin') Z.transpose.toLin')
    (q : {p : Submodule F (V d) × Submodule F (W n) //
      LinearMap.range X.transpose.toLin' ≤ p.1 ∧
        p.2 ≤ LinearMap.ker X.transpose.toLin'}) :
    a7PairShare q.1.1 q.1.2 (fun M => (character Z M : ℂ)) ≤
      a7HybridQ (fun Xout =>
        actualW6Derivative X (0 : V d →ₗ[F] W n)
          (fun K => (character Z K : ℂ))
          ((carrierMatrixEquiv
              (LinearMap.range X.transpose.toLin')
              (LinearMap.ker X.transpose.toLin')).symm Xout)) := by
  have hsum := a7_preceding_character_q_eq_nested X Z hprec hsel
  refine le_trans ?_ (le_of_eq hsum.symm)
  exact Finset.single_le_sum
    (fun p _ => a7_pair_share_nonneg p.1.1 p.1.2 (fun M => (character Z M : ℂ)))
    (Finset.mem_univ q)

/-- Coordinate output `Q` of one parent acting on one character. -/
def a7PrecedingOutputQ {n d : Nat} (X Z : BinaryMatrix n d) : ℝ :=
  a7HybridQ (fun Xout =>
    actualW6Derivative X (0 : V d →ₗ[F] W n)
      (fun K => (character Z K : ℂ))
      ((carrierMatrixEquiv
          (LinearMap.range X.transpose.toLin')
          (LinearMap.ker X.transpose.toLin')).symm Xout))

/-- One preceding selected character has coordinate output `Q` at most the
original character `Q`. The factor is `1`: the output equals the nested pair
sum, and that sum is a subset of the original pair shares. A general complex
input remains open, so this does not delete the share hypothesis. -/
theorem a7_preceding_character_q_le_original {n d : Nat}
    (X Z : BinaryMatrix n d) (hprec : w6Precedes X Z)
    (hsel : Selected (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin') Z.transpose.toLin') :
    a7PrecedingOutputQ X Z ≤
      a7HybridQ (fun M => (character Z M : ℂ)) := by
  unfold a7PrecedingOutputQ
  exact le_trans
    (le_of_eq (a7_preceding_character_q_eq_nested X Z hprec hsel))
    (a7_character_nested_share_le_q
      (LinearMap.range X.transpose.toLin')
      (LinearMap.ker X.transpose.toLin') Z)

/-- Sum the coordinate output `Q` of a family of preceding selected parents,
indexed by the initial graphs of one fixed final with `a+b+k ≤ D`. The A9
fiber has cardinality at most `2^{3D(i+j+k)}`, and each output is at most the
original character `Q`, so the sum is at most that multiplicity times the
original `Q`. The family is a hypothesis: an `A9InitialDatum` is not yet a
parent matrix. A general complex input remains open, so this does not delete
the share hypothesis. -/
theorem a7_a9_preceding_output_sum_le {n d : Nat}
    (D i j k a b : Nat)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (Z : BinaryMatrix n d)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (parent : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j →
      BinaryMatrix n d)
    (hprec : ∀ datum, w6Precedes (parent datum) Z)
    (hsel : ∀ datum, Selected
      (LinearMap.range (parent datum).transpose.toLin')
      (LinearMap.ker (parent datum).transpose.toLin')
      Z.transpose.toLin') :
    (∑ datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
        a7PrecedingOutputQ (parent datum) Z) ≤
      (2 : ℝ) ^ (3 * D * (i + j + k)) *
        a7HybridQ (fun M => (character Z M : ℂ)) := by
  classical
  let Qorig := a7HybridQ (fun M => (character Z M : ℂ))
  have hnn : 0 ≤ Qorig := a7HybridQ_nonneg _
  have hcard := a9_final_inducing_multiplicity D i j k a b A B Y
    hfin hi hj hA hB hY
  have hle : ∀ datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
      a7PrecedingOutputQ (parent datum) Z ≤ Qorig :=
    fun datum => a7_preceding_character_q_le_original
      (parent datum) Z (hprec datum) (hsel datum)
  have hsum :
      (∑ datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
          a7PrecedingOutputQ (parent datum) Z) ≤
        ∑ _ : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j, Qorig :=
    Finset.sum_le_sum (fun datum _ => hle datum)
  have hconst :
      (∑ _ : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j, Qorig) =
        (Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) : ℝ) *
          Qorig := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine le_trans hsum ?_
  rw [hconst]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn

/-- The same family with the A8 graph weight `2^{6Dk}` on every output stays
under `2^{9D(i+j+k)}` times the original character `Q`. The weight is the
proved graph cost, not a new exponent. The parent family remains a hypothesis,
and a general complex input remains open. -/
theorem a7_a9_preceding_output_graph_charge {n d : Nat}
    (D i j k a b : Nat)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (Z : BinaryMatrix n d)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (parent : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j →
      BinaryMatrix n d)
    (hprec : ∀ datum, w6Precedes (parent datum) Z)
    (hsel : ∀ datum, Selected
      (LinearMap.range (parent datum).transpose.toLin')
      (LinearMap.ker (parent datum).transpose.toLin')
      Z.transpose.toLin') :
    (∑ datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
        (2 : ℝ) ^ (6 * D * k) * a7PrecedingOutputQ (parent datum) Z) ≤
      (2 : ℝ) ^ (9 * D * (i + j + k)) *
        a7HybridQ (fun M => (character Z M : ℂ)) := by
  classical
  let Qorig := a7HybridQ (fun M => (character Z M : ℂ))
  have hnn : 0 ≤ Qorig := a7HybridQ_nonneg _
  have hcost := a9_final_inducing_graph_cost D i j k a b A B Y
    hfin hi hj hA hB hY
  have hle : ∀ datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
      (2 : ℝ) ^ (6 * D * k) * a7PrecedingOutputQ (parent datum) Z ≤
        (2 : ℝ) ^ (6 * D * k) * Qorig :=
    fun datum => mul_le_mul_of_nonneg_left
      (a7_preceding_character_q_le_original
        (parent datum) Z (hprec datum) (hsel datum))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hsum :
      (∑ datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
          (2 : ℝ) ^ (6 * D * k) * a7PrecedingOutputQ (parent datum) Z) ≤
        ∑ _ : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
          (2 : ℝ) ^ (6 * D * k) * Qorig :=
    Finset.sum_le_sum (fun datum _ => hle datum)
  have hconst :
      (∑ _ : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
          (2 : ℝ) ^ (6 * D * k) * Qorig) =
        (Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) : ℝ) *
          ((2 : ℝ) ^ (6 * D * k) * Qorig) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hassoc :
      (Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) : ℝ) *
          ((2 : ℝ) ^ (6 * D * k) * Qorig) =
        ((Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) : ℝ) *
          (2 : ℝ) ^ (6 * D * k)) * Qorig :=
    (mul_assoc
      ((Fintype.card (A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) : ℝ))
      ((2 : ℝ) ^ (6 * D * k)) Qorig).symm
  refine le_trans hsum ?_
  rw [hconst, hassoc]
  exact mul_le_mul_of_nonneg_right hcost hnn

/-- The zero matrix has range zero and full kernel, so it selects every
frequency through `(⊥, ⊤)`. -/
theorem a7_zero_matrix_range {n d : Nat} :
    LinearMap.range ((0 : BinaryMatrix n d).transpose.toLin') = ⊥ := by
  rw [LinearMap.range_eq_bot]
  ext w
  simp [Matrix.transpose_zero]

theorem a7_zero_matrix_ker {n d : Nat} :
    LinearMap.ker ((0 : BinaryMatrix n d).transpose.toLin') = ⊤ := by
  refine le_antisymm le_top ?_
  intro w _
  rw [LinearMap.mem_ker]
  simp [Matrix.transpose_zero]

theorem a7_zero_matrix_selected {n d : Nat} (Z : BinaryMatrix n d) :
    Selected (LinearMap.range ((0 : BinaryMatrix n d).transpose.toLin'))
      (LinearMap.ker ((0 : BinaryMatrix n d).transpose.toLin'))
      Z.transpose.toLin' := by
  rw [a7_zero_matrix_range, a7_zero_matrix_ker]
  exact a7_bot_top_selected _

/-- Every initial datum of one fixed final may be sent to the zero matrix.
That matrix precedes `Z` and selects it, so this is an actual case of the
hypothesized family. The zero matrix does not read the graphs. A general
complex input remains open, so this does not delete the share hypothesis. -/
theorem a7_a9_zero_parent_family_le {n d : Nat}
    (D i j k a b : Nat)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (Z : BinaryMatrix n d)
    (hfin : a + b + k ≤ D) (hi : i ≤ a) (hj : j ≤ b)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k) :
    (∑ _datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j,
        a7PrecedingOutputQ (0 : BinaryMatrix n d) Z) ≤
      (2 : ℝ) ^ (3 * D * (i + j + k)) *
        a7HybridQ (fun M => (character Z M : ℂ)) :=
  a7_a9_preceding_output_sum_le D i j k a b A B Y Z
    hfin hi hj hA hB hY
    (fun _ => 0)
    (fun _ => a7_precedes_zero Z)
    (fun _ => a7_zero_matrix_selected Z)

/-- The project-then-lift map of one coordinate datum, as a map of the
coordinate spaces. -/
noncomputable def a9ThetaCarrier {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    V (k + (b - j)) →ₗ[F] W (k + (a - i)) :=
  ((⊥ : Submodule F (W (k + (a - i)))).quotEquivOfEqBot rfl).toLinearMap.comp
    ((a9FinalTheta d).comp
      (@Submodule.topEquiv F (V (k + (b - j))) _ _ _).symm.toLinearMap)

/-- That map as a binary matrix. This is the parent matrix determined by the
datum. -/
noncomputable def a9ThetaParentMatrix {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    BinaryMatrix (k + (a - i)) (k + (b - j)) :=
  LinearMap.toMatrix' (a9ThetaCarrier d)

theorem a9ThetaCarrier_rank {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    Module.finrank F (LinearMap.range (a9ThetaCarrier d)) = k := by
  classical
  let eTop := @Submodule.topEquiv F (V (k + (b - j))) _ _ _
  let eBot := (⊥ : Submodule F (W (k + (a - i)))).quotEquivOfEqBot rfl
  have hr1 : LinearMap.range ((a9FinalTheta d).comp eTop.symm.toLinearMap) =
      LinearMap.range (a9FinalTheta d) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr eTop.symm.surjective,
      Submodule.map_top]
  have hr2 : LinearMap.range (a9ThetaCarrier d) =
      Submodule.map eBot.toLinearMap (LinearMap.range (a9FinalTheta d)) := by
    unfold a9ThetaCarrier
    rw [LinearMap.range_comp, hr1]
  rw [hr2, LinearEquiv.finrank_map_eq eBot]
  exact a9FinalTheta_rank d

/-- The datum's parent matrix has rank `k`. -/
theorem a9ThetaParentMatrix_rank {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    (a9ThetaParentMatrix d).rank = k := by
  have hlin : (a9ThetaParentMatrix d).toLin' = a9ThetaCarrier d := by
    unfold a9ThetaParentMatrix
    exact Matrix.toLin'_toMatrix' (a9ThetaCarrier d)
  have hrank := Matrix.rank_eq_finrank_range_toLin (a9ThetaParentMatrix d)
    (Pi.basisFun F _) (Pi.basisFun F _)
  rw [Matrix.toLin_eq_toLin'] at hrank
  rw [hrank, hlin]
  exact a9ThetaCarrier_rank d

/-- On one fixed subspace pair, the parent matrix determines both graphs. -/
theorem a9ThetaParentMatrix_graphs {a b k i j : Nat}
    (A0 : W6Grass (V a) i) (B0 : W6Grass (V b) j)
    (im₁ im₂ : (V k) →ₗ[F] ((V a) ⧸ A0.1))
    (ker₁ ker₂ : ((V b) ⧸ B0.1) →ₗ[F] (V k))
    (h : a9ThetaParentMatrix ⟨A0, B0, im₁, ker₁⟩ =
      a9ThetaParentMatrix ⟨A0, B0, im₂, ker₂⟩) :
    ker₁ = ker₂ ∧ im₁ = im₂ := by
  have hlin : a9ThetaCarrier ⟨A0, B0, im₁, ker₁⟩ =
      a9ThetaCarrier ⟨A0, B0, im₂, ker₂⟩ := by
    unfold a9ThetaParentMatrix at h
    simpa [Matrix.toLin'_toMatrix'] using congrArg Matrix.toLin' h
  have htheta : a9FinalTheta ⟨A0, B0, im₁, ker₁⟩ =
      a9FinalTheta ⟨A0, B0, im₂, ker₂⟩ := by
    apply LinearMap.ext
    intro x
    let eTop := @Submodule.topEquiv F (V (k + (b - j))) _ _ _
    let eBot := (⊥ : Submodule F (W (k + (a - i)))).quotEquivOfEqBot rfl
    have hpoint := congrFun (congrArg DFunLike.coe hlin) (eTop x)
    simp only [a9ThetaCarrier, LinearMap.comp_apply,
      LinearEquiv.symm_apply_apply] at hpoint
    exact eBot.injective hpoint
  exact a9FinalTheta_graphs_inverse A0 B0 im₁ im₂ ker₁ ker₂ htheta

/-- The zero matrix is an actual preceding selected parent of the datum's
own matrix, so the coordinate output `Q` is at most that matrix's character
`Q`. A general complex input remains open, so this does not delete the share
hypothesis. -/
theorem a9ThetaParent_output_le {a b k i j : Nat}
    (d : A9InitialDatum (V a) (V b) (V k) i j) :
    a7PrecedingOutputQ
        (0 : BinaryMatrix (k + (a - i)) (k + (b - j)))
        (a9ThetaParentMatrix d) ≤
      a7HybridQ (fun M => (character (a9ThetaParentMatrix d) M : ℂ)) :=
  a7_preceding_character_q_le_original
    (0 : BinaryMatrix (k + (a - i)) (k + (b - j)))
    (a9ThetaParentMatrix d)
    (a7_precedes_zero _)
    (a7_zero_matrix_selected _)

/-- Sum the zero-parent outputs of the matrices determined by one coordinate
fiber. Each term is that matrix's own character `Q`. This does not charge
one ambient component by the fiber. -/
theorem a7_a9_theta_parent_sum_le {a b k i j : Nat} :
    (∑ d : A9InitialDatum (V a) (V b) (V k) i j,
        a7PrecedingOutputQ
          (0 : BinaryMatrix (k + (a - i)) (k + (b - j)))
          (a9ThetaParentMatrix d)) ≤
      ∑ d : A9InitialDatum (V a) (V b) (V k) i j,
        a7HybridQ (fun M => (character (a9ThetaParentMatrix d) M : ℂ)) := by
  classical
  exact Finset.sum_le_sum (fun d _ => a9ThetaParent_output_le d)

/-- Identify a finite module of rank `n` with the coordinate space `V n`. -/
noncomputable def a9ModuleToFin (n : Nat) {M : Type*}
    [AddCommGroup M] [Module F M] [Module.Finite F M]
    (h : Module.finrank F M = n) : M ≃ₗ[F] (V n) := by
  letI : Module.Free F M := Module.Free.of_basis (Module.finBasis F M)
  exact (Module.finBasis F M).equivFun.trans
    (LinearEquiv.piCongrLeft F (fun _ => F) (Equiv.cast (congrArg Fin h)))

/-- Push a subspace across a linear equivalence. -/
noncomputable def a9TransportGrass {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {i : Nat} (e : M ≃ₗ[F] N)
    (U : W6Grass M i) : W6Grass N i :=
  ⟨Submodule.map e.toLinearMap U.1, by
    rw [LinearEquiv.finrank_map_eq e]
    exact U.2⟩

theorem a9TransportGrass_injective {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {i : Nat} (e : M ≃ₗ[F] N) :
    Function.Injective (a9TransportGrass (i := i) e) := by
  intro U₁ U₂ h
  apply Subtype.ext
  have hmap : Submodule.map e.toLinearMap U₁.1 =
      Submodule.map e.toLinearMap U₂.1 :=
    congrArg Subtype.val h
  ext x
  constructor
  · intro hx
    have hmem : e x ∈ Submodule.map e.toLinearMap U₂.1 := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    rcases hmem with ⟨y, hy, he⟩
    have hyx : y = x := e.injective he
    simpa [hyx] using hy
  · intro hx
    have hmem : e x ∈ Submodule.map e.toLinearMap U₁.1 := by
      rw [hmap]
      exact ⟨x, hx, rfl⟩
    rcases hmem with ⟨y, hy, he⟩
    have hyx : y = x := e.injective he
    simpa [hyx] using hy

/-- The quotient by a subspace travels with the linear equivalence. -/
noncomputable def a9QuotientTransport {M N : Type*}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (e : M ≃ₗ[F] N) (U : Submodule F M) :
    (M ⧸ U) ≃ₗ[F] (N ⧸ Submodule.map e.toLinearMap U) :=
  LinearEquiv.ofBijective
    (U.mapQ (Submodule.map e.toLinearMap U) e.toLinearMap (by
      intro x hx
      exact ⟨x, hx, rfl⟩))
    (by
      constructor
      · intro q₁ q₂ hq
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U q₁
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective U q₂
        apply (Submodule.Quotient.eq U).mpr
        have hq' : Submodule.Quotient.mk (e x) =
            Submodule.Quotient.mk (e y) := hq
        have hdiff : e x - e y ∈ Submodule.map e.toLinearMap U :=
          (Submodule.Quotient.eq (Submodule.map e.toLinearMap U)).mp hq'
        rcases hdiff with ⟨u, hu, he⟩
        have hxy : x - y = u := e.injective (by
          simpa [map_sub] using he.symm)
        rw [hxy]
        exact hu
      · intro q
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
          (Submodule.map e.toLinearMap U) q
        obtain ⟨x, hx⟩ := e.surjective y
        refine ⟨U.mkQ x, ?_⟩
        change Submodule.Quotient.mk (e x) = Submodule.Quotient.mk y
        rw [hx])

/-- Move one fixed-final graph datum onto coordinate carriers. -/
noncomputable def a9TransportDatum {A B S : Type*}
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [AddCommGroup S] [Module F S]
    {a b k i j : Nat}
    (eA : A ≃ₗ[F] (V a)) (eB : B ≃ₗ[F] (V b)) (eS : S ≃ₗ[F] (V k))
    (d : A9InitialDatum A B S i j) :
    A9InitialDatum (V a) (V b) (V k) i j where
  A0 := a9TransportGrass eA d.A0
  B0 := a9TransportGrass eB d.B0
  imGraph :=
    (a9QuotientTransport eA d.A0.1).toLinearMap.comp
      (d.imGraph.comp eS.symm.toLinearMap)
  kerGraph :=
    eS.toLinearMap.comp
      (d.kerGraph.comp (a9QuotientTransport eB d.B0.1).symm.toLinearMap)

theorem a9Transport_ker_cancel {B S : Type*}
    [AddCommGroup B] [Module F B] [AddCommGroup S] [Module F S]
    {b k j : Nat}
    (eB : B ≃ₗ[F] (V b)) (eS : S ≃ₗ[F] (V k))
    (B0 : W6Grass B j) (ker : (B ⧸ B0.1) →ₗ[F] S)
    (q : B ⧸ B0.1) :
    (eS.toLinearMap.comp
        (ker.comp (a9QuotientTransport eB B0.1).symm.toLinearMap))
        ((a9QuotientTransport eB B0.1) q) = eS (ker q) := by
  simp [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- Distinct graph data stay distinct after the coordinate transport.
Each datum therefore charges one coordinate datum, and
`a9EmbedSumFiber_injective` sends that datum to one sum fiber. -/
theorem a9TransportDatum_injective {A B S : Type*}
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [AddCommGroup S] [Module F S]
    {a b k i j : Nat}
    (eA : A ≃ₗ[F] (V a)) (eB : B ≃ₗ[F] (V b)) (eS : S ≃ₗ[F] (V k)) :
    Function.Injective (a9TransportDatum (i := i) (j := j) eA eB eS) := by
  intro d₁ d₂ h
  cases d₁ with
  | mk A1 B1 im₁ ker₁ =>
    cases d₂ with
    | mk A2 B2 im₂ ker₂ =>
      have hA0 : (a9TransportDatum eA eB eS ⟨A1, B1, im₁, ker₁⟩).A0 =
          (a9TransportDatum eA eB eS ⟨A2, B2, im₂, ker₂⟩).A0 := by
        rw [h]
      have hB0 : (a9TransportDatum eA eB eS ⟨A1, B1, im₁, ker₁⟩).B0 =
          (a9TransportDatum eA eB eS ⟨A2, B2, im₂, ker₂⟩).B0 := by
        rw [h]
      have hA : A1 = A2 := a9TransportGrass_injective eA
        (by simpa [a9TransportDatum] using hA0)
      have hB : B1 = B2 := a9TransportGrass_injective eB
        (by simpa [a9TransportDatum] using hB0)
      subst hA
      subst hB
      unfold a9TransportDatum at h
      injection h with _hA0 _hB0 him hker
      have him' : im₁ = im₂ := by
        apply LinearMap.ext
        intro s
        have hpoint := congrFun (congrArg DFunLike.coe him) (eS s)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.symm_apply_apply] at hpoint
        exact (a9QuotientTransport eA A1.1).injective hpoint
      have hker' : ker₁ = ker₂ := by
        apply LinearMap.ext
        intro q
        have hpoint := congrFun (congrArg DFunLike.coe hker)
          ((a9QuotientTransport eB B1.1) q)
        change (eS.toLinearMap.comp
            (ker₁.comp (a9QuotientTransport eB B1.1).symm.toLinearMap))
            ((a9QuotientTransport eB B1.1) q) =
          (eS.toLinearMap.comp
            (ker₂.comp (a9QuotientTransport eB B1.1).symm.toLinearMap))
            ((a9QuotientTransport eB B1.1) q) at hpoint
        rw [a9Transport_ker_cancel eB eS B1 ker₁ q,
          a9Transport_ker_cancel eB eS B1 ker₂ q] at hpoint
        exact eS.injective hpoint
      cases him'
      cases hker'
      rfl

/-- Each graph datum of one fixed final `(A, W/B, range Y)` charges one
sum fiber. The transport is injective, and `a9EmbedSumFiber_injective`
keeps those fibers apart. `a9FinalTheta_rank` keeps rank `k`. The
multiplicity `2^{3D(i+j+k)}` remains `a9_final_inducing_multiplicity`,
and the graph cost remains `a9_final_inducing_graph_cost`. This does not
bound `a7HybridQ` of an output, and it does not remove the share. -/
noncomputable def a9FinalInducingTriple {n d a b k i j : Nat}
    (hk : 0 < k)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) :
    A9EmbeddedSumFiber a b k i j :=
  a9EmbedSumFiber hk
    (a9TransportDatum (a9ModuleToFin a hA) (a9ModuleToFin b hB)
      (a9ModuleToFin k hY) datum)

theorem a9FinalInducingTriple_injective {n d a b k i j : Nat}
    (hk : 0 < k)
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k) :
    Function.Injective (a9FinalInducingTriple (n := n) (d := d)
      (a := a) (b := b) (k := k) (i := i) (j := j) hk A B Y hA hB hY) := by
  intro d₁ d₂ h
  exact a9TransportDatum_injective (a9ModuleToFin a hA) (a9ModuleToFin b hB)
    (a9ModuleToFin k hY)
    (a9EmbedSumFiber_injective hk (by simpa [a9FinalInducingTriple] using h))

/-- The transported project-then-lift map still has rank `k`. -/
theorem a9FinalInducingTriple_rank {n d a b k i j : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) :
    Module.finrank F (LinearMap.range (a9FinalTheta
      (a9TransportDatum (a9ModuleToFin a hA) (a9ModuleToFin b hB)
        (a9ModuleToFin k hY) datum))) = k :=
  a9FinalTheta_rank
    (a9TransportDatum (a9ModuleToFin a hA) (a9ModuleToFin b hB)
      (a9ModuleToFin k hY) datum)

/-- The parent matrix of one initial datum of a fixed final `(A, W/B, range Y)`.
Transport to coordinates, then read the project-then-lift map. Its rank is `k`.
The zero matrix precedes it. A general complex input remains open, so this
does not delete the share hypothesis. -/
noncomputable def a9FinalParentMatrix {n d a b k i j : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) :
    BinaryMatrix (k + (a - i)) (k + (b - j)) :=
  a9ThetaParentMatrix
    (a9TransportDatum (a9ModuleToFin a hA) (a9ModuleToFin b hB)
      (a9ModuleToFin k hY) datum)

theorem a9FinalParentMatrix_rank {n d a b k i j : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) :
    (a9FinalParentMatrix A B Y hA hB hY datum).rank = k :=
  a9ThetaParentMatrix_rank
    (a9TransportDatum (a9ModuleToFin a hA) (a9ModuleToFin b hB)
      (a9ModuleToFin k hY) datum)

theorem a9FinalParent_output_le {n d a b k i j : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : W n →ₗ[F] V d)
    (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W n ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (datum : A9InitialDatum A (W n ⧸ B) (LinearMap.range Y) i j) :
    a7PrecedingOutputQ
        (0 : BinaryMatrix (k + (a - i)) (k + (b - j)))
        (a9FinalParentMatrix A B Y hA hB hY datum) ≤
      a7HybridQ (fun M =>
        (character (a9FinalParentMatrix A B Y hA hB hY datum) M : ℂ)) :=
  a9ThetaParent_output_le
    (a9TransportDatum (a9ModuleToFin a hA) (a9ModuleToFin b hB)
      (a9ModuleToFin k hY) datum)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
