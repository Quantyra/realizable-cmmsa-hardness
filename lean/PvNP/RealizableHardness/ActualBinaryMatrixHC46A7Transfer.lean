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
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Moment
open PvNP.RealizableHardness.ActualFiniteDegreeFourierProduct
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.BinaryMatrixA1Complex
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

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
