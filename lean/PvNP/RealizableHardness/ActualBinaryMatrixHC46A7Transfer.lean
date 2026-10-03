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

theorem a7_qComponent_uniform_nonneg {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) :
    0 ≤ typedUniformMean (fun T : V d →ₗ[F] W n => typedW6QComponent A B T f) := by
  unfold typedUniformMean
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  refine Finset.sum_nonneg (fun _ _ => ?_)
  unfold typedW6QComponent
  exact sq_nonneg _

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

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer
