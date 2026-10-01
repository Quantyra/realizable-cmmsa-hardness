import PvNP.RealizableHardness.ActualTypedABFullA16Assembly
import PvNP.RealizableHardness.ActualTypedABEndpointTransport
import PvNP.RealizableHardness.ActualBinaryMatrixHC46CommonDerivative
import PvNP.RealizableHardness.ActualTypedABBottomTopRankReindex
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction

/-! The complete arbitrary-carrier A16 energy assembly. The source premise
is the original actual globalness statement, and the endpoint is the actual
selected hybrid filter followed by the chosen affine carrier restriction. -/

namespace PvNP.RealizableHardness.ActualTypedABFullA16Final

open ActualTypedABFullA16Assembly
open ActualTypedABCanonicalDCollapse
open ActualTypedABRankedTower
open ActualTypedABBottomTopRankReindex
open ActualFiniteDegreeFourierReconstruction
open BinaryMatrixTypedA14Line
open ActualTypedABCanonicalFlag
open ActualTypedABCanonicalEndpointCollapse
open ActualTypedABCanonicalRankProjectionCollapse
open ActualTypedABEndpointTransport
open ActualTypedABOriginalGlobalBridgeClean
open ActualBinaryMatrixHC46A18SourceGlobal
open BinaryMatrixA1TypedFourier BinaryMatrixFourier BinaryMatrixComplexA14
open BinaryMatrixComplexA15 BinaryMatrixTypedA15Transport
open BinaryMatrixNestedSelectorA1
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

private theorem succ_le_two_pow (m : Nat) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        m + 1 + 1 ≤ 2 * (m + 1) := by omega
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by simp [pow_succ, Nat.mul_comm]

private theorem count_le_two_pow_sq (D : Nat) : D + 1 ≤ 2 ^ (D ^ 2) := by
  by_cases hD : D = 0
  · simp [hD]
  have hDpos : 1 ≤ D := by omega
  have hDsquare : D ≤ D ^ 2 := by
    simpa [pow_two] using (Nat.le_mul_self D)
  exact (succ_le_two_pow D).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two hDsquare)

/-- Every retained rank projection is the residual typed projection of its
own source-canonical tower, transported to the requested endpoint carrier.
The same original source is used at every rank; only the residual rank changes. -/
private theorem retained_rank_representation {n d i l h : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (lines : DomainLineFlag (⊥ : Submodule F (V d)) l)
    (hlines : lines.endpoint = A)
    (hypers : CodomainHyperplaneFlag (⊤ : Submodule F (W n)) h)
    (hhypers : hypers.endpoint = B)
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hpositive : l + h ≠ 0) (hlevel : l + h ≤ i) :
    ∃ φ : ((V d ⧸ A) →ₗ[F] B) → Complex,
      (fun M => filteredCarrierFunction A B T
        (complexRankProjection i f) M) =
        typedComplexRankProjection A B (i - (h + l)) φ := by
  let source : ((V d ⧸ (⊥ : Submodule F (V d))) →ₗ[F]
      (⊤ : Submodule F (W n))) → Complex := fun M =>
    filteredCarrierFunction (⊥ : Submodule F (V d))
      (⊤ : Submodule F (W n)) 0 f M
  let r := i - (h + l)
  let T0 := initialBottomTopBase T
  let tower := buildCanonicalSourceTower (r := r) (f := source)
    lines hypers T0
  let hends := buildCanonicalSourceTower_endpoints
    (r := r) (f := source) lines hypers T0
  let hA := hends.1.trans hlines
  let hB := hends.2.trans hhypers
  let e := endpointHomEquiv hA hB
  let φ : ((V d ⧸ A) →ₗ[F] B) → Complex := fun M =>
    (rankedTerminalData tower).fend (e.symm M)
  have hidx : r + (h + l) = i := by
    dsimp [r]
    omega
  have hcollapse :
      typedComplexRankProjection (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend r (rankedTerminalData tower).fend =
      fun M => filteredCarrierFunction (rankedTerminalData tower).Aend
        (rankedTerminalData tower).Bend T
        (complexRankProjection i f) M := by
    have hc := canonical_source_rank_projection_collapse
      (r := r) (l := l) (h := h) lines hypers T f hpositive
    simpa only [source, tower, T0, hidx] using hc
  have hrep :
      typedComplexRankProjection A B r φ =
        fun M => filteredCarrierFunction A B T
          (complexRankProjection i f) M := by
    funext M
    have hn := endpointProjection_natural hA hB
      (rankedTerminalData tower).fend (e.symm M)
    have hcM := congrFun hcollapse (e.symm M)
    dsimp [φ, e] at hn ⊢
    rw [endpointHomEquiv_apply_symm_apply] at hn
    simpa only [hA, hB] using hn.symm.trans hcM
  exact ⟨φ, hrep.symm⟩

/-- Arbitrary typed carriers, arbitrary affine base, and arbitrary ambient
width: Fourier support through `D` together with the original actual
up-to-`D` global bound implies the full A16 carrier-energy bound. The proof
derives parameter nonnegativity, treats zero carrier cost directly, removes
unselected low ranks, and sums the orthogonal residual-rank levels. -/
theorem filteredCarrierFunction_energy_le_A16
    {n d D : Nat} {eps : Real}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hglobal : UpToActualNormSqGlobal D eps f) :
    carrierMean A B (fun M => Complex.normSq
      (filteredCarrierFunction A B T f M)) ≤
      (2 : Real) ^ (11 * D ^ 2) * eps := by
  let l := Module.finrank F A
  let h := Module.finrank F (⊤ : Submodule F (W n)) - Module.finrank F B
  let k := l + h
  obtain ⟨lines, hlines, hypers, hhypers⟩ :=
    exists_canonical_source_flags A B
  have hquot := B.finrank_quotient_add_finrank
  have htop : Module.finrank F (⊤ : Submodule F (W n)) =
      Module.finrank F (W n) := bottomTopCodomainEquiv.finrank_eq
  have hcod : h = Module.finrank F (W n ⧸ B) := by
    dsimp [h]
    omega
  have hk : k = Module.finrank F A + Module.finrank F (W n ⧸ B) := by
    dsimp [k, l]
    rw [hcod]
  have heps : 0 ≤ eps := filteredCarrierFunction_parameter_nonneg f hglobal
  by_cases hkzero : k = 0
  · have hlzero : l = 0 := by dsimp [k] at hkzero; omega
    have hhzero : h = 0 := by dsimp [k] at hkzero; omega
    have hA_dim : Module.finrank F A = 0 := by simpa [l] using hlzero
    have hA : A = ⊥ := Submodule.finrank_eq_zero.mp hA_dim
    have hB_dim : Module.finrank F B =
        Module.finrank F (⊤ : Submodule F (W n)) := by
      have hhzero' : Module.finrank F (⊤ : Submodule F (W n)) -
          Module.finrank F B = 0 := by simpa [h] using hhzero
      omega
    have hB : B = ⊤ := Submodule.eq_of_le_of_finrank_eq le_top hB_dim
    rw [hA, hB]
    let Q0 : CarrierRestriction (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n)) :=
      ⟨⊥, ⊤, 0⟩
    have htyped := actual_global_to_bottomTop_typed f hglobal
    have hzero_mean : carrierMean (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n))
        (fun M => Complex.normSq (filteredCarrierFunction
          (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) 0 f M)) ≤ eps := by
      have hQ := htyped Q0 (by simp [Q0, CarrierRestriction.order])
      simpa [BinaryMatrixA1TypedFourier.carrierMean,
        CarrierRestriction.fibre, Q0, filteredCarrierFunction_bot_top] using hQ
    let T0 := initialBottomTopBase T
    have hmean := zero_step_carrier_energy_mean T0 f
    have hbase : (⊤ : Submodule F (W n)).subtype.comp
        (T0.comp (Submodule.mkQ (⊥ : Submodule F (V d)))) = T :=
      initialBottomTopBase_ambient T
    have hshift : carrierMean (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n))
        (fun M => Complex.normSq (filteredCarrierFunction
          (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) T f M)) =
      carrierMean (⊥ : Submodule F (V d))
        (⊤ : Submodule F (W n))
        (fun M => Complex.normSq (filteredCarrierFunction
          (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n)) 0 f M)) := by
      simpa [hbase] using hmean
    have hsmall : (2 : Real) ^ (10 * D ^ 2) ≤
        (2 : Real) ^ (11 * D ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num
    calc
      carrierMean (⊥ : Submodule F (V d)) (⊤ : Submodule F (W n))
          (fun M => Complex.normSq
            (filteredCarrierFunction (⊥ : Submodule F (V d))
              (⊤ : Submodule F (W n)) T f M)) = _ := hshift
      _ ≤ eps := hzero_mean
      _ ≤ (2 : Real) ^ (11 * D ^ 2) * eps := by
        have hfactor : (1 : Real) ≤ (2 : Real) ^ (11 * D ^ 2) := by positivity
        calc
          eps = 1 * eps := by ring
          _ ≤ (2 : Real) ^ (11 * D ^ 2) * eps :=
            mul_le_mul_of_nonneg_right hfactor heps
  · have hkpos : k ≠ 0 := hkzero
    let levels : Finset Nat := Finset.range (D + 1)
    let g : Nat → ((V d ⧸ A) →ₗ[F] B) → Complex := fun i M =>
      filteredCarrierFunction A B T (complexRankProjection i f) M
    have hlevel (i : Nat) (hi : i ∈ levels) :
        carrierMean A B (fun M => Complex.normSq (g i M)) ≤
          (2 : Real) ^ (10 * D ^ 2) * eps := by
      have hiD : i ≤ D := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hlow : i < k
      · have hz := filteredCarrierFunction_rankProjection_zero_of_below_carrier
          A B T f (by omega)
        have hzero : g i = fun _ => 0 := by
          funext M
          exact congrFun hz M
        rw [hzero]
        simp only [Complex.normSq_zero, carrierMean]
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _) heps
      · have hki : k ≤ i := by omega
        exact filteredCarrierFunction_rankProjection_energy_bound A B
          lines hlines hypers hhypers T f eps heps hglobal
          (by omega) (by omega) hiD
    have horth : ∀ i ∈ levels, ∀ j ∈ levels, i ≠ j →
        carrierMean A B (fun M => complexRealDotFinal (g i M) (g j M)) = 0 := by
      intro i hi j hj hij
      by_cases hilo : i < k
      · have hz := filteredCarrierFunction_rankProjection_zero_of_below_carrier
          A B T f (by omega)
        have hzero : g i = fun _ => 0 := by
          funext M
          exact congrFun hz M
        simp [complexRealDotFinal, hzero]
      · by_cases hjlo : j < k
        · have hz := filteredCarrierFunction_rankProjection_zero_of_below_carrier
            A B T f (by omega)
          have hzero : g j = fun _ => 0 := by
            funext M
            exact congrFun hz M
          simp [complexRealDotFinal, hzero]
        · have hik : k ≤ i := by omega
          have hjk : k ≤ j := by omega
          obtain ⟨φi, hri⟩ := retained_rank_representation A B
            lines hlines hypers hhypers T f (by omega) (by omega)
          obtain ⟨φj, hrj⟩ := retained_rank_representation A B
            lines hlines hypers hhypers T f (by omega) (by omega)
          have hres : i - k ≠ j - k := by omega
          rw [hri, hrj]
          exact typedComplexRankProjection_cross_orthogonal A B φi φj hres
    have hsumEnergy := carrierEnergy_finite_sum_of_orthogonal
      A B levels g horth
    have hdecomp : (fun M => ∑ i ∈ levels, g i M) =
        fun M => filteredCarrierFunction A B T f M := by
      funext M
      exact filteredCarrierFunction_reconstruct_range_of_support
        A B T f hsupport M
    have henergy : carrierMean A B (fun M => Complex.normSq
        (filteredCarrierFunction A B T f M)) =
        ∑ i ∈ levels, carrierMean A B
          (fun M => Complex.normSq (g i M)) := by
      calc
        _ = carrierMean A B
            (fun M => Complex.normSq (∑ i ∈ levels, g i M)) := by
              congr 1
              funext M
              exact (congrFun hdecomp M).symm
        _ = _ := hsumEnergy
    calc
      carrierMean A B (fun M => Complex.normSq
          (filteredCarrierFunction A B T f M)) =
        ∑ i ∈ levels, carrierMean A B
          (fun M => Complex.normSq (g i M)) := henergy
      _ ≤ ∑ i ∈ levels, ((2 : Real) ^ (10 * D ^ 2) * eps) :=
        Finset.sum_le_sum (by
          intro i hi
          exact hlevel i hi)
      _ = (D + 1 : Real) * ((2 : Real) ^ (10 * D ^ 2) * eps) := by
        simp [levels]
      _ ≤ (2 : Real) ^ (D ^ 2) *
          ((2 : Real) ^ (10 * D ^ 2) * eps) := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast count_le_two_pow_sq D)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) ≤ 2) _) heps)
      _ = ((2 : Real) ^ (D ^ 2) *
          (2 : Real) ^ (10 * D ^ 2)) * eps := by ring
      _ = (2 : Real) ^ (11 * D ^ 2) * eps := by
        rw [← pow_add]
        congr 1
        ring

end
end PvNP.RealizableHardness.ActualTypedABFullA16Final
