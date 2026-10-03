import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
import PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Moment
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7EnergyConsumer
import PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction

/-! Manuscript A6 on the ordinary T1 transfer.

The Hölder step is the fourth-power cost `2^(3ij)` of a sum of `2^(ij)`
terms. Averaging over the affine base is a translation of the finite matrix
group, so it preserves the ordinary-filter fourth moment. Each triple
reconstructs its original pair in both directions, and a mixed derivative
whose order exceeds the Fourier degree is identically zero.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer

open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite
set_option maxHeartbeats 1500000

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Moment
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7EnergyConsumer
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Incidence
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Convolution
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
open PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d -> F
private abbrev W (n : Nat) := Fin n -> F

/-- Fourth-power Hölder cost of a finite sum: `N` terms contribute `N^3`. -/
theorem a6_holder_fourth_sum {ι : Type*} [Fintype ι] (g : ι → Complex) :
    Complex.normSq (∑ i, g i) ^ 2 ≤
      (Fintype.card ι : ℝ) ^ 3 * ∑ i, Complex.normSq (g i) ^ 2 := by
  classical
  let N : ℝ := Fintype.card ι
  let S : ℝ := ∑ i, Complex.normSq (g i)
  have h1 : Complex.normSq (∑ i, g i) ≤ N * S := by
    simpa [N, S] using complex_normSq_sum_le_card_mul_sum_normSq g
  have hsq : S ^ 2 ≤ N * ∑ i, Complex.normSq (g i) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ : ι => (1 : ℝ)) (fun i => Complex.normSq (g i))
    simpa [S, Finset.card_univ, N] using h
  have hpow : Complex.normSq (∑ i, g i) ^ 2 ≤ (N * S) ^ 2 := by
    have ha : 0 ≤ Complex.normSq (∑ i, g i) := Complex.normSq_nonneg _
    have hb : 0 ≤ N * S := by
      apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
    nlinarith
  calc
    Complex.normSq (∑ i, g i) ^ 2 ≤ (N * S) ^ 2 := hpow
    _ = N ^ 2 * S ^ 2 := by ring
    _ ≤ N ^ 2 * (N * ∑ i, Complex.normSq (g i) ^ 2) := by
      gcongr
    _ = N ^ 3 * ∑ i, Complex.normSq (g i) ^ 2 := by ring

/-- `7D(i+j) + 3ij ≤ 24Dt` whenever `i,j ≤ D` and `i+j ≤ 2t`. -/
theorem a6_exponent_le (D i j t : Nat) (hi : i ≤ D) (hj : j ≤ D)
    (hij : i + j ≤ 2 * t) :
    7 * D * (i + j) + 3 * i * j ≤ 24 * D * t := by
  have hijD : i * j ≤ D * (i + j) := by
    calc
      i * j ≤ D * j := Nat.mul_le_mul_right j hi
      _ ≤ D * (i + j) := Nat.mul_le_mul_left D (Nat.le_add_left j i)
  have h3 : 3 * (i * j) ≤ 3 * (D * (i + j)) := Nat.mul_le_mul_left 3 hijD
  have h10 : 7 * D * (i + j) + 3 * i * j ≤ 10 * D * (i + j) := by
    have hsum : 7 * D * (i + j) + 3 * (i * j) ≤
        7 * D * (i + j) + 3 * (D * (i + j)) := Nat.add_le_add_left h3 _
    have hassoc : 7 * D * (i + j) + 3 * (D * (i + j)) = 10 * D * (i + j) := by
      ring
    rw [hassoc] at hsum
    have hre : 3 * i * j = 3 * (i * j) := by ring
    rw [hre]
    exact hsum
  have h20 : 10 * D * (i + j) ≤ 20 * D * t := by
    calc
      10 * D * (i + j) ≤ 10 * D * (2 * t) := Nat.mul_le_mul_left (10 * D) hij
      _ = 20 * D * t := by ring
  have h24 : 20 * D * t ≤ 24 * D * t := by
    have hmul : 20 * (D * t) ≤ 24 * (D * t) := Nat.mul_le_mul_right (D * t) (by decide : 20 ≤ 24)
    simpa [Nat.mul_assoc] using hmul
  exact le_trans h10 (le_trans h20 h24)

/-- Selected ambient rank splits as carrier cost plus residual carrier rank. -/
theorem a6_selected_rank_split {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Y : BinaryMatrix n d)
    (hsel : Selected C H Y.transpose.toLin') :
    Y.rank = Module.finrank F C + Module.finrank F (W n ⧸ H) +
      Module.finrank F (LinearMap.range
        ((C.mkQ.comp Y.transpose.toLin').domRestrict H)) := by
  classical
  let L : W n →ₗ[F] V d := Y.transpose.toLin'
  let qL : W n →ₗ[F] (V d ⧸ C) := C.mkQ.comp L
  let R : Submodule F (V d) := LinearMap.range L
  let CR : Submodule F R := C.comap R.subtype
  let qR : R →ₗ[F] (V d ⧸ C) := C.mkQ.comp R.subtype
  let qH : H →ₗ[F] (V d ⧸ C) := qL.domRestrict H
  have hCR : C ≤ R := hsel.1
  have hCRdim : Module.finrank F CR = Module.finrank F C :=
    (Submodule.comapSubtypeEquivOfLe hCR).finrank_eq
  have hkerR : LinearMap.ker qR = CR := by
    simp [qR, CR, LinearMap.ker_comp]
  have hfactor : qL = qR.comp L.rangeRestrict := by
    ext x
    rfl
  have hqrange : LinearMap.range qL = LinearMap.range qR := by
    rw [hfactor]
    exact LinearMap.range_comp_of_range_eq_top qR (LinearMap.range_rangeRestrict L)
  have hqrank : Module.finrank F (LinearMap.range qL) =
      Module.finrank F (LinearMap.range qR) :=
    congrArg (fun S : Submodule F (V d ⧸ C) => Module.finrank F S) hqrange
  have hnullR := LinearMap.finrank_range_add_finrank_ker qR
  have hdimR : Module.finrank F R =
      Module.finrank F (LinearMap.range qL) + Module.finrank F C := by
    rw [hqrank]
    rw [hkerR, hCRdim] at hnullR
    exact hnullR.symm
  have hmatrixRank : Y.rank = Module.finrank F R := by
    change Matrix.rank Y = Module.finrank F (LinearMap.range L)
    rw [← Matrix.rank_transpose Y]
    rw [Matrix.rank_eq_finrank_range_toLin Y.transpose
      (Pi.basisFun F _) (Pi.basisFun F _)]
    rw [Matrix.toLin_eq_toLin']
  have hkerBound : LinearMap.ker qL ≤ H := by
    intro x hx
    have hxzero : C.mkQ (L x) = 0 := by
      simpa [qL, LinearMap.mem_ker] using hx
    have hxC : L x ∈ C := by
      have hmem : L x ∈ LinearMap.ker C.mkQ := LinearMap.mem_ker.mpr hxzero
      rw [Submodule.ker_mkQ] at hmem
      exact hmem
    exact hsel.2 x hxC
  have hkerH : LinearMap.ker qH = (LinearMap.ker qL).comap H.subtype := by
    ext h
    simp [qH, qL, LinearMap.mem_ker, LinearMap.domRestrict_apply]
  have hkerDim : Module.finrank F (LinearMap.ker qH) =
      Module.finrank F (LinearMap.ker qL) := by
    rw [hkerH]
    exact (Submodule.comapSubtypeEquivOfLe hkerBound).finrank_eq
  have hnullL := LinearMap.finrank_range_add_finrank_ker qL
  have hnullH := LinearMap.finrank_range_add_finrank_ker qH
  have hquotH := H.finrank_quotient_add_finrank
  change Module.finrank F (W n ⧸ H) + Module.finrank F H =
    Module.finrank F (W n) at hquotH
  have hqRankSplit : Module.finrank F (LinearMap.range qL) =
      Module.finrank F (W n ⧸ H) + Module.finrank F (LinearMap.range qH) := by
    rw [hkerDim] at hnullH
    omega
  calc
    Y.rank = Module.finrank F R := hmatrixRank
    _ = Module.finrank F (LinearMap.range qL) + Module.finrank F C := hdimR
    _ = Module.finrank F (W n ⧸ H) + Module.finrank F (LinearMap.range qH) +
          Module.finrank F C := by rw [hqRankSplit]
    _ = Module.finrank F C + Module.finrank F (W n ⧸ H) +
          Module.finrank F (LinearMap.range qH) := by omega

/-- Mixed order `dim C + codim H + rank X`. -/
def a6Order {n d : Nat} {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) : Nat :=
  Module.finrank F (t1AmbientC t.C) +
    Module.finrank F (W n ⧸ t1AmbientH t.K) +
    Module.finrank F (LinearMap.range (t1PullbackMap t))

/-- Uniform average, over the original base and the output carrier, of one
mixed derivative's fourth power. -/
def a6DerivativeFourth {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex) : ℝ :=
  (∑ T : V d →ₗ[F] W n, ∑ M : (V d ⧸ A) →ₗ[F] B,
      Complex.normSq (typedW6FourierDerivative (t1AmbientC t.C) (t1AmbientH t.K)
        (t1PullbackMap t)
        (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
        (t1OutputEquiv t M)) ^ 2) /
    ((Fintype.card (V d →ₗ[F] W n) : ℝ) *
      (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ))

/-- The original pair is the preimage of the image and the kernel of the
triple. This is one reconstruction direction. -/
theorem a6_reconstruct_forward {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    Submodule.comap (Submodule.mkQ (t1AmbientC t.C))
        (LinearMap.range (t1PullbackMap t)) = A ∧
      Submodule.map (t1AmbientH t.K).subtype
        (LinearMap.ker (t1PullbackMap t)) = B := by
  constructor
  · rw [t1Pullback_range, t1AQuotientToAmbient_range]
    rw [Submodule.comap_map_eq]
    rw [Submodule.ker_mkQ]
    exact sup_eq_left.mpr (t1AmbientC_le_A t.C)
  · rw [t1Pullback_ker]
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_subtype]
      exact t1AmbientH_containsB B t.K)

/-- Activity forces ordinary selection and the canonical triple. This is the
other reconstruction direction, with no extra triple. -/
theorem a6_reconstruct_backward {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (t : T1IndexTriple A B)
    (ht : t1ActiveTriple A B Y t) :
    ∃ hY : DR6OrdinarySelected A B Y, t = t1SelectedTriple A B Y hY :=
  t1ActiveTriple_unique A B Y t ht

/-- A degree-`D` ordinary filter vanishes when `dim A` or `codim B` exceeds `D`. -/
theorem a6_ordinaryFilter_zero_of_high_degree {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hhigh : D < Module.finrank F A ∨ D < Module.finrank F (W n ⧸ B))
    (M : BinaryMatrix n d) :
    DR6ComplexOrdinaryFilter A B f M = 0 := by
  classical
  unfold DR6ComplexOrdinaryFilter
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hsel : DR6ComplexOrdinarySelected A B Y
  · have hord : DR6OrdinarySelected A B Y :=
      (dr6_complexSelector_iff_actualOrdinary A B Y).1 hsel
    let L : W n →ₗ[F] V d := Y.transpose.toLin'
    have hrank : Y.rank = Module.finrank F (LinearMap.range L) := by
      change Matrix.rank Y = Module.finrank F (LinearMap.range L)
      rw [← Matrix.rank_transpose Y]
      rw [Matrix.rank_eq_finrank_range_toLin Y.transpose
        (Pi.basisFun F _) (Pi.basisFun F _)]
      rw [Matrix.toLin_eq_toLin']
    have hi : Module.finrank F A ≤ Y.rank := by
      rw [hrank]
      exact Submodule.finrank_mono hord.1
    have hj : Module.finrank F (W n ⧸ B) ≤ Y.rank := by
      have hker : Module.finrank F (LinearMap.ker L) ≤ Module.finrank F B :=
        Submodule.finrank_mono hord.2
      have hnull := LinearMap.finrank_range_add_finrank_ker L
      have hquot := B.finrank_quotient_add_finrank
      change Module.finrank F (W n ⧸ B) + Module.finrank F B =
        Module.finrank F (W n) at hquot
      rw [hrank]
      omega
    have hgt : D < Y.rank := by
      cases hhigh with
      | inl hA => exact lt_of_lt_of_le hA hi
      | inr hB => exact lt_of_lt_of_le hB hj
    have hcoeff : complexFourierCoeff f Y = 0 := hsupport Y hgt
    simp [hsel, hcoeff]
  · simp [hsel]

/-- A mixed derivative of order greater than the Fourier degree is zero. -/
theorem a6_mixed_zero_of_order_gt {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (ht : D < a6Order t)
    (T : V d →ₗ[F] W n)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedW6FourierDerivative (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
      (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
      (t1OutputEquiv t M) = 0 := by
  classical
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  unfold typedW6FourierDerivative
  apply Finset.sum_eq_zero
  intro Z _
  by_cases hpred : typedW6Precedes C H X Z
  · have hcoeff : complexCarrierFourierCoeff C H
        (filteredCarrierFunction C H T f) Z = 0 := by
      rw [t1FilteredCarrierFunction_fourierCoeff]
      apply Finset.sum_eq_zero
      intro Y _
      by_cases hsel : Selected C H Y.transpose.toLin'
      · by_cases hq : Z = C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)
        · have hpred' : Module.finrank F (LinearMap.range Z) =
              Module.finrank F (LinearMap.range X) +
                Module.finrank F (LinearMap.range (Z - X)) := hpred
          have hmap : (C.mkQ.comp Y.transpose.toLin').domRestrict H = Z := by
            ext x
            simp [hq, LinearMap.domRestrict_apply]
          have hsplit := a6_selected_rank_split C H Y hsel
          have hrank : a6Order t ≤ Y.rank := by
            rw [hmap] at hsplit
            have hord : a6Order t =
                Module.finrank F C + Module.finrank F (W n ⧸ H) +
                  Module.finrank F (LinearMap.range X) := by
              simp [a6Order, C, H, X]
            have hle : Module.finrank F (LinearMap.range X) ≤
                Module.finrank F (LinearMap.range Z) := by
              rw [hpred']
              exact Nat.le_add_right _ _
            rw [hord]
            calc
              Module.finrank F C + Module.finrank F (W n ⧸ H) +
                  Module.finrank F (LinearMap.range X) ≤
                Module.finrank F C + Module.finrank F (W n ⧸ H) +
                  Module.finrank F (LinearMap.range Z) :=
                Nat.add_le_add_left hle _
              _ = Y.rank := hsplit.symm
          have hcoeffY : complexFourierCoeff f Y = 0 := hsupport Y (lt_of_lt_of_le ht hrank)
          simp [hsel, hq, hcoeffY]
        · simp [hsel, hq]
      · simp [hsel]
    rw [if_pos hpred, hcoeff, zero_mul]
  · rw [if_neg hpred]

/-- Pointwise Hölder cost `2^(3ij)` on the ordinary affine slice. -/
theorem a6_pointwise_holder {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    Complex.normSq (complexAmbientAffineRestrict A B T
        (DR6ComplexOrdinaryFilter A B f) M) ^ 2 ≤
      (2 : ℝ) ^ (3 * (Module.finrank F A * Module.finrank F (W n ⧸ B))) *
        ∑ t : T1IndexTriple A B,
          Complex.normSq (typedW6FourierDerivative (t1AmbientC t.C)
            (t1AmbientH t.K) (t1PullbackMap t)
            (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
            (t1OutputEquiv t M)) ^ 2 := by
  classical
  have hId := t1PointwiseFull_fourierIdentity A B T f M
  have hhold := a6_holder_fourth_sum (fun t : T1IndexTriple A B =>
    typedW6FourierDerivative (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
      (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
      (t1OutputEquiv t M))
  rw [← hId] at hhold
  have hcard := t1Triple_card A B
  have hpow : (Fintype.card (T1IndexTriple A B) : ℝ) ^ 3 =
      (2 : ℝ) ^ (3 * (Module.finrank F A * Module.finrank F (W n ⧸ B))) := by
    rw [hcard, Nat.cast_pow, ← pow_mul, mul_comm]
    ring
  simpa [hpow] using hhold

/-- Translation along a fixed affine shift is a bijection of the matrix group,
so the ordinary-filter fourth moment is the uniform average of its affine slices. -/
theorem a6_uniform_translation {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) :
    uniformMean (fun M => Complex.normSq (DR6ComplexOrdinaryFilter A B f M) ^ 2) =
      (∑ T : V d →ₗ[F] W n, ∑ N : (V d ⧸ A) →ₗ[F] B,
        Complex.normSq (complexAmbientAffineRestrict A B T
          (DR6ComplexOrdinaryFilter A B f) N) ^ 2) /
        ((Fintype.card (V d →ₗ[F] W n) : ℝ) *
          (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)) := by
  classical
  let phi : BinaryMatrix n d → ℝ := fun M =>
    Complex.normSq (DR6ComplexOrdinaryFilter A B f M) ^ 2
  let eMatrix : (V d →ₗ[F] W n) ≃ BinaryMatrix n d :=
    { toFun := LinearMap.toMatrix'
      invFun := Matrix.toLin'
      left_inv := fun T => by simp
      right_inv := fun M => by simp }
  have hcardM : Fintype.card (V d →ₗ[F] W n) = Fintype.card (BinaryMatrix n d) :=
    Fintype.card_congr eMatrix
  have hslice (N : (V d ⧸ A) →ₗ[F] B) :
      ∑ T : V d →ₗ[F] W n,
        phi (LinearMap.toMatrix' (T + B.subtype.comp (N.comp A.mkQ))) =
      ∑ M : BinaryMatrix n d, phi M := by
    let shift : V d →ₗ[F] W n := B.subtype.comp (N.comp A.mkQ)
    let eShift : (V d →ₗ[F] W n) ≃ (V d →ₗ[F] W n) :=
      { toFun := fun T => T + shift
        invFun := fun T => T - shift
        left_inv := fun T => by simp [shift]
        right_inv := fun T => by simp [shift] }
    calc
      ∑ T, phi (LinearMap.toMatrix' (T + shift)) =
          ∑ T, phi (eMatrix (eShift T)) := by simp [eMatrix, eShift, shift]
      _ = ∑ T, phi (eMatrix T) :=
        Equiv.sum_comp eShift (fun T => phi (eMatrix T))
      _ = ∑ M, phi M := Equiv.sum_comp eMatrix phi
  have hsum : ∑ N : (V d ⧸ A) →ₗ[F] B, ∑ T, phi (LinearMap.toMatrix'
      (T + B.subtype.comp (N.comp A.mkQ))) =
      (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ) * ∑ M, phi M := by
    -- the inner equality is in ℕ-indexed sums of reals; convert after
    have hnat : ∑ N : (V d ⧸ A) →ₗ[F] B, ∑ T, phi (LinearMap.toMatrix'
        (T + B.subtype.comp (N.comp A.mkQ))) =
        ∑ N : (V d ⧸ A) →ₗ[F] B, ∑ M, phi M := by
      apply Finset.sum_congr rfl
      intro N _
      simpa using hslice N
    rw [hnat]
    simp [Finset.sum_const, Finset.card_univ]
  unfold uniformMean
  have hden : ((Fintype.card (V d →ₗ[F] W n) : ℝ) *
      (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)) ≠ 0 := by
    positivity
  -- rewrite the double sum via hsum and cancel the output cardinality
  have hrewrite :
      (∑ T, ∑ N : (V d ⧸ A) →ₗ[F] B, phi (LinearMap.toMatrix'
          (T + B.subtype.comp (N.comp A.mkQ)))) /
        ((Fintype.card (V d →ₗ[F] W n) : ℝ) *
          (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)) =
      (∑ M, phi M) / (Fintype.card (BinaryMatrix n d) : ℝ) := by
    have hcomm : ∑ T, ∑ N : (V d ⧸ A) →ₗ[F] B, phi (LinearMap.toMatrix'
        (T + B.subtype.comp (N.comp A.mkQ))) =
        ∑ N : (V d ⧸ A) →ₗ[F] B, ∑ T, phi (LinearMap.toMatrix'
          (T + B.subtype.comp (N.comp A.mkQ))) := Finset.sum_comm
    rw [hcomm, hsum, hcardM]
    field_simp
  simpa [phi, complexAmbientAffineRestrict] using hrewrite.symm

/-- Ordinary dimension splits across the triple: `i + j = order + rank X`. -/
theorem a6_dimension_split {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    Module.finrank F A + Module.finrank F (W n ⧸ B) =
      a6Order t + Module.finrank F (LinearMap.range (t1PullbackMap t)) := by
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  have hCdim : Module.finrank F C = Module.finrank F t.C :=
    (Submodule.equivMapOfInjective A.subtype (Submodule.injective_subtype A) t.C).finrank_eq.symm
  have hA : Module.finrank F A =
      Module.finrank F C + Module.finrank F (LinearMap.range X) := by
    have hrange : LinearMap.range X = A.map (Submodule.mkQ C) := by
      rw [t1Pullback_range, t1AQuotientToAmbient_range]
    have hinj : Function.Injective (t1AQuotientToAmbient t.C) :=
      t1AQuotientToAmbient_injective t.C
    have hrankQ : Module.finrank F (LinearMap.range (t1AQuotientToAmbient t.C)) =
        Module.finrank F (A ⧸ t.C) := LinearMap.finrank_range_of_inj hinj
    have hquot : Module.finrank F (A ⧸ t.C) + Module.finrank F t.C =
        Module.finrank F A := t.C.finrank_quotient_add_finrank
    have hrangeDim : Module.finrank F (LinearMap.range X) =
        Module.finrank F (A ⧸ t.C) := by
      rw [t1Pullback_range, hrankQ]
    have hCeq : Module.finrank F C = Module.finrank F t.C := hCdim
    rw [hCeq, hrangeDim]
    rw [add_comm]
    exact hquot.symm
  have hB : Module.finrank F (W n ⧸ B) =
      Module.finrank F (W n ⧸ H) + Module.finrank F (LinearMap.range X) := by
    have hker : LinearMap.ker X = B.comap H.subtype := t1Pullback_ker t
    have hBdim : Module.finrank F (LinearMap.ker X) = Module.finrank F B := by
      rw [hker]
      exact (Submodule.comapSubtypeEquivOfLe
        (t1AmbientH_containsB B t.K)).finrank_eq
    have hnull := LinearMap.finrank_range_add_finrank_ker X
    have hHdim : Module.finrank F H =
        Module.finrank F (LinearMap.range X) + Module.finrank F B := by
      rw [hBdim] at hnull
      exact hnull.symm
    have hH : Module.finrank F (W n ⧸ H) + Module.finrank F H =
        Module.finrank F (W n) := by
      simpa using H.finrank_quotient_add_finrank
    have hWB : Module.finrank F (W n ⧸ B) + Module.finrank F B =
        Module.finrank F (W n) := by
      simpa using B.finrank_quotient_add_finrank
    apply Nat.add_right_cancel (m := Module.finrank F B)
    calc
      Module.finrank F (W n ⧸ B) + Module.finrank F B =
          Module.finrank F (W n) := hWB
      _ = Module.finrank F (W n ⧸ H) + Module.finrank F H := hH.symm
      _ = Module.finrank F (W n ⧸ H) +
            (Module.finrank F (LinearMap.range X) + Module.finrank F B) := by
          rw [hHdim]
      _ = Module.finrank F (W n ⧸ H) + Module.finrank F (LinearMap.range X) +
            Module.finrank F B := by ac_rfl
  rw [hA, hB]
  simp [a6Order, C, H, X]
  ac_rfl

private theorem a6_sum3_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    ∑ a : α, ∑ b : β, ∑ c : γ, f a b c =
      ∑ c : γ, ∑ a : α, ∑ b : β, f a b c := by
  have h1 : ∑ a : α, ∑ b : β, ∑ c : γ, f a b c =
      ∑ b : β, ∑ a : α, ∑ c : γ, f a b c := Finset.sum_comm
  have h2 : ∑ b : β, ∑ a : α, ∑ c : γ, f a b c =
      ∑ b : β, ∑ c : γ, ∑ a : α, f a b c := by
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have h3 : ∑ b : β, ∑ c : γ, ∑ a : α, f a b c =
      ∑ c : γ, ∑ b : β, ∑ a : α, f a b c := Finset.sum_comm
  have h4 : ∑ c : γ, ∑ b : β, ∑ a : α, f a b c =
      ∑ c : γ, ∑ a : α, ∑ b : β, f a b c := by
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  exact h1.trans (h2.trans (h3.trans h4))

/-- One ordinary pair obeys the Hölder bound with cost `2^(3ij)`. -/
theorem a6_pair_fourth_le {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex) :
    uniformMean (fun M => Complex.normSq (DR6ComplexOrdinaryFilter A B f M) ^ 2) ≤
      (2 : ℝ) ^ (3 * (Module.finrank F A * Module.finrank F (W n ⧸ B))) *
        ∑ t : T1IndexTriple A B, a6DerivativeFourth A B t f := by
  classical
  rw [a6_uniform_translation A B f]
  let i := Module.finrank F A
  let j := Module.finrank F (W n ⧸ B)
  let cT : ℝ := Fintype.card (V d →ₗ[F] W n)
  let cN : ℝ := Fintype.card ((V d ⧸ A) →ₗ[F] B)
  let slice (T : V d →ₗ[F] W n) (N : (V d ⧸ A) →ₗ[F] B) : ℝ :=
    Complex.normSq (complexAmbientAffineRestrict A B T
      (DR6ComplexOrdinaryFilter A B f) N) ^ 2
  let deriv (T : V d →ₗ[F] W n) (N : (V d ⧸ A) →ₗ[F] B)
      (t : T1IndexTriple A B) : ℝ :=
    Complex.normSq (typedW6FourierDerivative (t1AmbientC t.C)
      (t1AmbientH t.K) (t1PullbackMap t)
      (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
      (t1OutputEquiv t N)) ^ 2
  have hpoint : ∑ T, ∑ N, slice T N ≤
      (2 : ℝ) ^ (3 * (i * j)) * ∑ T, ∑ N, ∑ t, deriv T N t := by
    have hineq (T : V d →ₗ[F] W n) (N : (V d ⧸ A) →ₗ[F] B) :
        slice T N ≤ (2 : ℝ) ^ (3 * (i * j)) * ∑ t, deriv T N t := by
      simpa [slice, deriv, i, j] using a6_pointwise_holder A B T f N
    calc
      ∑ T, ∑ N, slice T N ≤ ∑ T, ∑ N, ((2 : ℝ) ^ (3 * (i * j)) * ∑ t, deriv T N t) := by
        apply Finset.sum_le_sum
        intro T _
        apply Finset.sum_le_sum
        intro N _
        exact hineq T N
      _ = (2 : ℝ) ^ (3 * (i * j)) * ∑ T, ∑ N, ∑ t, deriv T N t := by
        symm
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun _ _ => ?_)
        rw [Finset.mul_sum]
  have hswap : ∑ T, ∑ N, ∑ t, deriv T N t = ∑ t, ∑ T, ∑ N, deriv T N t :=
    a6_sum3_comm deriv
  have hden : 0 < cT * cN := by
    dsimp [cT, cN]
    positivity
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hpoint
  have hfactor : (∑ T, ∑ N, ∑ t, deriv T N t) / (cT * cN) =
      ∑ t, a6DerivativeFourth A B t f := by
    rw [hswap]
    unfold a6DerivativeFourth deriv
    dsimp [cT, cN]
    rw [Finset.sum_div]
  calc
    _ ≤ ((2 : ℝ) ^ (3 * (i * j)) * ∑ T, ∑ N, ∑ t, deriv T N t) / (cT * cN) := hdiv
    _ = (2 : ℝ) ^ (3 * (i * j)) *
        ((∑ T, ∑ N, ∑ t, deriv T N t) / (cT * cN)) := by rw [mul_div_assoc]
    _ = (2 : ℝ) ^ (3 * (Module.finrank F A * Module.finrank F (W n ⧸ B))) *
        ∑ t, a6DerivativeFourth A B t f := by
      rw [hfactor]

/-- The averaged fourth power of one mixed derivative is nonnegative. -/
theorem a6DerivativeFourth_nonneg {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex) :
    0 ≤ a6DerivativeFourth A B t f := by
  unfold a6DerivativeFourth
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro _ _
    apply Finset.sum_nonneg
    intro _ _
    exact sq_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every triple of a nonzero ordinary pair has positive mixed order. -/
theorem a6_order_pos {n d : Nat} (p : dr6ActualNonzeroABPairs (n := n) (d := d))
    (t : T1IndexTriple p.1.1 p.1.2) : 0 < a6Order t := by
  have hsplit := a6_dimension_split t
  have hsum : 0 < Module.finrank F p.1.1 + Module.finrank F (W n ⧸ p.1.2) := by
    cases p.2 with
    | inl hA =>
      have hi : 0 < Module.finrank F p.1.1 := by
        have hne : Module.finrank F p.1.1 ≠ 0 := by
          intro hz
          exact hA ((Submodule.finrank_eq_zero).1 hz)
        omega
      omega
    | inr hB =>
      have hne : Module.finrank F (W n ⧸ p.1.2) ≠ 0 := by
        intro hz
        have hquot := (p.1.2).finrank_quotient_add_finrank
        have htop : Module.finrank F p.1.2 = Module.finrank F (W n) := by
          change Module.finrank F (W n ⧸ p.1.2) + Module.finrank F p.1.2 =
            Module.finrank F (W n) at hquot
          omega
        exact hB (Submodule.eq_top_of_finrank_eq htop)
      omega
  have hge : Module.finrank F (LinearMap.range (t1PullbackMap t)) ≤ a6Order t := by
    dsimp [a6Order]
    exact Nat.le_add_left _ _
  have hspos : 0 < a6Order t + Module.finrank F (LinearMap.range (t1PullbackMap t)) := by
    rw [← hsplit]
    exact hsum
  cases Nat.eq_zero_or_pos (a6Order t) with
  | inr hpos => exact hpos
  | inl hz =>
      have hr : Module.finrank F (LinearMap.range (t1PullbackMap t)) = 0 :=
        Nat.le_antisymm (by simpa [hz] using hge) (Nat.zero_le _)
      rw [hz, hr, Nat.zero_add] at hspos
      exact absurd hspos (lt_irrefl 0)

/-- Codimension of `B` is the ambient rank minus `finrank B`. -/
theorem a6_codim_eq {n : Nat} (B : Submodule F (W n)) :
    Module.finrank F (V n) - Module.finrank F B =
      Module.finrank F (W n ⧸ B) := by
  have hpi : Module.finrank F (V n) = n := by
    simpa using (Module.finrank_fin_fun (K := F) n)
  have hW : Module.finrank F (W n) = n := by
    simpa using (Module.finrank_fin_fun (K := F) n)
  have hsum := B.finrank_quotient_add_finrank
  change Module.finrank F (W n ⧸ B) + Module.finrank F B =
    Module.finrank F (W n) at hsum
  omega

/-- A high-degree ordinary filter has fourth moment zero. -/
theorem a6_fourth_moment_zero_of_high {n d D : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (hhigh : D < Module.finrank F A ∨ D < Module.finrank F (W n ⧸ B)) :
    uniformMean (fun M => Complex.normSq (DR6ComplexOrdinaryFilter A B f M) ^ 2) = 0 := by
  unfold uniformMean
  have hfun : ∀ M, Complex.normSq (DR6ComplexOrdinaryFilter A B f M) ^ 2 = 0 := by
    intro M
    rw [a6_ordinaryFilter_zero_of_high_degree A B f hsupport hhigh M]
    simp
  simp [hfun]

/-- `2^a * (2^b * S) = 2^(a+b) * S`. -/
theorem a6_pow_factor (a b : Nat) (S : ℝ) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ b * S) = (2 : ℝ) ^ (a + b) * S := by
  rw [← mul_assoc, ← pow_add]

/-- One mixed derivative absorbs the Hölder and degree weight into `2^(24Dt)`. -/
theorem a6_scaled_triple_le {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (f : BinaryMatrix n d → Complex)
    (hi : Module.finrank F A ≤ D) (hj : Module.finrank F (W n ⧸ B) ≤ D) :
    (2 : ℝ) ^ (7 * D * (Module.finrank F A + Module.finrank F (W n ⧸ B)) +
        3 * (Module.finrank F A * Module.finrank F (W n ⧸ B))) *
      a6DerivativeFourth A B t f ≤
    (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth A B t f := by
  let i := Module.finrank F A
  let j := Module.finrank F (W n ⧸ B)
  have hle : Module.finrank F (LinearMap.range (t1PullbackMap t)) ≤ a6Order t := by
    dsimp [a6Order]
    exact Nat.le_add_left _ _
  have hs : i + j = a6Order t +
      Module.finrank F (LinearMap.range (t1PullbackMap t)) := by
    simpa [i, j] using a6_dimension_split t
  have htwo : i + j ≤ 2 * a6Order t := by
    rw [hs, two_mul]
    exact Nat.add_le_add_left hle _
  have hexp := a6_exponent_le D i j (a6Order t) hi hj htwo
  have hmul : 7 * D * (i + j) + 3 * (i * j) =
      7 * D * (i + j) + 3 * i * j := by ring
  have hbase : (2 : ℝ) ^ (7 * D * (i + j) + 3 * (i * j)) ≤
      (2 : ℝ) ^ (24 * D * a6Order t) := by
    rw [hmul]
    exact pow_le_pow_right₀ (by norm_num) hexp
  exact mul_le_mul_of_nonneg_right hbase (a6DerivativeFourth_nonneg A B t f)

/-- One nonzero ordinary pair is bounded by its positive-order mixed derivatives. -/
theorem a6_one_pair_energy_le {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (p : dr6ActualNonzeroABPairs (n := n) (d := d)) :
    (2 : ℝ) ^ (7 * D * (Module.finrank F p.1.1 +
        (Module.finrank F (V n) - Module.finrank F p.1.2))) *
      uniformMean (fun M =>
        Complex.normSq (DR6ComplexOrdinaryFilter p.1.1 p.1.2 f M) ^ 2) ≤
    ∑ t : T1IndexTriple p.1.1 p.1.2,
      if 0 < a6Order t then
        (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
      else 0 := by
  classical
  let A := p.1.1
  let B := p.1.2
  let i := Module.finrank F A
  let j := Module.finrank F (W n ⧸ B)
  have hcodim : Module.finrank F (V n) - Module.finrank F B = j := by
    simpa [i, j, A, B] using a6_codim_eq B
  by_cases hhigh : D < i ∨ D < j
  · have hzero := a6_fourth_moment_zero_of_high A B f hsupport hhigh
    rw [hcodim, hzero]
    simp
    apply Finset.sum_nonneg
    intro t _
    by_cases ho : 0 < a6Order t
    · rw [if_pos ho]
      exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (a6DerivativeFourth_nonneg A B t f)
    · rw [if_neg ho]
  · have hi : i ≤ D := by
      have : ¬ D < i := by
        intro h
        exact hhigh (Or.inl h)
      omega
    have hj : j ≤ D := by
      have : ¬ D < j := by
        intro h
        exact hhigh (Or.inr h)
      omega
    have hmean := a6_pair_fourth_le A B f
    rw [hcodim]
    calc
      (2 : ℝ) ^ (7 * D * (i + j)) *
          uniformMean (fun M => Complex.normSq (DR6ComplexOrdinaryFilter A B f M) ^ 2) ≤
        (2 : ℝ) ^ (7 * D * (i + j)) * ((2 : ℝ) ^ (3 * (i * j)) *
          ∑ t, a6DerivativeFourth A B t f) :=
        mul_le_mul_of_nonneg_left hmean (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = (2 : ℝ) ^ (7 * D * (i + j) + 3 * (i * j)) * ∑ t, a6DerivativeFourth A B t f :=
        a6_pow_factor (7 * D * (i + j)) (3 * (i * j)) _
      _ = ∑ t, (2 : ℝ) ^ (7 * D * (i + j) + 3 * (i * j)) * a6DerivativeFourth A B t f := by
        rw [Finset.mul_sum]
      _ ≤ ∑ t, (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth A B t f := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        simpa [i, j, A, B] using a6_scaled_triple_le (D := D) t f hi hj
      _ = ∑ t, if 0 < a6Order t then
            (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth A B t f else 0 := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        have ho : 0 < a6Order t := a6_order_pos p t
        simp [ho]

/-- Manuscript A6: the DR6 fourth moment is the degree term plus the weighted
mixed-derivative sum. Orders above the degree contribute zero. -/
theorem manuscript_A6 {n d D : Nat} (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) :
    uniformMean (fun M => Complex.normSq (f M) ^ 2) / 162 ≤
      (2 : ℝ) ^ (6 * D * D) * (uniformMean (fun M => Complex.normSq (f M))) ^ 2 +
        ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
          ∑ t : T1IndexTriple p.1.1 p.1.2,
            if 0 < a6Order t then
              (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
            else 0 := by
  have hDR6 := dr6_actual_complex_fourth_moment_over_162_le (n := n) (d := d) (D := D) f hsupport
  have henergy : dr6ActualWeightedOrdinaryFilterEnergy (n := n) (d := d) (D := D) f ≤
      ∑ p : dr6ActualNonzeroABPairs (n := n) (d := d),
        ∑ t : T1IndexTriple p.1.1 p.1.2,
          if 0 < a6Order t then
            (2 : ℝ) ^ (24 * D * a6Order t) * a6DerivativeFourth p.1.1 p.1.2 t f
          else 0 := by
    unfold dr6ActualWeightedOrdinaryFilterEnergy
    refine Finset.sum_le_sum (fun p _ => a6_one_pair_energy_le f hsupport p)
  exact le_trans hDR6 (add_le_add_right henergy _)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A6Transfer
