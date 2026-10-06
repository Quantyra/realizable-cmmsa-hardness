import PvNP.RealizableHardness.ActualBinaryMatrixHC46CommonDerivative
import PvNP.RealizableHardness.ActualBinaryMatrixHC46FourierA16
import PvNP.RealizableHardness.ActualBinaryMatrixHC46MixedPeeling

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46CommonA16

open BinaryMatrixFourier BinaryMatrixComplexA14
open ActualBinaryMatrixHC46CommonDerivative
open ActualBinaryMatrixHC46FourierA16
open ActualBinaryMatrixHC46MixedPeeling
open ActualBinaryMatrixHC46FinitePeeling
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private def complexRealDot (z w : Complex) : Real :=
  z.re * w.re + z.im * w.im

private theorem uniformMean_sum {ι : Type} (s : Finset ι)
    {n d : Nat} (f : ι -> BinaryMatrix n d -> Real) :
    uniformMean (fun M => ∑ i ∈ s, f i M) =
      ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_comm]
  rw [← Finset.sum_mul]

private theorem uniformMean_complexRealDot_sum_left {ι : Type}
    (s : Finset ι) {n d : Nat}
    (f : ι -> BinaryMatrix n d -> Complex)
    (g : BinaryMatrix n d -> Complex) :
    uniformMean (fun M => complexRealDot (∑ i ∈ s, f i M) (g M)) =
      ∑ i ∈ s, uniformMean (fun M => complexRealDot (f i M) (g M)) := by
  have hfun : (fun M => complexRealDot (∑ i ∈ s, f i M) (g M)) =
      fun M => ∑ i ∈ s, complexRealDot (f i M) (g M) := by
    funext M
    dsimp [complexRealDot]
    simp only [Complex.re_sum, Complex.im_sum, Finset.sum_mul]
    rw [Finset.sum_add_distrib]
  rw [hfun, uniformMean_sum]

private theorem uniformMean_complex_normSq_add {n d : Nat}
    (f g : BinaryMatrix n d -> Complex) :
    uniformMean (fun M => Complex.normSq (f M + g M)) =
      uniformMean (fun M => Complex.normSq (f M)) +
        uniformMean (fun M => Complex.normSq (g M)) +
          2 * uniformMean (fun M => complexRealDot (f M) (g M)) := by
  have hsum : (∑ M : BinaryMatrix n d, Complex.normSq (f M + g M)) =
      (∑ M : BinaryMatrix n d, Complex.normSq (f M)) +
        (∑ M : BinaryMatrix n d, Complex.normSq (g M)) +
          2 * (∑ M : BinaryMatrix n d, complexRealDot (f M) (g M)) := by
    calc
      (∑ M : BinaryMatrix n d, Complex.normSq (f M + g M)) =
          ∑ M : BinaryMatrix n d,
            (Complex.normSq (f M) + Complex.normSq (g M) +
              2 * complexRealDot (f M) (g M)) := by
                apply Finset.sum_congr rfl
                intro M hM
                simp [Complex.normSq_apply, complexRealDot]
                ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  unfold uniformMean
  rw [hsum]
  ring

/-- Finite complex energy additivity follows from the real-part Hermitian
cross term, which is exactly the term appearing in `Complex.normSq`. -/
theorem complexEnergy_finite_sum_of_orthogonal {ι : Type}
    (s : Finset ι) {n d : Nat}
    (f : ι -> BinaryMatrix n d -> Complex)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      uniformMean (fun M => complexRealDot (f i M) (f j M)) = 0) :
    uniformMean (fun M => Complex.normSq (∑ i ∈ s, f i M)) =
      ∑ i ∈ s, uniformMean (fun M => Complex.normSq (f i M)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [uniformMean]
  | @insert a s ha ih =>
      have hsum : (fun M => ∑ i ∈ insert a s, f i M) =
          fun M => f a M + ∑ i ∈ s, f i M := by
        funext M
        simp [ha]
      have hsumSq := congrArg
        (fun g => uniformMean (fun M => Complex.normSq (g M))) hsum
      rw [hsumSq, uniformMean_complex_normSq_add]
      have hcross : uniformMean (fun M =>
          complexRealDot (∑ i ∈ s, f i M) (f a M)) = 0 := by
        rw [uniformMean_complexRealDot_sum_left]
        apply Finset.sum_eq_zero
        intro i hi
        have hia : i ≠ a := by
          intro h
          subst i
          exact ha hi
        have hmem : i ∈ insert a s := Finset.mem_insert_of_mem hi
        have hamem : a ∈ insert a s := Finset.mem_insert_self _ _
        exact horth i hmem a hamem hia
      have hcross' : uniformMean (fun M =>
          complexRealDot (f a M) (∑ i ∈ s, f i M)) = 0 := by
        have hcomm : (fun M => complexRealDot (f a M) (∑ i ∈ s, f i M)) =
            (fun M => complexRealDot (∑ i ∈ s, f i M) (f a M)) := by
          funext M
          dsimp [complexRealDot]
          ring
        rw [hcomm, hcross]
      rw [ih (by
        intro i hi j hj hij
        exact horth i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij), hcross']
      simp [ha]

/-- The complex rank filters reconstruct the initial function over the
finite set of Fourier ranks that actually occur on its matrix space. -/
theorem complexRankProjection_reconstruct {n d : Nat}
    (f : BinaryMatrix n d -> Complex) (M : BinaryMatrix n d) :
    (∑ i ∈ (Finset.univ : Finset (BinaryMatrix n d)).image
        (fun Y => Y.rank), complexRankProjection i f M) = f M := by
  apply Complex.ext
  · rw [Complex.re_sum]
    simp_rw [complexRankProjection_re]
    exact ActualBinaryMatrixHC46FourierA16.rankProjection_reconstruct
      (fun X => (f X).re) M
  · rw [Complex.im_sum]
    simp_rw [complexRankProjection_im]
    exact ActualBinaryMatrixHC46FourierA16.rankProjection_reconstruct
      (fun X => (f X).im) M

/-- Applying the projection-free mixed derivative to the Fourier
reconstruction gives the finite sum over the original input ranks. The
rank shift belongs to the output support argument and is not used here. -/
theorem commonMixedDerivativeChain_input_rank_reconstruct {n d k l : Nat}
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2)
    (M : BinaryMatrix n d) :
    (∑ i ∈ (Finset.univ : Finset (BinaryMatrix (n + l) (d + k))).image
        (fun Y => Y.rank),
      commonMixedDerivativeChain k l
        (complexRankProjection i f) tLine tHyp M) =
      commonMixedDerivativeChain k l f tLine tHyp M := by
  let ranks := (Finset.univ : Finset (BinaryMatrix (n + l) (d + k))).image
    (fun Y => Y.rank)
  have hdecomp : (fun X => ∑ i ∈ ranks, complexRankProjection i f X) = f := by
    funext X
    exact complexRankProjection_reconstruct f X
  have happly := congrArg
    (fun g => commonMixedDerivativeChain k l g tLine tHyp) hdecomp
  have hsum := commonMixedDerivativeChain_finset_sum ranks
    (fun i => complexRankProjection i f) tLine tHyp
  calc
    (∑ i ∈ ranks, commonMixedDerivativeChain k l
        (complexRankProjection i f) tLine tHyp M) =
      commonMixedDerivativeChain k l
        (fun X => ∑ i ∈ ranks, complexRankProjection i f X) tLine tHyp M := by
          exact (congrFun hsum M).symm
    _ = commonMixedDerivativeChain k l f tLine tHyp M := congrFun happly M

/-- Contributions from distinct original input ranks are orthogonal after
the mixed operator. Low ranks vanish; surviving ranks are identified with
the residual-rank A16 orthogonality theorem. -/
theorem commonMixedDerivativeChain_input_rank_orthogonal
    {n d r s k l : Nat} (hrs : r ≠ s)
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2) :
    uniformMean (fun M => complexRealDot
      (commonMixedDerivativeChain k l (complexRankProjection r f) tLine tHyp M)
      (commonMixedDerivativeChain k l (complexRankProjection s f) tLine tHyp M)) = 0 := by
  by_cases hrlo : r < k + l
  · rw [commonMixedDerivativeChain_low_rank_zero f tLine tHyp hrlo]
    simp [uniformMean, complexRealDot]
  · by_cases hslo : s < k + l
    · rw [commonMixedDerivativeChain_low_rank_zero f tLine tHyp hslo]
      simp [uniformMean, complexRealDot]
    · have hrge : k + l <= r := by omega
      have hsge : k + l <= s := by omega
      let r' := r - (k + l)
      let s' := s - (k + l)
      have hrindex : r' + (k + l) = r := by
        dsimp [r']
        exact Nat.sub_add_cancel hrge
      have hsindex : s' + (k + l) = s := by
        dsimp [s']
        exact Nat.sub_add_cancel hsge
      have hrs' : r' ≠ s' := by
        intro heq
        apply hrs
        omega
      have hrproj : complexRankProjection r f =
          complexRankProjection (r' + (k + l)) f := by
        rw [hrindex]
      have hsproj : complexRankProjection s f =
          complexRankProjection (s' + (k + l)) f := by
        rw [hsindex]
      have hrchain :
          commonMixedDerivativeChain k l (complexRankProjection r f) tLine tHyp =
            mixedCoordinateDerivativeChain r' k l
              (complexRankProjection (r' + (k + l)) f) tLine tHyp := by
        calc
          commonMixedDerivativeChain k l (complexRankProjection r f) tLine tHyp =
              commonMixedDerivativeChain k l
                (complexRankProjection (r' + (k + l)) f) tLine tHyp := by
                  exact congrArg (fun g => commonMixedDerivativeChain k l g tLine tHyp)
                    hrproj
          _ = mixedCoordinateDerivativeChain r' k l
                (complexRankProjection (r' + (k + l)) f) tLine tHyp :=
                  (mixedCoordinateDerivativeChain_eq_common_assoc
                    (r := r') f tLine tHyp).symm
      have hschain :
          commonMixedDerivativeChain k l (complexRankProjection s f) tLine tHyp =
            mixedCoordinateDerivativeChain s' k l
              (complexRankProjection (s' + (k + l)) f) tLine tHyp := by
        calc
          commonMixedDerivativeChain k l (complexRankProjection s f) tLine tHyp =
              commonMixedDerivativeChain k l
                (complexRankProjection (s' + (k + l)) f) tLine tHyp := by
                  exact congrArg (fun g => commonMixedDerivativeChain k l g tLine tHyp)
                    hsproj
          _ = mixedCoordinateDerivativeChain s' k l
                (complexRankProjection (s' + (k + l)) f) tLine tHyp :=
                  (mixedCoordinateDerivativeChain_eq_common_assoc
                    (r := s') f tLine tHyp).symm
      rw [hrchain, hschain]
      exact ActualBinaryMatrixHC46FourierA16.mixedCoordinateDerivativeChain_complex_orthogonal
        hrs' f tLine tHyp

/-- The true finite Fourier decomposition of the unprojected common mixed
operator is energy preserving over the original input ranks. -/
theorem commonMixedDerivativeChain_complex_energy_reconstruct
    {n d k l : Nat}
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2) :
    uniformMean (fun M => Complex.normSq
      (commonMixedDerivativeChain k l f tLine tHyp M)) =
      ∑ i ∈ (Finset.univ : Finset (BinaryMatrix (n + l) (d + k))).image
        (fun Y => Y.rank),
        uniformMean (fun M => Complex.normSq
          (commonMixedDerivativeChain k l
            (complexRankProjection i f) tLine tHyp M)) := by
  let ranks := (Finset.univ : Finset (BinaryMatrix (n + l) (d + k))).image
    (fun Y => Y.rank)
  have hdecomp : (fun X => ∑ i ∈ ranks, complexRankProjection i f X) = f := by
    funext X
    exact complexRankProjection_reconstruct f X
  have hsum := commonMixedDerivativeChain_finset_sum ranks
    (fun i => complexRankProjection i f) tLine tHyp
  have hrepr : commonMixedDerivativeChain k l f tLine tHyp =
      fun M => ∑ i ∈ ranks,
        commonMixedDerivativeChain k l (complexRankProjection i f) tLine tHyp M := by
    calc
      commonMixedDerivativeChain k l f tLine tHyp =
          commonMixedDerivativeChain k l
            (fun X => ∑ i ∈ ranks, complexRankProjection i f X) tLine tHyp := by
              exact congrArg (fun g => commonMixedDerivativeChain k l g tLine tHyp)
                hdecomp.symm
      _ = _ := hsum
  rw [hrepr]
  apply complexEnergy_finite_sum_of_orthogonal
  intro i hi j hj hij
  exact commonMixedDerivativeChain_input_rank_orthogonal hij f tLine tHyp

/-- Each pair of distinct input-rank contributions to the common mixed
operator has zero real Hermitian cross-energy, by the actual mixed A14
support theorem. -/
theorem commonMixedDerivativeChain_rank_orthogonal {n d r s k l : Nat}
    (hrs : r ≠ s)
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2) :
    uniformMean (fun M => complexRealDot
      (commonMixedDerivativeChain k l
        (complexRankProjection ((r + l) + k) f) tLine tHyp M)
      (commonMixedDerivativeChain k l
        (complexRankProjection ((s + l) + k) f) tLine tHyp M)) = 0 := by
  have h := ActualBinaryMatrixHC46FourierA16.mixedCoordinateDerivativeChain_complex_orthogonal
    (r := r) (s := s) hrs f tLine tHyp
  have hr := mixedCoordinateDerivativeChain_eq_common_assoc
    (r := r) f tLine tHyp
  have hs := mixedCoordinateDerivativeChain_eq_common_assoc
    (r := s) f tLine tHyp
  have h' := h
  rw [hr, hs] at h'
  simpa [complexRealDot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

/-- Parseval-style finite level sum for the complex common mixed derivative.
The cross terms vanish by the rank support just proved; no orthogonality
premise is assumed. -/
theorem commonMixedDerivativeChain_complex_energy_sum {n d k l q : Nat}
    (f : BinaryMatrix (n + l) (d + k) -> Complex)
    (tLine : Fin k -> Fin (n + l) -> ZMod 2)
    (tHyp : Fin l -> Fin d -> ZMod 2) :
    uniformMean (fun M => Complex.normSq
      (∑ r ∈ Finset.range (q + 1),
        commonMixedDerivativeChain k l
          (complexRankProjection ((r + l) + k) f) tLine tHyp M)) =
      ∑ r ∈ Finset.range (q + 1),
        uniformMean (fun M => Complex.normSq
          (commonMixedDerivativeChain k l
            (complexRankProjection ((r + l) + k) f) tLine tHyp M)) := by
  apply complexEnergy_finite_sum_of_orthogonal
  intro r hr s hs hrs
  exact commonMixedDerivativeChain_rank_orthogonal hrs f tLine tHyp

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46CommonA16
