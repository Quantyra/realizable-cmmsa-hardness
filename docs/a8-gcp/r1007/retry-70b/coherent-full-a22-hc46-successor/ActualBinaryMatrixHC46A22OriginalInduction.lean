import PvNP.RealizableHardness.ActualBinaryMatrixHC46A22ParentFactorization
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A21DyadicMoment

/-! Original all-spaces A22. The positive-order bounds use only the strict
lower-level induction hypothesis. The beta-one duality estimate is applied
only after every original influence has been proved to be at most the energy. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OriginalInduction
open ActualBinaryMatrixHC46RealQNorm ActualBinaryMatrixHC46RealQTransport
open ActualBinaryMatrixHC46A22ParentFactorization
open ActualBinaryMatrixHC46A21DyadicMoment
open ActualBinaryMatrixHC46A18OriginalGlobalInduction
open ActualBinaryMatrixHC46A18InductionBounds
open ActualBinaryMatrixHC46A12InfluenceBound
open ActualBinaryMatrixHC46A12FourthMoment
open ActualBinaryMatrixHC46A7Transfer ActualBinaryMatrixHC46A7HybridW6Transport
open ActualTypedABCanonicalDCollapse
open BinaryMatrixFourier BinaryMatrixA1Complex BinaryMatrixComplexA14 BinaryMatrixComplexA15
open ActualFiniteDegreeFourierReconstruction
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

def a22Energy {n d : Nat} (f : BinaryMatrix n d → Complex) : Real :=
  uniformMean (fun M => Complex.normSq (f M))

theorem a22_energy_nonneg {n d : Nat} (f : BinaryMatrix n d → Complex) :
    0 ≤ a22Energy f := a21_second_nonneg f

theorem a22_projection_coefficient {n d j : Nat} (f : BinaryMatrix n d → Complex)
    (Y : BinaryMatrix n d) :
    complexFourierCoeff (complexRankProjection j f) Y =
      if Y.rank = j then complexFourierCoeff f Y else 0 := by
  apply Complex.ext
  · rw [complexFourierCoeff_re]
    simp_rw [complexRankProjection_re]
    rw [fourierCoeff_rankProjection]
    split_ifs <;> simp [complexFourierCoeff_re]
  · rw [complexFourierCoeff_im]
    simp_rw [complexRankProjection_im]
    rw [fourierCoeff_rankProjection]
    split_ifs <;> simp [complexFourierCoeff_im]

theorem a22_projection_energy_mass {n d j : Nat} (f : BinaryMatrix n d → Complex) :
    a22Energy (complexRankProjection j f) =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter (fun Y => Y.rank = j),
        Complex.normSq (complexFourierCoeff f Y) := by
  rw [a22Energy, complex_fourier_parseval]
  simp_rw [a22_projection_coefficient]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  split_ifs <;> simp

/-- Exact orthogonal projection pairing, not merely idempotence. -/
theorem a22_projection_pairing {n d j : Nat} (f : BinaryMatrix n d → Complex) :
    (∑ M : BinaryMatrix n d, star (complexRankProjection j f M) * f M) /
        (Fintype.card (BinaryMatrix n d) : Complex) =
      (a22Energy (complexRankProjection j f) : Complex) := by
  classical
  let S := (Finset.univ : Finset (BinaryMatrix n d)).filter (fun Y => Y.rank = j)
  have hterm (Y : BinaryMatrix n d) :
      (∑ M : BinaryMatrix n d,
        star (complexFourierCoeff f Y) * (character Y M : Complex) * f M) /
          (Fintype.card (BinaryMatrix n d) : Complex) =
      star (complexFourierCoeff f Y) * complexFourierCoeff f Y := by
    unfold complexFourierCoeff
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  calc
    _ = (∑ M : BinaryMatrix n d, ∑ Y ∈ S,
        star (complexFourierCoeff f Y) * (character Y M : Complex) * f M) /
          (Fintype.card (BinaryMatrix n d) : Complex) := by
      congr 1
      apply Finset.sum_congr rfl
      intro M _
      simp only [complexRankProjection, S, star_sum, star_mul', Complex.star_def,
        Complex.conj_ofReal, Finset.sum_mul]
    _ = ∑ Y ∈ S, star (complexFourierCoeff f Y) * complexFourierCoeff f Y := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro Y _
      exact hterm Y
    _ = (a22Energy (complexRankProjection j f) : Complex) := by
      rw [a22_projection_energy_mass]
      simp only [S, Complex.ofReal_sum, Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self]

theorem a22_projection_energy_le {n d j : Nat} (f : BinaryMatrix n d → Complex) :
    a22Energy (complexRankProjection j f) ≤ a22Energy f := by
  rw [a22_projection_energy_mass, a22Energy, complex_fourier_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Complex.normSq_nonneg _)

theorem a22_zero_cost_energy {n d : Nat} (A : Submodule F (V d))
    (B : Submodule F (W n)) (T : V d →ₗ[F] W n)
    (f : BinaryMatrix n d → Complex)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) = 0) :
    a12Energy A B f T = a22Energy f := by
  have hA0 : Module.finrank F A = 0 := by omega
  have hB0 : Module.finrank F (W n ⧸ B) = 0 := by omega
  have hA : A = ⊥ := Submodule.finrank_eq_zero.mp hA0
  have hBdim : Module.finrank F B = Module.finrank F (⊤ : Submodule F (W n)) := by
    have h := B.finrank_quotient_add_finrank
    rw [hB0, zero_add] at h
    rw [finrank_top]
    exact h
  have hB : B = ⊤ := Submodule.eq_of_le_of_finrank_eq le_top hBdim
  subst A
  subst B
  have hs := a7_zero_order_component T f
  change a12Energy ⊥ ⊤ f T ^ 2 = a22Energy f ^ 2 at hs
  exact (sq_eq_sq₀ (a12_energy_nonneg ⊥ ⊤ f T) (a22_energy_nonneg f)).mp hs

theorem a22_dyadic_even {p : Nat} (hp : 2 ≤ p) (hdyadic : ∃ k : Nat, p = 2 ^ k) :
    1 ≤ p / 2 ∧ p = 2 * (p / 2) := by
  obtain ⟨k, rfl⟩ := hdyadic
  have hk : k ≠ 0 := by intro hz; simp [hz] at hp
  obtain ⟨j, rfl⟩ : ∃ j : Nat, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_left _ (by decide : 0 < (2 : Nat))]
  constructor
  · have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
    omega
  · omega

/-- Honest beta-one A23: the influence hypothesis is supplied only by a
proved energy comparison in the A22 induction. Natural powers avoid division
by a square root, including the p=2 endpoint. -/
theorem a22_dual_energy_of_influences {n d j p : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex) (hp : 2 ≤ p)
    (hdyadic : ∃ k : Nat, p = 2 ^ k)
    (heps : 0 ≤ eps) (hnorm : realQNorm (pConjugate p) f ≤ eps)
    (hinfl : OriginalActualInfluenceThrough j
      (a22Energy (complexRankProjection j f)) (complexRankProjection j f)) :
    a22Energy (complexRankProjection j f) ≤ (2 : Real) ^ (420 * j ^ 2 * p) * eps ^ 2 := by
  let h := complexRankProjection j f
  let E := a22Energy h
  have hE0 : 0 ≤ E := a22_energy_nonneg h
  by_cases hE : E = 0
  · change E ≤ _
    rw [hE]
    positivity
  have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hE)
  obtain ⟨hm, hpEven⟩ := a22_dyadic_even hp hdyadic
  let m := p / 2
  have hmpos : 0 < m := by dsimp [m]; omega
  have hsub : 1 + (m - 1) = m := by omega
  have hsupport := complexRankProjection_supportedThrough le_rfl f
  have hglobal := actual_A18_original_global (r := j) h hsupport hinfl
  have hscale : a18BudgetScale j j E = (2 : Real) ^ (10 * j ^ 2) * E := by
    unfold a18BudgetScale
    congr 1
    congr 1
    ring
  have hglobal' : UpToActualNormSqGlobal j ((2 : Real) ^ (10 * j ^ 2) * E) h := by
    simpa only [hscale] using hglobal
  have hmoment := manuscript_A21_actual h hsupport hglobal' hp hdyadic
  have hmoment' : lpMoment p (fun M => ‖h M‖) ≤
      (2 : Real) ^ (200 * j ^ 2 * p ^ 2 + (10 * j ^ 2) * (m - 1)) * E ^ m := by
    calc
      _ ≤ (2 : Real) ^ (200 * j ^ 2 * p ^ 2) * E *
          ((2 : Real) ^ (10 * j ^ 2) * E) ^ (m - 1) := hmoment
      _ = _ := by
        rw [mul_pow ((2 : Real) ^ (10 * j ^ 2)) E (m - 1), ← pow_mul]
        rw [← hsub]
        simp only [pow_add, pow_one]
        ring
  have hholder := realQNorm_holder_nat_pow hp h f
  rw [a22_projection_pairing, Complex.norm_real, Real.norm_of_nonneg hE0] at hholder
  have hholderMoment : E ^ p ≤ lpMoment p (fun M => ‖h M‖) *
      realQNorm (pConjugate p) f ^ p := by
    simpa [lpMoment, uniformMean, abs_of_nonneg (norm_nonneg _)] using hholder
  have hmoment0 : 0 ≤ lpMoment p (fun M => ‖h M‖) := by
    unfold lpMoment uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) _))
      (Nat.cast_nonneg _)
  have hholder' : E ^ p ≤ lpMoment p (fun M => ‖h M‖) * eps ^ p := by
    apply hholderMoment.trans
    apply mul_le_mul_of_nonneg_left _ hmoment0
    exact pow_le_pow_left₀ (realQNorm_nonneg _ _) hnorm p
  have hexp : 200 * j ^ 2 * p ^ 2 + (10 * j ^ 2) * (m - 1) ≤
      (420 * j ^ 2 * p) * m := by
    have hpm : p = 2 * m := hpEven
    nlinarith
  have hcoefficient : (2 : Real) ^ (200 * j ^ 2 * p ^ 2 + (10 * j ^ 2) * (m - 1)) ≤
      ((2 : Real) ^ (420 * j ^ 2 * p)) ^ m := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hexp
  have hpower : E ^ m * E ^ m ≤ E ^ m *
      ((2 : Real) ^ (420 * j ^ 2 * p) * eps ^ 2) ^ m := by
    calc
      E ^ m * E ^ m = E ^ p := by
        rw [hpEven, Nat.mul_comm 2 (p / 2), pow_mul E m 2, pow_two]
      _ ≤ lpMoment p (fun M => ‖h M‖) * eps ^ p := hholder'
      _ ≤ ((2 : Real) ^ (200 * j ^ 2 * p ^ 2 + (10 * j ^ 2) * (m - 1)) * E ^ m) *
          eps ^ p := mul_le_mul_of_nonneg_right hmoment' (pow_nonneg heps _)
      _ ≤ (((2 : Real) ^ (420 * j ^ 2 * p)) ^ m * E ^ m) * eps ^ p := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg heps _)
        exact mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hE0 _)
      _ = _ := by
        rw [hpEven, pow_mul eps 2 m,
          mul_pow ((2 : Real) ^ (420 * j ^ 2 * p)) (eps ^ 2) m]
        ring
  have hcancel := (mul_le_mul_left (pow_pos hEpos m)).mp hpower
  exact (pow_le_pow_iff_left₀ hE0 (by positivity) (Nat.ne_of_gt hmpos)).mp hcancel

theorem a22_positive_exponent {j p : Nat} (hj : 1 ≤ j) (hp : 2 ≤ p) :
    500 * (j - 1) ^ 2 * p + 6 * j ≤ 500 * j ^ 2 * p := by
  have hsub : j - 1 + 1 = j := Nat.sub_add_cancel hj
  nlinarith

/-- Complete original A22, simultaneously over all finite binary spaces.
Every positive-order derivative is covered by the actual parent factorization;
the zero-order energy is handled before invoking the conditional dual estimate. -/
theorem manuscript_A22_actual {n d j p : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex)
    (hglobal : UpToActualLqGlobal j (pConjugate p) eps f)
    (hp : 2 ≤ p) (hdyadic : ∃ k : Nat, p = 2 ^ k) :
    OriginalActualInfluenceThrough j ((2 : Real) ^ (500 * j ^ 2 * p) * eps ^ 2)
      (complexRankProjection j f) := by
  have hall : ∀ level : Nat, ∀ {n' d' : Nat} {eta : Real}
      (g : BinaryMatrix n' d' → Complex),
      UpToActualLqGlobal level (pConjugate p) eta g →
      OriginalActualInfluenceThrough level ((2 : Real) ^ (500 * level ^ 2 * p) * eta ^ 2)
        (complexRankProjection level g) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro n' d' eta g hg
      have heta := UpToActualLqGlobal_parameter_nonneg g hg
      have hnorm := UpToActualLqGlobal_whole g hg
      let E := a22Energy (complexRankProjection level g)
      let B := (2 : Real) ^ (500 * (level - 1) ^ 2 * p + 6 * level) * eta ^ 2
      have hpositive : ∀ (A : Submodule F (V d')) (H : Submodule F (W n'))
          (T : V d' →ₗ[F] W n'),
          Module.finrank F A + Module.finrank F (W n' ⧸ H) ≤ level →
          0 < Module.finrank F A + Module.finrank F (W n' ⧸ H) →
          a12Energy A H (complexRankProjection level g) T ≤ B := by
        intro A H T hcost hpos
        have hlevel : 1 ≤ level := by omega
        refine a22_positive_parent_from_lowerIH g hlevel hp hg ?_ A H T hcost hpos
        intro n'' d'' theta u hu
        exact ih (level - 1) (by omega) u hu
      have hclose : ∀ bound : Real, E ≤ bound → B ≤ bound →
          OriginalActualInfluenceThrough level bound (complexRankProjection level g) := by
        intro bound hE hB A H T hcost
        by_cases hz : Module.finrank F A + Module.finrank F (W n' ⧸ H) = 0
        · rw [a22_zero_cost_energy A H T _ hz]
          exact hE
        · exact (hpositive A H T hcost (Nat.pos_of_ne_zero hz)).trans hB
      by_cases hlevel : level = 0
      · subst level
        have hEall : OriginalActualInfluenceThrough 0 E (complexRankProjection 0 g) := by
          intro A H T hcost
          rw [a22_zero_cost_energy A H T _ (by omega)]
        have hE := a22_dual_energy_of_influences g hp hdyadic heta hnorm hEall
        intro A H T hcost
        rw [a22_zero_cost_energy A H T _ (by omega)]
        simpa only [Nat.zero_pow (by decide : 0 < (2 : Nat)), zero_mul, pow_zero, one_mul] using hE
      · have hB : B ≤ (2 : Real) ^ (500 * level ^ 2 * p) * eta ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg eta)
          exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2)
            (a22_positive_exponent (by omega) hp)
        by_cases hEB : E ≤ B
        · exact hclose _ (hEB.trans hB) hB
        · have hEall := hclose E le_rfl (le_of_lt (lt_of_not_ge hEB))
          have hE := a22_dual_energy_of_influences g hp hdyadic heta hnorm hEall
          have hfinal : E ≤ (2 : Real) ^ (500 * level ^ 2 * p) * eta ^ 2 := by
            apply hE.trans
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg eta)
            apply pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2)
            omega
          exact hclose _ hfinal hB
  exact hall j f hglobal

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OriginalInduction
