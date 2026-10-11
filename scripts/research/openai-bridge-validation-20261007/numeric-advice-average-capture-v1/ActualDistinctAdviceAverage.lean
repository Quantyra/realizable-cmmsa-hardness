import PvNP.RealizableHardness.ActualDistinctAdviceCoverage
import PvNP.RealizableHardness.ActualRefreshGaussian
import PvNP.RealizableHardness.ActualFiniteLaw

/-! Concrete Gaussian specialization and dimension selection under the
original finite law. The complement law is never conditioned on success. -/
namespace PvNP.RealizableHardness.ActualDistinctAdviceAverage

open PvNP.RealizableHardness
open GrassmannCounting ActualMaximalPairLadder NumericRefreshFormalOffer
open ActualRefreshGoodCover ActualDistinctAdviceCoverage ActualRefreshGaussian
open ActualFiniteLaw
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable (d r : Nat)

theorem gaussian_advice_dimension_bound (hrd : r ≤ d) (a : Fin (r + 1)) :
    (gaussian d a.val : Rat) ≤ 4 * (2 : Rat)^(d*d) := by
  have had : a.val ≤ d := by omega
  have hexp : a.val * (d-a.val) ≤ d*d :=
    Nat.mul_le_mul had (Nat.sub_le _ _)
  exact (gaussian_upper_four had).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) hexp) (by norm_num))

/-- Concrete leading-power consequence of the exact distinct-Q cover bound. -/
theorem summed_good_advice_fraction_numeric_lower
    (T : RefreshTable V d) (e : Real) (hrd : r ≤ d)
    (hdV : d ≤ Module.finrank (ZMod 2) V) (D : Rat)
    (hcover : D < ((originalGoodZoomCover V d r T e).card : Rat) /
      Fintype.card (Grass V d)) :
    D / (4 * (2 : Rat)^(d*d)) <
      ∑ a : Fin (r + 1), goodAdviceFraction V d r T e a := by
  exact summed_good_advice_fraction_lower V d r T e hrd hdV
    (4 * (2 : Rat)^(d*d)) D (by positivity)
    (gaussian_advice_dimension_bound d r hrd) hcover

/-- The manuscript's d=2h density coefficient, with no count hypothesis. -/
theorem summed_good_advice_fraction_density_lower
    {h m : Nat} (T : RefreshTable V (2*h)) (e : Real)
    (hrd : r ≤ 2*h) (hdV : 2*h ≤ Module.finrank (ZMod 2) V)
    (D : Rat)
    (hcover : D / (2 * (m : Rat)) <
      ((originalGoodZoomCover V (2*h) r T e).card : Rat) /
        Fintype.card (Grass V (2*h))) :
    D / (8 * (m : Rat) * (2 : Rat)^(4*h^2)) <
      ∑ a : Fin (r + 1), goodAdviceFraction V (2*h) r T e a := by
  have hresult := summed_good_advice_fraction_numeric_lower V (2*h) r T e hrd hdV
    (D / (2 * (m : Rat))) hcover
  have heq : (2*h)*(2*h) = 4*h^2 := by ring
  rw [heq] at hresult
  rw [div_div] at hresult
  have hden : (2 * (m : Rat)) * (4 * (2 : Rat)^(4*h^2)) =
      8 * (m : Rat) * (2 : Rat)^(4*h^2) := by ring
  rw [hden] at hresult
  exact hresult

/-- Unconditioned expectation over every original outcome, including those
outside the supplied good set. -/
def originalLawAdviceFraction {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (T : Ω → RefreshTable V d) (e : Real)
    (a : Fin (r + 1)) : Rat :=
  ∑ ω : Ω, μ.mass ω * goodAdviceFraction V d r (T ω) e a

/-- Sum over dimensions commutes with the original law. Bad outcomes still
contribute their actual nonnegative fraction; no good-event denominator appears. -/
theorem original_law_summed_fraction_lower
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Ω → RefreshTable V d) (e : Real) (G : Finset Ω) (D : Rat)
    (hlocal : ∀ ω ∈ G, D ≤
      ∑ a : Fin (r + 1), goodAdviceFraction V d r (T ω) e a) :
    eventMass μ G * D ≤
      ∑ a : Fin (r + 1), originalLawAdviceFraction V d r μ T e a := by
  have hpoint (ω : Ω) :
      (if ω ∈ G then μ.mass ω * D else 0) ≤
        ∑ a : Fin (r + 1), μ.mass ω * goodAdviceFraction V d r (T ω) e a := by
    by_cases hω : ω ∈ G
    · rw [if_pos hω, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hlocal ω hω) (μ.nonneg ω)
    · rw [if_neg hω]
      exact Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg ω)
        (goodAdviceFraction_nonneg V d r (T ω) e a)
  have hs := Finset.sum_le_sum fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) => hpoint ω
  have hleft : (∑ ω : Ω, if ω ∈ G then μ.mass ω * D else 0) =
      eventMass μ G * D := by
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, eventMass, Finset.sum_mul]
  rw [hleft, Finset.sum_comm] at hs
  exact hs

/-- One fixed advice dimension is selected after averaging over the entire
original law. Exact-budget witnesses then have the fixed codimension r-a. -/
theorem exists_dimension_original_law_fraction_lower
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Ω → RefreshTable V d) (e : Real) (G : Finset Ω) (D : Rat)
    (hlocal : ∀ ω ∈ G, D ≤
      ∑ a : Fin (r + 1), goodAdviceFraction V d r (T ω) e a) :
    ∃ a : Fin (r + 1), eventMass μ G * D / ((r : Rat) + 1) ≤
      originalLawAdviceFraction V d r μ T e a := by
  have hs := original_law_summed_fraction_lower V d r μ T e G D hlocal
  have hden : (r : Rat) + 1 ≠ 0 := by positivity
  have hc : (∑ _a : Fin (r + 1), eventMass μ G * D / ((r : Rat) + 1)) =
      eventMass μ G * D := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp [hden]
  obtain ⟨a, _ha, hbound⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (r+1))).Nonempty)
    (hc.le.trans hs)
  exact ⟨a, hbound⟩

theorem good_advice_fixed_codimension
    (T : RefreshTable V d) (e : Real) (a : Fin (r+1)) (Q : Grass V a.val)
    (hQ : Q ∈ goodAdvice V d r T e a) :
    ∃ P : DecodedPair Q d, codim P.W = r-a.val ∧
      e/2 < (agreement T Q P : Real) := by
  obtain ⟨P, hbudget, hagree⟩ := (mem_goodAdvice_iff V d r T e a Q).mp hQ
  exact ⟨P, by omega, hagree⟩

end
end PvNP.RealizableHardness.ActualDistinctAdviceAverage
