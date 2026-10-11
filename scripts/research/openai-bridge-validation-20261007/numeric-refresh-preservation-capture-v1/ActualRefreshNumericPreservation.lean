import PvNP.RealizableHardness.ActualRefreshCandidateCount
import PvNP.RealizableHardness.ActualNumericRobustReal

/-! Concrete product-law failure bound at the manuscript's selected numeric
parameters. No event-mass hypothesis or favorable table is supplied. -/
namespace PvNP.RealizableHardness.ActualRefreshNumericPreservation

open PvNP.RealizableHardness
open GrassmannCounting NumericRefreshFormalOffer NumericRefreshTailOffer
open ActualRefreshCandidates ActualRefreshCandidateCount
open ActualNumericRobustReal ActualNumericRobustCutoffs
open ActualNumericSourceHeight ActualNumericExplicitHeight SamplerParameters

set_option autoImplicit false
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

private theorem decay_exponent_identity {h r n : Nat}
    (hh : 16 ≤ h) (hr : 8*(r+1) ≤ h) (hn : 8*h+4*r+16 ≤ n) :
    -((1 / (2 : Real)^(2*h)) * (1 / (2 : Real)^(2*h)) *
      (2 : Real)^((2*h-r)*(n-r-2*h))) / 3 =
        -((2 : Real)^refreshExponent h r n) / 12 := by
  let K := (2*h-r)*(n-r-2*h)
  have hu : h ≤ 2*h-r := by omega
  have hv : 16 ≤ n-r-2*h := by omega
  have hp : 4*h ≤ K+2 := by
    have hx := Nat.mul_le_mul hu hv
    dsimp [K]
    nlinarith [hx]
  have he : refreshExponent h r n + 4*h = K+2 := Nat.sub_add_cancel hp
  have hpow : (2 : Real)^refreshExponent h r n *
      (2 : Real)^(2*h) * (2 : Real)^(2*h) = 4 * (2 : Real)^K := by
    rw [← pow_add, ← pow_add]
    have he' : refreshExponent h r n + 2*h + 2*h = K+2 := by omega
    rw [he', pow_add]
    norm_num
    <;> ring
  change -((1 / (2 : Real)^(2*h)) * (1 / (2 : Real)^(2*h)) *
    (2 : Real)^K) / 3 = -((2 : Real)^refreshExponent h r n) / 12
  field_simp
  <;> nlinarith [hpow]

/-- The actual union over the full dependent candidate carrier is bounded
by the explicit Fn, using exact dual-label probabilities and Gaussian counts. -/
theorem actual_failure_mass_le_numeric_bound
    {h r n : Nat} (X : Finset (Grass V (2*h)))
    (hdim : Module.finrank (ZMod 2) V = n)
    (hh : 16 ≤ h) (hr : 8*(r+1) ≤ h) (hn : 8*h+4*r+16 ≤ n) :
    realEventMass V (2*h) (freshFullLabelLaw V (2*h))
      (allCandidateFreshFailures V (2*h) r X) ≤ refreshFailureBound h r n := by
  have hbound := allCandidateFreshFailures_mass_le_uniform
    (V := V) (d := 2*h) (r := r) X hdim (by omega) (by omega)
  have hdecay := decay_exponent_identity hh hr hn
  rw [hdecay] at hbound
  simpa only [refreshFailureBound, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] using hbound

theorem numeric_failure_bound_lt_one {m h A : Nat}
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h) (hA : 1 ≤ A) :
    refreshFailureBound h (numericRankThreshold m) (2*blocks A h) < 1 := by
  have htotal := numeric_refresh_total_failure_lt_half hm hh hA
  have hH : (1 : Real) ≤
      (refreshHorizon (numericRankThreshold m) (2*blocks A h)
        (refreshThreshold m h) : Real) := by
    exact_mod_cast (show 1 ≤ refreshHorizon (numericRankThreshold m)
      (2*blocks A h) (refreshThreshold m h) by unfold refreshHorizon; omega)
  have hF : 0 ≤ refreshFailureBound h (numericRankThreshold m) (2*blocks A h) := by
    unfold refreshFailureBound
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hH hF]

/-- The actual per-state bad mass is below one uniformly for every X at the
unchanged numeric floor, independently of how X was selected before refresh. -/
theorem numeric_actual_failure_mass_lt_one {m h A : Nat}
    (X : Finset (Grass V (2*h)))
    (hdim : Module.finrank (ZMod 2) V = 2*blocks A h)
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h) (hA : 1 ≤ A) :
    realEventMass V (2*h) (freshFullLabelLaw V (2*h))
      (allCandidateFreshFailures V (2*h) (numericRankThreshold m) X) < 1 := by
  have hg := numeric_robust_dimension_guards hm hh hA
  exact (actual_failure_mass_le_numeric_bound X hdim hg.2.2.1 hg.2.1
    hg.2.2.2.2.1).trans_lt (numeric_failure_bound_lt_one hm hh hA)

/-- A fresh table preserving all actual candidates exists under the actual
uniform full-table law; it is a conclusion, never an assumed random outcome. -/
theorem exists_numeric_actual_preserving_refresh {m h A : Nat}
    (X : Finset (Grass V (2*h)))
    (hdim : Module.finrank (ZMod 2) V = 2*blocks A h)
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h) (hA : 1 ≤ A) :
    ∃ F : RefreshTable V (2*h),
      F ∉ allCandidateFreshFailures V (2*h) (numericRankThreshold m) X := by
  exact exists_actual_preserving_refresh V (2*h) (numericRankThreshold m) X
    (numeric_actual_failure_mass_lt_one X hdim hm hh hA)

end
end PvNP.RealizableHardness.ActualRefreshNumericPreservation
