import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Centered Bernoulli exponential bound, proved by the log-partition curvature.
No concentration, computational reduction, or hardness assertion is assumed. -/
namespace PvNP.RealizableHardness.BernoulliMGF

noncomputable def partition (p t : ℝ) : ℝ := 1 - p + p * Real.exp t
noncomputable def gap (p t : ℝ) : ℝ := t ^ 2 / 8 + p * t - Real.log (partition p t)
noncomputable def gapSlope (p t : ℝ) : ℝ := t / 4 + p - p * Real.exp t / partition p t
noncomputable def gapCurvature (p t : ℝ) : ℝ :=
  1 / 4 - (p * Real.exp t * (1 - p)) / (partition p t) ^ 2

lemma partition_pos (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 < partition p t := by
  rcases eq_or_lt_of_le hp with h | h
  · simp [partition, ← h]
  · unfold partition
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hp1) (mul_pos h (Real.exp_pos t))

lemma partition_deriv (p t : ℝ) :
    HasDerivAt (partition p) (p * Real.exp t) t := by
  convert! ((Real.hasDerivAt_exp t).const_mul p).const_add (1 - p) using 1

lemma gap_deriv (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (gap p) (gapSlope p t) t := by
  have h := (((hasDerivAt_id t).pow 2).div_const 8).add
    ((hasDerivAt_id t).const_mul p)
  convert! h.sub ((partition_deriv p t).log (partition_pos p t hp hp1).ne') using 1
  try simp only [gap, gapSlope, id_eq]
  ring

lemma gapSlope_deriv (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (gapSlope p) (gapCurvature p t) t := by
  have hn := (Real.hasDerivAt_exp t).const_mul p
  have hd := partition_deriv p t
  have h := (((hasDerivAt_id t).div_const 4).add_const p).sub
    (hn.div hd (partition_pos p t hp hp1).ne')
  convert! h using 1
  try dsimp [gapSlope, gapCurvature]
  have hz := (partition_pos p t hp hp1).ne'
  field_simp [hz]
  try dsimp [partition]
  ring

lemma gapCurvature_nonneg (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ gapCurvature p t := by
  have hd : 0 < (partition p t) ^ 2 := sq_pos_of_pos (partition_pos p t hp hp1)
  unfold gapCurvature
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hd).mpr
  dsimp [partition]
  nlinarith [sq_nonneg (1 - p - p * Real.exp t)]

lemma gapSlope_monotone (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (gapSlope p) :=
  monotone_of_hasDerivAt_nonneg (fun t => gapSlope_deriv p t hp hp1)
    (fun t => gapCurvature_nonneg p t hp hp1)

@[simp] lemma gap_zero (p : ℝ) : gap p 0 = 0 := by simp [gap, partition]
@[simp] lemma gapSlope_zero (p : ℝ) : gapSlope p 0 = 0 := by simp [gapSlope, partition]

theorem gap_nonneg (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ gap p t := by
  have hd := fun x => gap_deriv p x hp hp1
  have hm := gapSlope_monotone p hp hp1
  rcases le_total 0 t with ht | ht
  · have hmono : MonotoneOn (gap p) (Set.Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          have hx0 : 0 ≤ x := (interior_subset hx)
          simpa using hm hx0)
    simpa using hmono (by simp) ht ht
  · have hanti : AntitoneOn (gap p) (Set.Iic 0) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          have hx0 : x ≤ 0 := (interior_subset hx : x ∈ Set.Iic 0)
          simpa using hm hx0)
    simpa using hanti ht (by simp) ht

/-- Exact centered Bernoulli MGF bound, for all real t including both tails. -/
theorem centered_mgf_le (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) ≤
      Real.exp (t ^ 2 / 8) := by
  have hlog : Real.log (partition p t) ≤ t ^ 2 / 8 + p * t := by
    have h := gap_nonneg p t hp hp1
    dsimp [gap] at h
    linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (partition_pos p t hp hp1)] at he
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-t * p)).le
  have hleft : partition p t * Real.exp (-t * p) =
      (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) := by
    rw [partition, add_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hright : Real.exp (t ^ 2 / 8 + p * t) * Real.exp (-t * p) =
      Real.exp (t ^ 2 / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [hleft, hright] at hm

end PvNP.RealizableHardness.BernoulliMGF
