import PvNP.RealizableHardness.MatrixGrassmannIdentity
import PvNP.RealizableHardness.SamplerProximity

/-! SOURCE ONLY. The actual fixed-copy MZ4.4 parameter specialization.
The copy count m is not the separate analytic norm exponent of MZ4.1. -/
namespace PvNP.RealizableHardness.MatrixGrassmannSpecialization
open GrassmannCounting MatrixGrassmannIdentity SamplerParameters
set_option autoImplicit false
noncomputable section

/-- A rational slack representation; admissibility is 0<a<b. -/
def slack (a b : ℕ) : ℚ := (a : ℚ) / b
def scale (b q : ℕ) : ℕ := b*q
def baseDimension (a b q : ℕ) : ℕ := 2*(b-a)*q
def extensionWidth (a q : ℕ) : ℕ := 2*a*q

theorem slack_range {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    0 < slack a b ∧ slack a b < 1 := by
  have hb : (0:ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  constructor
  · exact div_pos (by exact_mod_cast ha) hb
  · exact (div_lt_one hb).mpr (by exact_mod_cast hab)

theorem dimensions_add {a b : ℕ} (hab : a ≤ b) (q : ℕ) :
    baseDimension a b q + extensionWidth a q = 2*scale b q := by
  unfold baseDimension extensionWidth scale
  have := Nat.sub_add_cancel hab
  nlinarith

theorem baseDimension_exact {a b : ℕ} (hab : a ≤ b) (hb : 0 < b) (q : ℕ) :
    (baseDimension a b q : ℚ) = 2*(1-slack a b)*(scale b q : ℚ) := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  unfold baseDimension slack scale
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hab]
  push_cast
  field_simp

theorem extensionWidth_exact {a b : ℕ} (hb : 0 < b) (q : ℕ) :
    (extensionWidth a q : ℚ) = 2*slack a b*(scale b q : ℚ) := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  unfold extensionWidth slack scale
  push_cast
  field_simp

/-- A direct numerical consequence of actual ambient growth and fixed copy count.
The final half-error inequality is proved, never supplied as a hypothesis. -/
theorem half_error_of_growth {J h d w m : ℕ} (hh : 0 < h)
    (hdw : d+w = 2*h) (hsize : 2*h ≤ J) (hm : m+1 ≤ J) :
    ((d+m*w : ℕ):ℝ)*(2:ℝ)^(d+w-1)/(2:ℝ)^(3*J) ≤ 1/2 := by
  have hJ : 0 < J := by omega
  have hc : d+m*w ≤ J^2 := by
    have hfirst : d+m*w ≤ (m+1)*(d+w) := by nlinarith
    have hprod := Nat.mul_le_mul hm hsize
    rw [← hdw] at hprod
    nlinarith
  have hJpow : J ≤ 2^J := Nat.le_of_lt Nat.lt_two_pow_self
  have hsquare : (J:ℝ)^2 ≤ (2:ℝ)^(2*J) := by
    have hx : (J:ℝ) ≤ (2:ℝ)^J := by exact_mod_cast hJpow
    have hhx := mul_self_le_mul_self (Nat.cast_nonneg J : (0:ℝ) ≤ J) hx
    simpa [pow_two, pow_mul, mul_comm] using hhx
  have hcoef : ((d+m*w : ℕ):ℝ) ≤ (2:ℝ)^(2*J) := by
    have ht : ((d+m*w : ℕ):ℝ) ≤ (J:ℝ)^2 := by exact_mod_cast hc
    exact ht.trans hsquare
  have hexp : (2:ℝ)^(d+w-1) ≤ (2:ℝ)^(J-1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnum : ((d+m*w : ℕ):ℝ)*(2:ℝ)^(d+w-1) ≤ (2:ℝ)^(3*J-1) := by
    have ht := mul_le_mul hcoef hexp (by positivity) (by positivity)
    have he : 2*J+(J-1) = 3*J-1 := by omega
    simpa only [← pow_add,he] using ht
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(3*J))).mpr
  have he : 3*J = (3*J-1)+1 := by omega
  calc
    _ ≤ (2:ℝ)^(3*J-1) := hnum
    _ = 1/2*(2:ℝ)^(3*J) := by rw [he,pow_add]; norm_num; ring

/-- A and the paper's actual copy count m are fixed before the threshold for h. -/
theorem eventual_actual_half_error (A m : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → 0 < h ∧ 2*h ≤ 3*blocks A h ∧
      ∀ d w : ℕ, d+w = 2*h →
        ((d+m*w : ℕ):ℝ)*(2:ℝ)^(d+w-1)/(2:ℝ)^(3*blocks A h) ≤ 1/2 := by
  obtain ⟨N,hN⟩ := SamplerProximity.eventually_ready A m hA
  refine ⟨max N (m+1), ?_⟩
  intro h hh
  have hr := hN h (le_trans (le_max_left _ _) hh)
  have hh0 : 0 < h := hr.1
  have hs := (SamplerProximity.ready_dimensions hr).2
  have hm : m+1 ≤ blocks A h := by
    have : m+1 ≤ h := le_trans (le_max_right _ _) hh
    omega
  refine ⟨hh0,by omega,?_⟩
  intro d w hdw
  exact half_error_of_growth hh0 hdw hs hm

/-- Cofinal admissible integral h=b*q. No dimension is rounded. -/
theorem eventual_integral_parameters (A m a b : ℕ)
    (hA : 0 < A) (ha : 0 < a) (hab : a < b) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      0 < scale b q ∧
      baseDimension a b q + extensionWidth a q ≤ 3*blocks A (scale b q) ∧
      ((baseDimension a b q + m*extensionWidth a q : ℕ):ℝ) *
        (2:ℝ)^(baseDimension a b q + extensionWidth a q-1) /
          (2:ℝ)^(3*blocks A (scale b q)) ≤ 1/2 := by
  obtain ⟨N,hN⟩ := eventual_actual_half_error A m hA
  refine ⟨N,?_⟩
  intro q hq
  have hb : 1 ≤ b := by omega
  have hqscale : q ≤ scale b q := by
    unfold scale
    simpa using Nat.mul_le_mul_right q hb
  have hh := hN (scale b q) (hq.trans hqscale)
  have hdw := dimensions_add hab.le q
  exact ⟨hh.1,by simpa [hdw] using hh.2.1,hh.2.2 _ _ hdw⟩

/-- MZ4.4 for the actual modified sampler, actual fixed copy count, and exact
rational-integral test dimensions. Ambient equality is a dimension identification,
not a supplied rank probability, coupling, or error hypothesis. -/
theorem eventual_matrix_grassmann_specialization (A m a b : ℕ)
    (hA : 0 < A) (ha : 0 < a) (hab : a < b) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V],
      Module.finrank (ZMod 2) V = 3*blocks A (scale b q) →
      ∀ (Rset : Grass V (baseDimension a b q) → Bool)
        (Lset : Grass V (baseDimension a b q + extensionWidth a q) → Bool),
        grassmannExperiment Rset Lset m ≤ 2*matrixMoment Rset Lset m := by
  obtain ⟨N,hN⟩ := eventual_integral_parameters A m a b hA ha hab
  refine ⟨N,?_⟩
  intro q hq V _ _ _ hV Rset Lset
  have hh := hN q hq
  apply grassmann_le_twice_moment (by rw [hV]; exact hh.2.1)
    (by rw [dimensions_add hab.le]; omega) m Rset Lset
  simpa only [hV] using hh.2.2

end
end PvNP.RealizableHardness.MatrixGrassmannSpecialization
