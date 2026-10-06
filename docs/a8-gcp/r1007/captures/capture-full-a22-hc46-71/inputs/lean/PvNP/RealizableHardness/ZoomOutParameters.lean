/- UNCOMPILED source draft. No author or independent kernel acceptance claimed. -/
import PvNP.RealizableHardness.SamplerProximity
import PvNP.RealizableHardness.GaussianNearOne
import PvNP.RealizableHardness.ZoomOutIncidence

namespace PvNP.RealizableHardness.ZoomOutParameters
open TripleRestrictionRank GrassmannIncidence GrassmannCounting
open SamplerParameters GaussianNearOne ZoomOutIncidence
noncomputable section

/-- Explicit finite relative intervals, including the actual product error. -/
def Bounds (J n b c : ℕ) (p : ℚ) : Prop :=
  error (n-c) b ≤ 1 / (2 : ℚ)^(J/2) ∧
  leading b c * (1-error (n-c) b) ≤ p ∧
  p ≤ leading b c ∧
  leading b c * (1-1/(2 : ℚ)^(J/2)) ≤ p ∧
  leading b c / 2 ≤ p

lemma ratio_bounds {J n b c : ℕ} (hc : c ≤ n) (hb : b+1 ≤ n-c)
    (hk : b+c+J/2 ≤ n) :
    Bounds J n b c ((gaussian (n-c) b : ℚ) / gaussian n b) := by
  have he := error_le_inverse_pow (show b+J/2 ≤ n-c by omega)
  have hn := gaussian_near_one hc hb
  have hf := gaussian_near_one_half_J hc hb hk
  exact ⟨he, hn.1, hn.2, hf.1, gaussian_probability_ge_half hc hb⟩

/-- An actual retained space always has at least one coordinate per block. -/
lemma retained_dimension_lower {J : ℕ} (s : Draw J) :
    J ≤ Module.finrank (ZMod 2) (retained s) := by
  have hd := TripleRestrictionDimension.dropCount_le s
  have he := TripleRestrictionDimension.retained_finrank_add_twice_dropCount s
  omega

/-- The existing sufficient proximity budget also leaves half the ambient
dimension unused after the zoom-out dimensions. -/
lemma ready_budget {A r h : ℕ} (hr : SamplerProximity.Ready A r h) :
    2 * (2*h+r+1) ≤ blocks A h := by
  have hE : SamplerProximity.exponent A h ≤ (blocks A h : ℝ) := by
    have hn : 2^(A*h^2) ≤ blocks A h := Nat.le_of_lt Nat.lt_two_pow_self
    unfold SamplerProximity.exponent
    exact_mod_cast hn
  have hm : 0 ≤ SamplerProximity.mean A h := by
    unfold SamplerProximity.mean
    positivity
  have hp : 0 ≤ 2 * (r : ℝ) * (h : ℝ)^4 := by positivity
  have hq : 0 ≤ ((r : ℝ)+200) * (h : ℝ)^2 := by positivity
  have hn : (2 : ℝ) * (2*(h : ℝ)+(r : ℝ)+1) ≤ (blocks A h : ℝ) := by
    nlinarith [hr.2]
  exact_mod_cast hn

/-- One threshold after fixed A,r; no growth premise remains. -/
theorem eventual_budget (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h →
      r < h ∧ 2 * (2*h+r+1) ≤ blocks A h := by
  obtain ⟨N, hN⟩ := SamplerProximity.eventually_ready A r hA
  refine ⟨max N (r+1), ?_⟩
  intro h hh
  exact ⟨by omega, ready_budget (hN h (by omega))⟩

/-- Natural subtraction and floor division are controlled by a concrete budget. -/
lemma dimension_budget {J n h r a c : ℕ} (hJ : J ≤ n)
    (hh : r < h) (hbudget : 2*(2*h+r+1) ≤ J) (ha : a ≤ r) (hc : c ≤ r) :
    a < 2*h ∧ 2*h ≤ J ∧ c ≤ n-a ∧
      (2*h-a)+1 ≤ (n-a)-c ∧ (2*h-a)+c+J/2 ≤ n-a := by
  omega

theorem retained_bounds {A r h a c : ℕ} (hh : r < h)
    (hbudget : 2*(2*h+r+1) ≤ blocks A h) (ha : a ≤ r) (hc : c ≤ r)
    (s : Draw (blocks A h)) (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ W)
    (hstable : Module.finrank (ZMod 2) ↥(retained s ⊓ W) + c =
      Module.finrank (ZMod 2) (retained s)) :
    Bounds (blocks A h) (Module.finrank (ZMod 2) (retained s)-a) (2*h-a) c
      (retainedZoomMass s Q W (2*h)) := by
  have hdim := retained_dimension_lower s
  obtain ⟨had, hdJ, hcn, hspare, hhalf⟩ := dimension_budget hdim hh hbudget ha hc
  rw [retainedZoomMass_rank_stable s Q W c hQV hQW had.le
    (hdJ.trans hdim) hstable]
  exact ratio_bounds hcn hspare hhalf

theorem ambient_bounds {A r h a c : ℕ} (hh : r < h)
    (hbudget : 2*(2*h+r+1) ≤ blocks A h) (ha : a ≤ r) (hc : c ≤ r)
    (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hQW : Q.val ≤ W) (hcodim : Module.finrank (ZMod 2) W + c = 3 * blocks A h) :
    Bounds (blocks A h) (3*blocks A h-a) (2*h-a) c
      (ambientZoomMass Q W (2*h)) := by
  obtain ⟨had, hdJ, hcn, hspare, hhalf⟩ := dimension_budget
    (show blocks A h ≤ 3*blocks A h by omega) hh hbudget ha hc
  rw [ambientZoomMass_codimension Q W c hQW had.le hdJ hcodim]
  exact ratio_bounds hcn hspare hhalf

/-- Exact prescribed family. The threshold precedes all advice dimensions,
codimensions, draws and subspaces. Only containment and rank geometry remain. -/
theorem eventual_zoom_out (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → ∀ a c : ℕ, a ≤ r → c ≤ r →
      a < 2*h ∧ 2*h ≤ blocks A h ∧
      (∀ (s : Draw (blocks A h)) (Q : Advice (blocks A h) a)
        (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h))),
        Q.val ≤ retained s → Q.val ≤ W →
        Module.finrank (ZMod 2) ↥(retained s ⊓ W) + c =
          Module.finrank (ZMod 2) (retained s) →
        Bounds (blocks A h) (Module.finrank (ZMod 2) (retained s)-a) (2*h-a) c
          (retainedZoomMass s Q W (2*h))) ∧
      (∀ (Q : Advice (blocks A h) a)
        (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h))),
        Q.val ≤ W → Module.finrank (ZMod 2) W + c = 3*blocks A h →
        Bounds (blocks A h) (3*blocks A h-a) (2*h-a) c
          (ambientZoomMass Q W (2*h))) := by
  obtain ⟨N, hN⟩ := eventual_budget A r hA
  refine ⟨N, ?_⟩
  intro h hh a c ha hc
  obtain ⟨hlarge, hbudget⟩ := hN h hh
  have hd := dimension_budget (show blocks A h ≤ blocks A h by omega)
    hlarge hbudget ha hc
  exact ⟨hd.1, hd.2.1,
    fun s Q W hQV hQW hs => retained_bounds hlarge hbudget ha hc s Q W hQV hQW hs,
    fun Q W hQW hcodim => ambient_bounds hlarge hbudget ha hc Q W hQW hcodim⟩

end
end PvNP.RealizableHardness.ZoomOutParameters
