/- UNCOMPILED checks, not an executed verification report. -/
import PvNP.RealizableHardness.SamplerProximity
open PvNP.RealizableHardness
open SamplerParameters SamplerProximity DropTailParameters

#print axioms SamplerProximity.two_pos
#print axioms SamplerProximity.two_mono
#print axioms SamplerProximity.blocks_real
#print axioms SamplerProximity.beta_real
#print axioms SamplerProximity.decay_two
#print axioms SamplerProximity.eventual_inner_domination
#print axioms SamplerProximity.eventually_ready
#print axioms SamplerProximity.mean_le_two
#print axioms SamplerProximity.beta_le_two
#print axioms SamplerProximity.advice_le_two
#print axioms SamplerProximity.zoom_le_two
#print axioms SamplerProximity.ready_advice
#print axioms SamplerProximity.ready_zoom_scaled
#print axioms SamplerProximity.ready_zoom
#print axioms SamplerProximity.ready_small_beta
#print axioms SamplerProximity.ready_density
#print axioms SamplerProximity.ready_dimensions
#print axioms SamplerProximity.decay_antitone
#print axioms SamplerProximity.five_decay70_lt
#print axioms SamplerProximity.ready_exceptional
#print axioms SamplerProximity.eventual_proximity

example (h : ℕ) : (blocks 0 h : ℝ) = 2 := by simp [blocks_zero_A]
example (h : ℕ) : (beta 0 h : ℝ) = 0 := by simp [beta_zero_A]
example : decay 100 0 = 1 := decay_zero 100
example {h : ℕ} (hh : 1 ≤ h) : 5 * decay 70 h < decay 20 h := five_decay70_lt hh
example (r : ℕ) : ∃ N : ℕ, ∀ h : ℕ, N ≤ h → r + 1 ≤ blocks 1 h := by
  obtain ⟨N, hN⟩ := eventual_proximity 1 r (by norm_num)
  exact ⟨N, fun h hh => (hN h hh).1⟩
example {A r h : ℕ} (hr : SamplerProximity.Ready A r h) :
    8 * (2 : ℝ) ^ (2 * r * h ^ 4) * ((2 : ℝ) ^ r - 1) * (beta A h : ℝ) ≤ decay 30 h :=
  ready_density hr le_rfl le_rfl
example {A r h : ℕ} (hr : SamplerProximity.Ready A r h) :
    (2 : ℝ) ^ (2 * h) * (beta A h : ℝ) ≤ 1 / 8 := ready_small_beta hr
