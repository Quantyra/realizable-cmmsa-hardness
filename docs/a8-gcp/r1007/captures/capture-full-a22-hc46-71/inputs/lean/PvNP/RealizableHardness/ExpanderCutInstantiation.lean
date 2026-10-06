import PvNP.RealizableHardness.PortCycleReplacement
import Complexitylib.Classes.PCP.Internal.Cheeger
import Complexitylib.Classes.PCP.Internal.FamilyFin

/-! SOURCE DRAFT: not compiled. Reuses the pinned library's spectral-to-cut
proof and reconciles its outgoing darts with our half-total mismatch count.
No hardness or machine-time hypothesis is substituted for a construction. -/
namespace PvNP.RealizableHardness.ExpanderCutInstantiation
open scoped BigOperators
open PortCycleReplacement
set_option autoImplicit false

noncomputable section

/-- One undirected crossing per pair of reversed darts, with multiplicity.
Loops have zero contribution. This is the convention of `external`. -/
def boundary (G : Complexity.RegGraph) (S : G.V → Bool) : ℝ :=
  (∑ p : G.V × G.D, distance (S p.1) (S (G.nbr p.1 p.2))) / 2

def support (G : Complexity.RegGraph) (S : G.V → Bool) : Finset G.V :=
  Finset.univ.filter fun v => S v = true

lemma support_card (G : Complexity.RegGraph) (S : G.V → Bool) :
    ((support G S).card : ℝ) = count S := by
  classical
  simp only [support, Finset.card_filter, Nat.cast_sum, count]
  apply Finset.sum_congr rfl
  intro v _
  cases S v <;> norm_num [bit]

lemma support_compl_card (G : Complexity.RegGraph) (S : G.V → Bool) :
    ((support G S)ᶜ.card : ℝ) = count (fun v => !(S v)) := by
  classical
  have he : (support G S)ᶜ = support G (fun v => !(S v)) := by
    ext v
    cases h : S v <;> simp [support, h]
  rw [he, support_card]

/-- The involutive rotation in `RegGraph` justifies dividing by two;
no simplicity or absence of loops is required. -/
theorem boundary_eq_outgoing (G : Complexity.RegGraph) (S : G.V → Bool) :
    boundary G S = ((G.dartsBetween (support G S) (support G S)ᶜ).card : ℝ) := by
  classical
  have hp (p : G.V × G.D) :
      distance (S p.1) (S (G.nbr p.1 p.2)) =
      (if p.1 ∈ support G S ∧ G.nbr p.1 p.2 ∉ support G S then (1 : ℝ) else 0) +
      (if p.1 ∉ support G S ∧ G.nbr p.1 p.2 ∈ support G S then (1 : ℝ) else 0) := by
    cases h₁ : S p.1 <;> cases h₂ : S (G.nbr p.1 p.2) <;>
      simp [distance, support, h₁, h₂]
  unfold boundary
  simp_rw [hp]
  rw [Finset.sum_add_distrib, G.sum_darts_boundary]
  ring

lemma product_over_sum_ge_half_min (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) : min a b / 2 ≤ a * b / (a + b) := by
  apply (le_div_iff₀ hab).2
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr h)]

/-- Exact min-side expansion from the normalized spectral convention.
This also covers the empty graph without division by its order. -/
theorem boundary_expansion (G : Complexity.RegGraph) (lam : ℝ)
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) (hspec : G.SpectralBound lam)
    (S : G.V → Bool) :
    ((G.deg : ℝ) * (1 - lam) / 2) * smallSide S ≤ boundary G S := by
  classical
  rw [boundary_eq_outgoing]
  by_cases hn : 0 < G.order
  · have he := G.card_dartsBetween_compl_ge hlam₀ hspec hn (support G S)
    rw [support_card, support_compl_card] at he
    have hab : count S + count (fun v => !(S v)) = (G.order : ℝ) :=
      count_complement S
    have hnR : 0 < (G.order : ℝ) := by exact_mod_cast hn
    have hprod := product_over_sum_ge_half_min (count S) (count (fun v => !(S v)))
      (count_nonneg S) (count_nonneg _) (by rw [hab]; exact hnR)
    rw [hab] at hprod
    have hc : 0 ≤ (1 - lam) * (G.deg : ℝ) :=
      mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hprod hc
    unfold smallSide
    nlinarith
  · have hz : G.order = 0 := by omega
    have hab := count_complement S
    have ha := count_nonneg S
    have hb := count_nonneg (fun v => !(S v))
    have hzR : (Fintype.card G.V : ℝ) = 0 := by
      change (G.order : ℝ) = 0
      rw [hz]; norm_num
    rw [hzR] at hab
    have ha0 : count S = 0 := by linarith
    have hb0 : count (fun v => !(S v)) = 0 := by linarith
    simp only [smallSide, ha0, hb0, min_self, mul_zero]
    positivity

/-- The fixed actual library family, not a supplied expander assumption. -/
def fixedCoefficient : ℝ :=
  (Complexity.algFamily.degree : ℝ) * (1 - Complexity.algFamily.lam) / 2

theorem fixedCoefficient_pos : 0 < fixedCoefficient := by
  have hd : 0 < (Complexity.algFamily.degree : ℝ) := by
    exact_mod_cast Complexity.algFamily.degree_pos
  have hl : 0 < 1 - Complexity.algFamily.lam :=
    sub_pos.mpr Complexity.algFamily.lam_lt_one
  unfold fixedCoefficient
  positivity

theorem actual_family_expansion (n : ℕ)
    (S : (Complexity.algFamily.graph n).V → Bool) :
    fixedCoefficient * smallSide S ≤ boundary (Complexity.algFamily.graph n) S := by
  simpa [fixedCoefficient] using boundary_expansion (Complexity.algFamily.graph n)
    Complexity.algFamily.lam Complexity.algFamily.lam_nonneg
    Complexity.algFamily.lam_lt_one (Complexity.algFamily.spectral_graph n) S

/-- Direct application to the actual rotation, using the same cut convention
as the source replacement module. The remaining family integration is only
transport of its positive degree to successor form; no spectral lemma is left. -/
theorem port_cut_of_spectral {n d : Nat} (R : Port n d → Port n d)
    (hR : Function.Involutive R) (lam : Real) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hspec : (Complexity.RegGraph.ofRot (d + 1) (by omega) n R hR).SpectralBound lam)
    (S : Port n d → Bool) :
    let h : Real := (d + 1 : Real) * (1 - lam) / 2
    (h / ((d + 1 : Real) * (1 + h + (d + 1)))) * smallSide S ≤ cut R S := by
  dsimp only
  have hgap : 0 < 1 - lam := sub_pos.mpr hlam1
  apply cut_expansion R hR _ (by positivity)
  intro A
  have he := boundary_expansion
    (Complexity.RegGraph.ofRot (d + 1) (by omega) n R hR) lam hlam0 hlam1 hspec A
  rw [Complexity.RegGraph.deg_ofRot] at he
  change ((d + 1 : Nat) : Real) * (1 - lam) / 2 * smallSide A ≤
    external R (lift A) at he
  simpa only [Nat.cast_add, Nat.cast_one] using he


end
end PvNP.RealizableHardness.ExpanderCutInstantiation
