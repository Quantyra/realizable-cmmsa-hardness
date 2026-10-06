import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Finite rational weighted exception repair. No computational hardness is asserted. -/
namespace PvNP.RealizableHardness
open scoped BigOperators

noncomputable def average {I : Type*} [Fintype I] (p : I → Bool) : ℚ :=
  (∑ i, if p i then (1 : ℚ) else 0) / Fintype.card I

lemma average_nonneg {I : Type*} [Fintype I] (p : I → Bool) : 0 ≤ average p := by
  unfold average
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro i _
  split <;> norm_num

lemma average_le_one {I : Type*} [Fintype I] [Nonempty I] (p : I → Bool) :
    average p ≤ 1 := by
  unfold average
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).2
  calc
    _ ≤ ∑ _i : I, (1 : ℚ) := Finset.sum_le_sum fun i _ => by split <;> norm_num
    _ = _ := by simp

lemma average_not {I : Type*} [Fintype I] [Nonempty I] (p : I → Bool) :
    average (fun i => !(p i)) = 1 - average p := by
  have hc : (Fintype.card I : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  have hs : (∑ i, if !(p i) then (1 : ℚ) else 0) =
      (Fintype.card I : ℚ) - ∑ i, if p i then (1 : ℚ) else 0 := by
    calc
      _ = ∑ i, ((1 : ℚ) - if p i then (1 : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        cases p i <;> norm_num
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  rw [hs, sub_div, div_self hc]

lemma average_or_le {I : Type*} [Fintype I] (p q : I → Bool) :
    average (fun i => p i || q i) ≤ average p + average q := by
  unfold average
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases hp : p i <;> cases hq : q i <;> simp [hp, hq]

lemma average_true {I : Type*} [Fintype I] [Nonempty I] :
    average (fun _ : I => true) = 1 := by
  unfold average
  simp [Fintype.card_ne_zero]

noncomputable def weight {V : Type*} [Fintype V] (w : V → ℚ) (x : V → Bool) : ℚ :=
  ∑ v, if x v then w v else 0

lemma weight_nonneg {V : Type*} [Fintype V] (w : V → ℚ) (x : V → Bool)
    (hw : ∀ v, 0 ≤ w v) : 0 ≤ weight w x := by
  apply Finset.sum_nonneg
  intro v _
  split <;> simp_all

noncomputable def repairedWeight {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℚ) (lam : ℚ) (x : V → Bool) (e : I → Bool) : ℚ :=
  (weight w x + lam * average e) / (1 + lam)

/-- One fresh raw weight lam/card I per index, followed by normalization. -/
noncomputable def repairedWeights {V I : Type*} [Fintype I]
    (w : V → ℚ) (lam : ℚ) (z : V ⊕ I) : ℚ :=
  Sum.elim w (fun _ => lam / Fintype.card I) z / (1 + lam)

lemma weight_div {V : Type*} [Fintype V] (w : V → ℚ) (x : V → Bool) (d : ℚ) :
    weight (fun v => w v / d) x = weight w x / d := by
  unfold weight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  split <;> simp

/-- The aggregate cost is the actual sum of selected output coordinate weights. -/
theorem repairedWeight_eq_sum {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℚ) (lam : ℚ) (x : V → Bool) (e : I → Bool) :
    weight (repairedWeights w lam) (Sum.elim x e) = repairedWeight w lam x e := by
  unfold repairedWeights
  rw [weight_div]
  simp only [repairedWeight, weight]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  congr 1
  unfold average
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : e i = true <;> simp [h]

lemma repairedWeights_pos {V I : Type*} [Fintype I] [Nonempty I]
    (w : V → ℚ) (lam : ℚ) (hw : ∀ v, 0 < w v) (hlam : 0 < lam) :
    ∀ z : V ⊕ I, 0 < repairedWeights w lam z := by
  intro z
  cases z with
  | inl v => exact div_pos (hw v) (by linarith)
  | inr i =>
    apply div_pos _ (by linarith : 0 < 1 + lam)
    apply div_pos hlam
    exact_mod_cast Fintype.card_pos

theorem repairedWeights_sum {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    (w : V → ℚ) (lam : ℚ) (hw : ∑ v, w v = 1) (hlam : 0 ≤ lam) :
    ∑ z : V ⊕ I, repairedWeights w lam z = 1 := by
  have heq := repairedWeight_eq_sum w lam (fun _ : V => true) (fun _ : I => true)
  have hfun : (Sum.elim (fun _ : V => true) (fun _ : I => true)) = fun _ => true := by
    funext z; cases z <;> rfl
  rw [hfun] at heq
  simp only [weight, ite_true] at heq
  rw [heq]
  unfold repairedWeight
  simp only [weight, ite_true, hw, average_true, mul_one]
  exact div_self (by linarith)

lemma repairedBudget_pos (s eps lam : ℚ) (hs : 0 < s) (heps : 0 ≤ eps) (hlam : 0 ≤ lam) :
    0 < (s + lam * eps) / (1 + lam) := by positivity

lemma repairedBudget_le_one (s eps lam : ℚ) (hs : s ≤ 1) (heps : eps ≤ 1) (hlam : 0 ≤ lam) :
    (s + lam * eps) / (1 + lam) ≤ 1 := by
  apply (div_le_one (by linarith : 0 < 1 + lam)).2
  nlinarith [mul_le_mul_of_nonneg_left heps hlam]

/-- Semantic augmentation, with a distinct Boolean exception coordinate for each index. -/
def repaired {V I : Type*} (F : I → (V → Bool) → Bool)
    (x : V → Bool) (e : I → Bool) (i : I) : Bool := F i x || e i

/-- Repair a genuine finite witness by enabling exactly its failed indices. -/
theorem exception_completeness {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    (w : V → ℚ) (F : I → (V → Bool) → Bool) (s eps lam : ℚ)
    (hlam : 0 ≤ lam) (x : V → Bool) (hx : weight w x ≤ s)
    (hyes : 1 - eps ≤ average (fun i => F i x)) :
    ∃ e : I → Bool,
      repairedWeight w lam x e ≤ (s + lam * eps) / (1 + lam) ∧
      ∀ i, repaired F x e i = true := by
  refine ⟨fun i => !(F i x), ?_, ?_⟩
  · unfold repairedWeight
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [average_not]
    have := mul_le_mul_of_nonneg_left
      (show 1 - average (fun i => F i x) ≤ eps by linarith) hlam
    linarith
  · intro i
    simp [repaired]

/-- The original NO promise is an explicit hypothesis, not an asserted hardness premise. -/
theorem exception_soundness {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℚ) (F : I → (V → Bool) → Bool) (s sig gam eps k : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hs : 0 < s) (hsig : 0 < sig) (hgam : 0 < gam)
    (heps : 0 ≤ eps) (hsmall : eps * sig ≤ gam / 2)
    (_hk : 0 ≤ k) (hkle : k ≤ sig / 4)
    (hno : ∀ x, weight w x ≤ sig * s → average (fun i => F i x) < gam)
    (x : V → Bool) (e : I → Bool)
    (hbudget : repairedWeight w (sig * s / gam) x e ≤
      k * ((s + (sig * s / gam) * eps) / (1 + sig * s / gam))) :
    average (repaired F x e) < 2 * gam := by
  let lam := sig * s / gam
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have he := average_nonneg e
  have hx := weight_nonneg w x hw
  have hle : lam * eps ≤ s / 2 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hgam).2
    nlinarith [mul_le_mul_of_nonneg_left hsmall (le_of_lt hs)]
  have hraw : weight w x + lam * average e ≤ k * (s + lam * eps) := by
    have hb : (weight w x + lam * average e) / (1 + lam) ≤
        (k * (s + lam * eps)) / (1 + lam) := by
      simpa only [repairedWeight, lam, mul_div_assoc] using hbudget
    exact (div_le_div_iff_of_pos_right (by linarith : 0 < 1 + lam)).1 hb
  have htotal : weight w x + lam * average e ≤ 3 * sig * s / 8 := by
    have hbase : 0 ≤ s + lam * eps := by positivity
    have hm := mul_le_mul_of_nonneg_right hkle hbase
    have hn := mul_le_mul_of_nonneg_left hle (le_of_lt hsig)
    nlinarith
  have hold : weight w x ≤ sig * s := by
    nlinarith [mul_nonneg (le_of_lt hlam) he, mul_pos hsig hs]
  have hecost : lam * average e ≤ 3 * sig * s / 8 := by linarith
  have hidentity : lam * gam = sig * s := by dsimp [lam]; field_simp
  have hebound : average e ≤ 3 * gam / 8 := by
    apply (mul_le_mul_iff_left₀ hlam).mp
    nlinarith only [hecost, hidentity]
  have ho := hno x hold
  have hu := average_or_le (fun i => F i x) e
  change average (fun i => F i x || e i) < 2 * gam
  linarith

#print axioms exception_completeness
#print axioms exception_soundness
end PvNP.RealizableHardness
