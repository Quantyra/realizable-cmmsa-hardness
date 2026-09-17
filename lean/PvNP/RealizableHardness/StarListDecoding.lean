import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Actual occurrence-weighted star list decoding. No formula compiler is asserted:
empty projection fibres may require false, absent from the current Formula syntax.
This source is a draft until its isolated build and independent reviews succeed. -/
namespace PvNP.RealizableHardness.StarListDecoding
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]
  {Sigma : V → Type*} [∀ v, Fintype (Sigma v)] [∀ v, Nonempty (Sigma v)]
  {m : ℕ}

/-- Edges are occurrences, not deduplicated vertex sets. -/
structure Star (V : Type*) (Sigma : V → Type*) (m : ℕ) where
  center : V
  leaf : Fin m → V
  projection : (i : Fin m) → Sigma (leaf i) → Sigma center
  separated : ∀ i, center ≠ leaf i

abbrev Labeling (Sigma : V → Type*) := (v : V) → Sigma v

def Star.slot (e : Star V Sigma m) : Fin (m + 1) → V :=
  Fin.cases e.center e.leaf

def Star.accepts (e : Star V Sigma m) (l : Labeling Sigma) : Prop :=
  ∀ i, e.projection i (l (e.leaf i)) = l e.center

noncomputable def Star.support (e : Star V Sigma m) : Finset V := by
  classical
  exact Finset.univ.image e.slot

/-- The witness is actual consistent labels, not independent answers per slot.
Labels outside the edge are unconstrained and can be filled by nonemptiness. -/
def Star.listWitness (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v)) : Prop :=
  ∃ l : Labeling Sigma, e.accepts l ∧ ∀ j, l (e.slot j) ∈ A (e.slot j)

@[simp] theorem Star.center_mem (e : Star V Sigma m) : e.center ∈ e.support := by
  classical
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

@[simp] theorem Star.leaf_mem (e : Star V Sigma m) (i : Fin m) :
    e.leaf i ∈ e.support := by
  classical
  exact Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩

theorem Star.accepts_of_agree (e : Star V Sigma m) {l q : Labeling Sigma}
    (hq : e.accepts q) (h : ∀ v ∈ e.support, l v = q v) : e.accepts l := by
  intro i
  rw [h _ (e.leaf_mem i), h _ e.center_mem]
  exact hq i

def choices (A : ∀ v, Finset (Sigma v)) (v : V) : Finset (Sigma v) := by
  classical
  exact if A v = ∅ then {Classical.choice (inferInstance : Nonempty (Sigma v))} else A v

theorem choices_nonempty (A : ∀ v, Finset (Sigma v)) (v : V) :
    (choices A v).Nonempty := by
  classical
  by_cases h : A v = ∅
  · simp [choices, h]
  · simpa [choices, h] using Finset.nonempty_iff_ne_empty.mpr h

def coordMass (A : ∀ v, Finset (Sigma v)) (v : V) (a : Sigma v) : ℝ := by
  classical
  exact if a ∈ choices A v then ((choices A v).card : ℝ)⁻¹ else 0

def labelMass (A : ∀ v, Finset (Sigma v)) (l : Labeling Sigma) : ℝ :=
  ∏ v, coordMass A v (l v)

theorem coordMass_nonneg (A : ∀ v, Finset (Sigma v)) (v : V) (a : Sigma v) :
    0 ≤ coordMass A v a := by
  classical
  unfold coordMass
  split_ifs <;> positivity

theorem coordMass_sum (A : ∀ v, Finset (Sigma v)) (v : V) :
    ∑ a, coordMass A v a = 1 := by
  classical
  have hc : ((choices A v).card : ℝ) ≠ 0 := by
    exact_mod_cast (choices_nonempty A v).card_pos.ne'
  simp [coordMass, hc]

theorem labelMass_nonneg (A : ∀ v, Finset (Sigma v)) (l : Labeling Sigma) :
    0 ≤ labelMass A l := Finset.prod_nonneg (fun v _ => coordMass_nonneg A v (l v))

theorem labelMass_sum (A : ∀ v, Finset (Sigma v)) : ∑ l, labelMass A l = 1 := by
  classical
  unfold labelMass
  rw [← Fintype.prod_sum]
  simp [coordMass_sum]

/-- Finite cylinder factorization for the actual global labeling distribution. -/
theorem cylinder_factorization (A : ∀ v, Finset (Sigma v))
    (P : (v : V) → Sigma v → Prop) :
    (∑ l : Labeling Sigma, if ∀ v, P v (l v) then labelMass A l else 0) =
      ∏ v, ∑ a, if P v a then coordMass A v a else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : ∀ v, P v (l v)
  · simp [h, labelMass]
  · rw [if_neg h]
    obtain ⟨v, hv⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)

theorem cylinder_pinned (A : ∀ v, Finset (Sigma v)) (s : Finset V)
    (q : Labeling Sigma) :
    (∑ l : Labeling Sigma, if ∀ v ∈ s, l v = q v then labelMass A l else 0) =
      ∏ v ∈ s, coordMass A v (q v) := by
  calc
    _ = ∏ v, ∑ a, if v ∈ s → a = q v then coordMass A v a else 0 := by
      convert cylinder_factorization A (fun v a => v ∈ s → a = q v) using 1
      · apply Finset.sum_congr rfl
        intro l _
        split_ifs <;> rfl
      · apply Finset.prod_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> rfl
    _ = _ := ?_
  have hi (v : V) : (∑ a, if v ∈ s → a = q v then coordMass A v a else 0) =
      if v ∈ s then coordMass A v (q v) else 1 := by
    by_cases h : v ∈ s <;> simp [h, coordMass_sum]
  simp_rw [hi]
  simp

def edgeProbability (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v)) : ℝ := by
  classical
  exact ∑ l, if e.accepts l then labelMass A l else 0

theorem edgeProbability_nonneg (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v)) :
    0 ≤ edgeProbability e A := by
  classical
  apply Finset.sum_nonneg
  intro l _
  split_ifs <;> first | exact labelMass_nonneg A l | exact le_rfl

/-- The exact distinct-vertex reciprocal lower bound, including repeated slots. -/
theorem edgeProbability_ge_distinct (e : Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) (hw : e.listWitness A) :
    ((∏ v ∈ e.support, (A v).card : ℕ) : ℝ)⁻¹ ≤ edgeProbability e A := by
  classical
  obtain ⟨q, hq, hA⟩ := hw
  have hmem (v : V) (hv : v ∈ e.support) : q v ∈ A v := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact hA j
  have hmass (v : V) (hv : v ∈ e.support) :
      coordMass A v (q v) = ((A v).card : ℝ)⁻¹ := by
    have hn : A v ≠ ∅ := Finset.ne_empty_of_mem (hmem v hv)
    simp [coordMass, choices, hn, hmem v hv]
  have hc := cylinder_pinned A e.support q
  simp_rw [Finset.prod_congr rfl hmass] at hc
  have hc' : (∑ l : Labeling Sigma,
      if ∀ v ∈ e.support, l v = q v then labelMass A l else 0) =
      ((∏ v ∈ e.support, (A v).card : ℕ) : ℝ)⁻¹ := by
    simpa only [Nat.cast_prod, Finset.prod_inv_distrib] using hc
  rw [← hc']
  apply Finset.sum_le_sum
  intro l _
  split_ifs with h ha ha
  · exact le_rfl
  · exact False.elim (ha (e.accepts_of_agree hq h))
  · exact labelMass_nonneg A l
  · exact le_rfl

def slotSum (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v)) : ℝ :=
  ∑ j, ((A (e.slot j)).card : ℝ)

theorem slotSum_nonneg (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v)) :
    0 ≤ slotSum e A := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Uniform AM-GM, stated with natural powers. -/
theorem slot_product_le (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v)) :
    (∏ j, ((A (e.slot j)).card : ℝ)) ≤ (slotSum e A / (m + 1)) ^ (m + 1) := by
  have hn : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin (m + 1)))
    (fun _ => (1 : ℝ)) (fun j => ((A (e.slot j)).card : ℝ))
    (by intros; norm_num) (by simpa using hn) (by intros; positivity)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg
    (fun _ _ => Nat.cast_nonneg _)) _) h (m + 1)
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    (Nat.succ_ne_zero m)] at hpow
  simpa [slotSum, Nat.cast_add, Nat.cast_one] using hpow

/-- The local decoder bound uses a coherent tuple and AM-GM, not a supplied probability law. -/
theorem edgeProbability_good (e : Star V Sigma m) (A : ∀ v, Finset (Sigma v))
    (rho : ℝ) (hrho : 0 < rho) (hw : e.listWitness A)
    (hsmall : slotSum e A ≤ 8 * (m + 1) * rho) :
    1 / (8 * rho) ^ (m + 1) ≤ edgeProbability e A := by
  classical
  have hpos (v : V) (hv : v ∈ e.support) : 1 ≤ (A v).card := by
    obtain ⟨q, _, hq⟩ := hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.card_pos.mpr ⟨_, hq j⟩)
  have hrepeat : (∏ v ∈ e.support, (A v).card) ≤ ∏ j, (A (e.slot j)).card :=
    Finset.prod_image_le_of_one_le hpos
  have hcast : ((∏ v ∈ e.support, (A v).card : ℕ) : ℝ) ≤
      ∏ j, ((A (e.slot j)).card : ℝ) := by exact_mod_cast hrepeat
  have hn : (0 : ℝ) < m + 1 := by positivity
  have havg : slotSum e A / (m + 1) ≤ 8 * rho := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [hsmall]
  have hb := hcast.trans ((slot_product_le e A).trans
    (pow_le_pow_left₀ (div_nonneg (slotSum_nonneg e A) hn.le) havg (m + 1)))
  have hd : (0 : ℝ) < ((∏ v ∈ e.support, (A v).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun v hv => lt_of_lt_of_le Nat.zero_lt_one (hpos v hv))
  exact (one_div_le_one_div_of_le hd hb).trans
    (by simpa [one_div] using (edgeProbability_ge_distinct e A hw))

/-- Occurrence weights retain zero-mass edges and duplicate slots. Positive-support
restriction is not needed for decoding and is NOT claimed as a typed compiler here. -/
def occurrenceWeight (p : E → ℝ) (edges : E → Star V Sigma m) (v : V) : ℝ := by
  classical
  exact (∑ e, p e * ∑ j : Fin (m + 1), if (edges e).slot j = v then 1 else 0) / (m + 1)

def listBudget (p : E → ℝ) (edges : E → Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) : ℝ :=
  ∑ v, occurrenceWeight p edges v * ((A v).card : ℝ)

theorem occurrenceWeight_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (edges : E → Star V Sigma m) (v : V) : 0 ≤ occurrenceWeight p edges v := by
  unfold occurrenceWeight
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg (hp e)
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> norm_num

theorem occurrenceWeight_sum (p : E → ℝ) (hnorm : ∑ e, p e = 1)
    (edges : E → Star V Sigma m) : ∑ v, occurrenceWeight p edges v = 1 := by
  classical
  have hn : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold occurrenceWeight
  rw [← Finset.sum_div, Finset.sum_comm]
  have hinner (e : E) :
      (∑ v, p e * ∑ j : Fin (m + 1), if (edges e).slot j = v then (1 : ℝ) else 0) =
        p e * (m + 1) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp
  simp_rw [hinner]
  rw [← Finset.sum_mul, hnorm, one_mul, div_self hn]

def alphabetMass (p : E → ℝ) (edges : E → Star V Sigma m) : ℝ :=
  ∑ v, occurrenceWeight p edges v * (Fintype.card (Sigma v) : ℝ)

theorem alphabetMass_ge_one (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hnorm : ∑ e, p e = 1) (edges : E → Star V Sigma m) :
    1 ≤ alphabetMass p edges := by
  rw [← occurrenceWeight_sum p hnorm edges]
  apply Finset.sum_le_sum
  intro v _
  have hc : (1 : ℝ) ≤ Fintype.card (Sigma v) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Sigma v))
  exact le_mul_of_one_le_right (occurrenceWeight_nonneg p hp edges v) hc

def variableWeight (p : E → ℝ) (edges : E → Star V Sigma m)
    (v : V) (_a : Sigma v) : ℝ := occurrenceWeight p edges v / alphabetMass p edges

def selectedWeight (p : E → ℝ) (edges : E → Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) : ℝ :=
  ∑ v, ∑ a ∈ A v, variableWeight p edges v a

theorem selectedWeight_eq (p : E → ℝ) (edges : E → Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) :
    selectedWeight p edges A = listBudget p edges A / alphabetMass p edges := by
  classical
  unfold selectedWeight variableWeight listBudget
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact normalized weight budget, with s = 1 / Lambda. -/
theorem selectedWeight_budget_iff (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hnorm : ∑ e, p e = 1) (edges : E → Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) (rho : ℝ) :
    selectedWeight p edges A ≤ rho * (1 / alphabetMass p edges) ↔
      listBudget p edges A ≤ rho := by
  have hL : 0 < alphabetMass p edges := lt_of_lt_of_le zero_lt_one
    (alphabetMass_ge_one p hp hnorm edges)
  rw [selectedWeight_eq, ← div_eq_mul_one_div, div_le_div_iff_of_pos_right hL]

theorem mean_slotSum (p : E → ℝ) (edges : E → Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) :
    ∑ e, p e * slotSum (edges e) A = (m + 1) * listBudget p edges A := by
  classical
  have hn : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold listBudget occurrenceWeight slotSum
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [mul_div_cancel₀ _ hn]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- Finite event mass, defined on the actual edge-occurrence law. -/
def eventMass (p : E → ℝ) (P : E → Prop) : ℝ := by
  classical
  exact ∑ e, if P e then p e else 0

theorem eventMass_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (P : E → Prop) :
    0 ≤ eventMass p P := by
  classical
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> simp_all

/-- Direct finite Markov bound derived from the actual list budget. -/
theorem bad_mass_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (edges : E → Star V Sigma m) (A : ∀ v, Finset (Sigma v))
    (rho : ℝ) (hrho : 0 < rho) (hbudget : listBudget p edges A ≤ rho) :
    eventMass p (fun e => 8 * (m + 1) * rho < slotSum (edges e) A) ≤ 1 / 8 := by
  classical
  let T : ℝ := 8 * (m + 1) * rho
  have hT : 0 < T := by dsimp [T]; positivity
  have hmark : T * eventMass p (fun e => T < slotSum (edges e) A) ≤
      ∑ e, p e * slotSum (edges e) A := by
    unfold eventMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    by_cases h : T < slotSum (edges e) A
    · simp only [if_pos h]
      nlinarith [mul_le_mul_of_nonneg_left h.le (hp e)]
    · simp only [if_neg h, mul_zero]
      exact mul_nonneg (hp e) (slotSum_nonneg _ _)
  rw [mean_slotSum] at hmark
  have hmean : (m + 1 : ℝ) * listBudget p edges A ≤ (m + 1) * rho :=
    mul_le_mul_of_nonneg_left hbudget (by positivity)
  have hd : (m + 1 : ℝ) * rho = T * (1 / 8) := by dsimp [T]; ring
  rw [hd] at hmean
  nlinarith [hmark.trans hmean]

theorem good_mass_ge (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (edges : E → Star V Sigma m) (A : ∀ v, Finset (Sigma v))
    (rho : ℝ) (hrho : 0 < rho) (hbudget : listBudget p edges A ≤ rho) :
    eventMass p (fun e => (edges e).listWitness A) - 1 / 8 ≤
      eventMass p (fun e => (edges e).listWitness A ∧
        slotSum (edges e) A ≤ 8 * (m + 1) * rho) := by
  classical
  have hsplit : eventMass p (fun e => (edges e).listWitness A) ≤
      eventMass p (fun e => (edges e).listWitness A ∧
        slotSum (edges e) A ≤ 8 * (m + 1) * rho) +
      eventMass p (fun e => 8 * (m + 1) * rho < slotSum (edges e) A) := by
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    by_cases hw : (edges e).listWitness A <;>
      by_cases hs : slotSum (edges e) A ≤ 8 * (m + 1) * rho <;>
      simp [hw, hs, not_lt_of_ge, lt_of_not_ge, hp e, *]
  linarith [bad_mass_le p hp edges A rho hrho hbudget]

def score (p : E → ℝ) (edges : E → Star V Sigma m) (l : Labeling Sigma) : ℝ :=
  eventMass p (fun e => (edges e).accepts l)

/-- Full decoding target as an attaining deterministic labeling, hence also a game-value bound.
The budget is the derived occurrence-weight list budget, never a mean/probability oracle. -/
theorem exists_decoding (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (edges : E → Star V Sigma m) (A : ∀ v, Finset (Sigma v))
    (rho : ℝ) (hrho : 0 < rho) (hbudget : listBudget p edges A ≤ rho) :
    ∃ l : Labeling Sigma,
      (eventMass p (fun e => (edges e).listWitness A) - 1 / 8) /
        (8 * rho) ^ (m + 1) ≤ score p edges l := by
  classical
  let D : ℝ := (8 * rho) ^ (m + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  let G : E → Prop := fun e => (edges e).listWitness A ∧
    slotSum (edges e) A ≤ 8 * (m + 1) * rho
  have hlocal : eventMass p G / D ≤ ∑ e, p e * edgeProbability (edges e) A := by
    unfold eventMass
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro e _
    by_cases h : G e
    · simp only [if_pos h]
      have hb := mul_le_mul_of_nonneg_left
        (edgeProbability_good (edges e) A rho hrho h.1 h.2) (hp e)
      simpa [D, div_eq_mul_inv] using hb
    · simp only [if_neg h, zero_div]
      exact mul_nonneg (hp e) (edgeProbability_nonneg _ _)
  have hexchange : (∑ e, p e * edgeProbability (edges e) A) =
      ∑ l, labelMass A l * score p edges l := by
    unfold edgeProbability score eventMass
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  obtain ⟨l, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Labeling Sigma)) (score p edges) Finset.univ_nonempty
  refine ⟨l, ?_⟩
  have havg : (∑ q, labelMass A q * score p edges q) ≤ score p edges l := by
    calc
      _ ≤ ∑ q, labelMass A q * score p edges l := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hmax q (Finset.mem_univ _)) (labelMass_nonneg A q)
      _ = _ := by rw [← Finset.sum_mul, labelMass_sum, one_mul]
  have hgood := good_mass_ge p hp edges A rho hrho hbudget
  rw [hexchange] at hlocal
  exact (div_le_div_of_nonneg_right hgood hD.le).trans (hlocal.trans havg)

/-- Integer-power parameter endpoint: equality at 3/4 is allowed. -/
theorem witness_mass_le_three_quarters (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (edges : E → Star V Sigma m) (A : ∀ v, Finset (Sigma v))
    (rho zeta : ℝ) (hrho : 0 < rho) (hbudget : listBudget p edges A ≤ rho)
    (hvalue : ∀ l : Labeling Sigma, score p edges l ≤ zeta)
    (hparam : (8 * rho) ^ (m + 1) * zeta ≤ 5 / 8) :
    eventMass p (fun e => (edges e).listWitness A) ≤ 3 / 4 := by
  obtain ⟨l, hl⟩ := exists_decoding p hp edges A rho hrho hbudget
  have hD : 0 < (8 * rho) ^ (m + 1) := by positivity
  have h := (div_le_iff₀ hD).mp (hl.trans (hvalue l))
  nlinarith

/-- The exact weighted-selection input of the handoff, with no supplied mean bound. -/
theorem exists_decoding_of_selectedWeight (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hnorm : ∑ e, p e = 1) (edges : E → Star V Sigma m)
    (A : ∀ v, Finset (Sigma v)) (rho : ℝ) (hrho : 0 < rho)
    (hbudget : selectedWeight p edges A ≤ rho * (1 / alphabetMass p edges)) :
    ∃ l : Labeling Sigma,
      (eventMass p (fun e => (edges e).listWitness A) - 1 / 8) /
        (8 * rho) ^ (m + 1) ≤ score p edges l :=
  exists_decoding p hp edges A rho hrho
    ((selectedWeight_budget_iff p hp hnorm edges A rho).mp hbudget)

end
end PvNP.RealizableHardness.StarListDecoding
