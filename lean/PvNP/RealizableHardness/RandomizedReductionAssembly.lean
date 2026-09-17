import PvNP.RealizableHardness.RandomizedReduction
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.List.OfFn

/-! UNCOMPILED source. Exact dynamic-prefix probability and machine-backed flat
seed composition. This does not supply an encoded CMMSA executor. -/
namespace PvNP.RealizableHardness.RandomizedReductionAssembly
open Complexity RandomizedReduction
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def prob {n : ℕ} (P : (Fin n → Bool) → Prop) : ℚ :=
  eventProb (Finset.univ.filter P)

lemma prob_average {n : ℕ} (P : (Fin n → Bool) → Prop) :
    prob P = (∑ u : Fin n → Bool, if P u then (1 : ℚ) else 0) / 2^n := by
  unfold prob eventProb
  congr 1
  simp [← Finset.sum_filter]

lemma prob_nonneg {n : ℕ} (P : (Fin n → Bool) → Prop) : 0 ≤ prob P :=
  eventProb_nonneg _

/-- Exact disintegration; the second predicate may depend on the first seed. -/
theorem block_disintegration (n B : ℕ)
    (E : (Fin n → Bool) → (Fin B → Bool) → Prop) :
    prob (fun w : Fin (n+B) → Bool => E (blockFst n B w) (blockSnd n B w)) =
      (∑ u : Fin n → Bool, prob (E u)) / 2^n := by
  rw [prob_average]
  have he := (blockEquiv n B).sum_comp
    (fun uv => if E uv.1 uv.2 then (1 : ℚ) else 0)
  change (∑ w, (if E (blockEquiv n B w).1 (blockEquiv n B w).2 then (1 : ℚ) else 0)) /
    2^(n+B) = _
  rw [he, Fintype.sum_prod_type]
  simp_rw [prob_average]
  rw [← Finset.sum_div, pow_add]
  field_simp
  <;> ring

lemma ofFn_blocks (n B : ℕ) (w : Fin (n+B) → Bool) :
    List.ofFn w = List.ofFn (blockFst n B w) ++ List.ofFn (blockSnd n B w) := by
  have hf : blockFst n B w = fun i : Fin n => w (Fin.castLE (by omega) i) := by
    funext i
    simp only [blockFst, blockEquiv, Equiv.trans_apply,
      Equiv.sumArrowEquivProdArrow_apply_fst]
    congr 1
  have hs : blockSnd n B w = fun i : Fin B => w (Fin.natAdd n i) := by
    funext i
    exact blockSnd_apply n B w i
  rw [hf, hs]
  exact List.ofFn_add

/-- List.take is exactly the finite prefix, including zero and full width. -/
lemma ofFn_prefix {k B : ℕ} (hk : k ≤ B) (w : Fin B → Bool) :
    (List.ofFn w).take k = List.ofFn (Fin.take k hk w) :=
  (Fin.ofFn_take_eq_take_ofFn hk w).symm

lemma prefix_probability {k B : ℕ} (hk : k ≤ B)
    (P : (Fin k → Bool) → Prop) :
    prob (fun w : Fin B → Bool => P (Fin.take k hk w)) = prob P := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := eventProb_block (a := k) (b := t) P (fun _ => True)
  change prob (fun w : Fin (k+t) → Bool => P (blockFst k t w)) = _
  simpa [prob] using h

/-- Padding cancellation for the actual second executor, at its actual output length. -/
theorem padded_success (S : SeededMap) (y : Bits) (B : ℕ)
    (hk : S.coinCount y.length ≤ B) (T : Set Bits) :
    prob (fun v : Fin B → Bool =>
      S.run (pair y ((List.ofFn v).take (S.ruler y).length)) ∈ T) =
      successProbability S y T := by
  simp_rw [S.ruler_length, ofFn_prefix hk]
  exact prefix_probability hk (fun v => S.apply y (List.ofFn v) ∈ T)

/-- The first random output controls the second prefix length; its exact
conditional law is averaged, rather than replaced by independent resampling. -/
theorem execute_disintegration (R S : SeededMap) (x : Bits) (B : ℕ)
    (hB : ∀ u : Fin (R.coinCount x.length) → Bool,
      S.coinCount (R.apply x (List.ofFn u)).length ≤ B) (T : Set Bits) :
    prob (fun w : Fin (R.coinCount x.length+B) → Bool =>
      execute R.run S.run S.ruler
        (pair (pair x (List.ofFn (blockFst _ B w)))
          (List.ofFn (blockSnd _ B w))) ∈ T) =
      (∑ u : Fin (R.coinCount x.length) → Bool,
        successProbability S (R.apply x (List.ofFn u)) T) / 2^(R.coinCount x.length) := by
  simp_rw [execute_pair]
  rw [block_disintegration (R.coinCount x.length) B
    (fun u v => S.run (pair (R.run (pair x (List.ofFn u)))
      ((List.ofFn v).take (S.ruler (R.run (pair x (List.ofFn u)))).length)) ∈ T)]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact padded_success S (R.apply x (List.ofFn u)) B (hB u) T

/-- Data constructed from FP evidence, not a supplied final runtime premise. -/
structure Padding (R S : SeededMap) where
  polynomial : Polynomial ℕ
  ruler : Bits → Bits
  ruler_fp : ruler ∈ FP
  ruler_length : ∀ x, (ruler x).length = polynomial.eval x.length
  enough : ∀ x u : Bits, u.length = R.coinCount x.length →
    S.coinCount (R.apply x u).length ≤ polynomial.eval x.length

theorem exists_padding (R S : SeededMap) : Nonempty (Padding R S) := by
  obtain ⟨a, ha⟩ := R.coinCount_poly
  obtain ⟨p, q, hpq⟩ := second_coin_padding R.run_fp S.ruler_fp a
  let B := q.comp (p.comp (pairEnvelope a))
  obtain ⟨ruler, hruler, hlen⟩ := Cobham.exists_exact_ruler B
  refine ⟨⟨B, ruler, hruler, hlen, ?_⟩⟩
  intro x u hu
  have h := hpq x u (by rw [hu]; exact ha x.length)
  simpa only [S.ruler_length, SeededMap.apply] using h

def flatFirst (R : SeededMap) (z : Bits) : Bits :=
  (pairSnd z).take (R.ruler (pairFst z)).length

/-- Suffix extraction is reverse/take/reverse, with an actual FP ruler. -/
def flatSecond {R S : SeededMap} (P : Padding R S) (z : Bits) : Bits :=
  ((pairSnd z).reverse.take (P.ruler (pairFst z)).length).reverse

def flatInput (R S : SeededMap) (P : Padding R S) (z : Bits) : Bits :=
  pair (pair (pairFst z) (flatFirst R z)) (flatSecond P z)

def flatRun (R S : SeededMap) (P : Padding R S) (z : Bits) : Bits :=
  execute R.run S.run S.ruler (flatInput R S P z)

theorem flatFirst_fp (R : SeededMap) : flatFirst R ∈ FP :=
  Cobham.takeLenFn_mem_FP (mem_FP_comp pairFst_mem_FP R.ruler_fp) pairSnd_mem_FP

theorem flatSecond_fp {R S : SeededMap} (P : Padding R S) : flatSecond P ∈ FP := by
  exact mem_FP_comp
    (Cobham.takeLenFn_mem_FP (mem_FP_comp pairFst_mem_FP P.ruler_fp)
      (mem_FP_comp pairSnd_mem_FP reverse_mem_FP)) reverse_mem_FP

theorem flatRun_fp (R S : SeededMap) (P : Padding R S) : flatRun R S P ∈ FP := by
  exact mem_FP_comp
    (mem_FP_pair (mem_FP_pair pairFst_mem_FP (flatFirst_fp R)) (flatSecond_fp P))
    (execute_fp R.run_fp S.run_fp S.ruler_fp)

def compose (R S : SeededMap) (P : Padding R S) : SeededMap where
  run := flatRun R S P
  run_fp := flatRun_fp R S P
  ruler := fun x => R.ruler x ++ P.ruler x
  ruler_fp := Cobham.appendFn_mem_FP R.ruler_fp P.ruler_fp
  coinCount n := R.coinCount n + P.polynomial.eval n
  ruler_length x := by simp [R.ruler_length, P.ruler_length]

theorem flat_seed_execution (R S : SeededMap) (P : Padding R S) (x : Bits)
    (w : Fin ((compose R S P).coinCount x.length) → Bool) :
    (compose R S P).apply x (List.ofFn w) =
      execute R.run S.run S.ruler
        (pair (pair x (List.ofFn (blockFst (R.coinCount x.length) (P.polynomial.eval x.length) w)))
          (List.ofFn (blockSnd (R.coinCount x.length) (P.polynomial.eval x.length) w))) := by
  have he := ofFn_blocks (R.coinCount x.length) (P.polynomial.eval x.length) w
  simp only [SeededMap.apply, compose, flatRun, flatInput, flatFirst, flatSecond,
    pairFst_pair, pairSnd_pair, R.ruler_length, P.ruler_length]
  rw [he]
  simp

theorem compose_probability (R S : SeededMap) (P : Padding R S) (x : Bits) (T : Set Bits) :
    successProbability (compose R S P) x T =
      (∑ u : Fin (R.coinCount x.length) → Bool,
        successProbability S (R.apply x (List.ofFn u)) T) / 2^(R.coinCount x.length) := by
  change prob (fun w => (compose R S P).apply x (List.ofFn w) ∈ T) = _
  simp_rw [flat_seed_execution]
  exact execute_disintegration R S x (P.polynomial.eval x.length)
    (fun u => P.enough x (List.ofFn u) (by simp)) T

/-- Each promise side uses only correctly promised intermediate outputs.
Other first outputs contribute nonnegative probability. -/
theorem compose_success_lower (R S : SeededMap) (P : Padding R S)
    (x : Bits) (M T : Set Bits) (e₁ e₂ : ℚ)
    (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₂1 : e₂ ≤ 1)
    (hR : 1-e₁ ≤ successProbability R x M)
    (hS : ∀ y ∈ M, 1-e₂ ≤ successProbability S y T) :
    1-(e₁+e₂) ≤ successProbability (compose R S P) x T := by
  have hpoint (u : Fin (R.coinCount x.length) → Bool) :
      (1-e₂) * (if R.apply x (List.ofFn u) ∈ M then (1 : ℚ) else 0) ≤
        successProbability S (R.apply x (List.ofFn u)) T := by
    by_cases hu : R.apply x (List.ofFn u) ∈ M
    · simpa [hu] using hS _ hu
    · have hn : 0 ≤ successProbability S (R.apply x (List.ofFn u)) T := by
        unfold successProbability
        exact eventProb_nonneg _
      simpa only [hu, ite_false, mul_zero] using hn
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hpoint u)
  have hd := div_le_div_of_nonneg_right hs
    (show (0 : ℚ) ≤ 2^(R.coinCount x.length) by positivity)
  rw [compose_probability]
  have hm : successProbability R x M =
      (∑ u : Fin (R.coinCount x.length) → Bool,
        if R.apply x (List.ofFn u) ∈ M then (1 : ℚ) else 0) / 2^(R.coinCount x.length) :=
    prob_average _
  rw [← Finset.mul_sum, mul_div_assoc, ← hm] at hd
  have hl := mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr he₂1)
  nlinarith [mul_nonneg he₁ he₂]

theorem compose_preserves (R S : SeededMap) (P : Padding R S)
    (source middle target : PromiseProblem) (ey₁ en₁ ey₂ en₂ : ℚ)
    (hy₁ : 0 ≤ ey₁) (hn₁ : 0 ≤ en₁) (hy₂ : 0 ≤ ey₂) (hn₂ : 0 ≤ en₂)
    (hy₂1 : ey₂ ≤ 1) (hn₂1 : en₂ ≤ 1)
    (hR : Preserves R source middle ey₁ en₁)
    (hS : Preserves S middle target ey₂ en₂) :
    Preserves (compose R S P) source target (ey₁+ey₂) (en₁+en₂) := by
  constructor
  · intro x hx
    exact compose_success_lower R S P x middle.yesInstances target.yesInstances
      ey₁ ey₂ hy₁ hy₂ hy₂1 (hR.1 x hx) hS.1
  · intro x hx
    exact compose_success_lower R S P x middle.noInstances target.noInstances
      en₁ en₂ hn₁ hn₂ hn₂1 (hR.2 x hx) hS.2

/-- Actual machine clock versus original input length under the proved coin
schedule. This includes every seed of that length, without a success premise. -/
theorem scheduled_machine (R : SeededMap) :
    ∃ (k : ℕ) (tm : TM k) (rawClock inputClock : Polynomial ℕ),
      tm.ComputesInTime R.run rawClock.eval ∧
      ∀ x seed : Bits, seed.length = R.coinCount x.length →
        rawClock.eval (pair x seed).length ≤ inputClock.eval x.length := by
  obtain ⟨k, tm, q, hq⟩ := mem_FP_iff_computesInTime_polynomial.mp R.run_fp
  obtain ⟨a, ha⟩ := R.coinCount_poly
  refine ⟨k, tm, q, q.comp (pairEnvelope a), hq, ?_⟩
  intro x seed hs
  have hp : (pair x seed).length ≤ (pairEnvelope a).eval x.length := by
    simp only [pair_length, pairEnvelope, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [hs]
    have := ha x.length
    omega
  simpa only [Polynomial.eval_comp] using polynomial_eval_mono_nat q hp

/-- Both polynomially bounded coins and an actual all-input halting TM are
derived for the composite, rather than supplied as final contracts. -/
theorem exists_composition (R S : SeededMap) :
    ∃ P : Padding R S,
      (∃ p : Polynomial ℕ, ∀ n, (compose R S P).coinCount n ≤ p.eval n) ∧
      (∃ (k : ℕ) (tm : TM k) (rawClock inputClock : Polynomial ℕ),
        tm.ComputesInTime (compose R S P).run rawClock.eval ∧
        ∀ x seed : Bits, seed.length = (compose R S P).coinCount x.length →
          rawClock.eval (pair x seed).length ≤ inputClock.eval x.length) := by
  obtain ⟨P⟩ := exists_padding R S
  exact ⟨P, (compose R S P).coinCount_poly, scheduled_machine (compose R S P)⟩

/-- The same constructed map has the probability guarantees, polynomial coins,
and actual machine clock. Source and target promises are actual string sets;
this generic closure does not assert that any particular promise is NP-hard. -/
theorem exists_preserving_composition (R S : SeededMap)
    (source middle target : PromiseProblem) (ey₁ en₁ ey₂ en₂ : ℚ)
    (hy₁ : 0 ≤ ey₁) (hn₁ : 0 ≤ en₁) (hy₂ : 0 ≤ ey₂) (hn₂ : 0 ≤ en₂)
    (hy₂1 : ey₂ ≤ 1) (hn₂1 : en₂ ≤ 1)
    (hR : Preserves R source middle ey₁ en₁)
    (hS : Preserves S middle target ey₂ en₂) :
    ∃ C : SeededMap,
      Preserves C source target (ey₁+ey₂) (en₁+en₂) ∧
      (∃ p : Polynomial ℕ, ∀ n, C.coinCount n ≤ p.eval n) ∧
      (∃ (k : ℕ) (tm : TM k) (rawClock inputClock : Polynomial ℕ),
        tm.ComputesInTime C.run rawClock.eval ∧
        ∀ x seed : Bits, seed.length = C.coinCount x.length →
          rawClock.eval (pair x seed).length ≤ inputClock.eval x.length) := by
  obtain ⟨P, hcoins, hclock⟩ := exists_composition R S
  exact ⟨compose R S P,
    compose_preserves R S P source middle target ey₁ en₁ ey₂ en₂
      hy₁ hn₁ hy₂ hn₂ hy₂1 hn₂1 hR hS, hcoins, hclock⟩

end
end PvNP.RealizableHardness.RandomizedReductionAssembly
