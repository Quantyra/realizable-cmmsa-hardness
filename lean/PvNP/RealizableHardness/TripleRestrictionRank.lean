import PvNP.RealizableHardness.FiniteSampling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FinCases

/-! Concrete independent triple restriction and its unconditional numeric
codimension failure bound. Author exports passed; independent review is pending.
No posterior independence is asserted. -/
namespace PvNP.RealizableHardness.TripleRestrictionRank
open scoped BigOperators

abbrev BlockChoice := Option (Fin 3)
abbrev Draw (J : ℕ) := Fin J → BlockChoice
abbrev Coord (J : ℕ) := Fin J × Fin 3
abbrev Vector (J : ℕ) := Coord J → ZMod 2
abbrev Coeff (c : ℕ) := Fin c → ZMod 2

/-- `none` keeps all three; `some k` keeps the singleton k. -/
def blockMass (β : ℚ) : BlockChoice → ℚ
  | none => 1 - β
  | some _ => β / 3

def kept (d : Draw J) (r : Coord J) : Prop :=
  d r.1 = none ∨ d r.1 = some r.2

noncomputable def probability (β : ℚ) (E : Draw J → Prop) : ℚ := by
  classical
  exact ∑ d, if E d then FiniteSampling.trialMass (blockMass β) J d else 0

lemma blockMass_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (a : BlockChoice) : 0 ≤ blockMass β a := by
  cases a with
  | none => simp only [blockMass]; linarith
  | some k => simp only [blockMass]; positivity

lemma blockMass_sum (β : ℚ) : ∑ a, blockMass β a = 1 := by
  simp [Fintype.sum_option, blockMass, Fin.sum_univ_succ]
  <;> ring

lemma drawMass_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (d : Draw J) :
    0 ≤ FiniteSampling.trialMass (blockMass β) J d :=
  FiniteSampling.trialMass_nonneg _ _ (blockMass_nonneg β hβ hβ1) d

lemma probability_univ (β : ℚ) : probability (J := J) β (fun _ => True) = 1 := by
  simp only [probability, if_true]
  exact FiniteSampling.trialMass_sum _ _ (blockMass_sum β)

lemma probability_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (E : Draw J → Prop) : 0 ≤ probability β E := by
  classical
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact drawMass_nonneg β hβ hβ1 d
  · exact le_rfl

lemma probability_mono (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (E F : Draw J → Prop) (hEF : ∀ d, E d → F d) :
    probability β E ≤ probability β F := by
  classical
  apply Finset.sum_le_sum
  intro d _
  by_cases he : E d
  · simp [he, hEF d he]
  · simp only [he, if_false]
    split_ifs
    · exact drawMass_nonneg β hβ hβ1 d
    · exact le_rfl

/-- A one-block cylinder is derived from the full concrete product law. -/
lemma block_marginal (β : ℚ) (j : Fin J) (e : BlockChoice → Bool) :
    probability β (fun d => e (d j) = true) =
      ∑ a, if e a then blockMass β a else 0 := by
  classical
  let events : Fin J → BlockChoice → Bool := fun i a => if i = j then e a else true
  have hc := FiniteSampling.trial_event_factorization (blockMass β) J events
  have he : ∀ d : Draw J, (∀ i, events i (d i) = true) ↔ e (d j) = true := by
    intro d
    constructor
    · intro h; simpa [events] using h j
    · intro h i; by_cases hi : i = j <;> simp [events, hi, h]
  have hr : (∏ i : Fin J, ∑ a, if events i a then blockMass β a else 0) =
      ∏ i : Fin J, if i = j then (∑ a, if e a then blockMass β a else 0) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = j
    · simp only [events, if_pos hi]
    · simp only [events, if_neg hi, Bool.true_eq, if_true]
      exact blockMass_sum β
  simp only [he] at hc
  rw [hr] at hc
  rw [Fintype.prod_ite_eq'] at hc
  calc
    probability β (fun d => e (d j) = true) =
        ∑ d : Fin J → BlockChoice, if e (d j) = true then
          FiniteSampling.trialMass (blockMass β) J d else 0 := by
      unfold probability
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : e (d j) = true
      · simp only [if_pos hd]
      · simp only [if_neg hd]
    _ = _ := hc

lemma drop_marginal (β : ℚ) (j : Fin J) :
    probability β (fun d : Draw J => (d j).isSome = true) = β := by
  rw [block_marginal]
  simp [Fintype.sum_option, blockMass, Fin.sum_univ_succ]
  <;> ring

/-- Removing a particular coordinate requires dropping its block. -/
lemma coordinate_removed_bound (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (r : Coord J) : probability β (fun d => ¬ kept d r) ≤ β := by
  apply (probability_mono β hβ hβ1 _ _ (fun d h => ?_)).trans (le_of_eq (drop_marginal β r.1))
  cases hd : d r.1 with
  | none => exact False.elim (h (Or.inl hd))
  | some k => simp [hd]

/-- The actual coordinate subspace selected by the draw. -/
noncomputable def retained (d : Draw J) : Submodule (ZMod 2) (Vector J) where
  carrier := {v | ∀ r, ¬ kept d r → v r = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy r hr; simp [hx r hr, hy r hr]
  smul_mem' := by intro a x hx r hr; simp [hx r hr]

/-- Restrict the coefficient vector of a linear functional to kept coordinates.
Zero padding identifies this with a coefficient vector in the original space. -/
noncomputable def restrict (d : Draw J) : Vector J →ₗ[ZMod 2] Vector J := by
  classical
  exact {
    toFun := fun v r => if kept d r then v r else 0
    map_add' := by intro x y; funext r; by_cases h : kept d r <;> simp [h]
    map_smul' := by intro a x; funext r; by_cases h : kept d r <;> simp [h] }

lemma restrict_eq_zero_iff (d : Draw J) (v : Vector J) :
    restrict d v = 0 ↔ ∀ r, kept d r → v r = 0 := by
  classical
  constructor
  · intro h r hr
    simpa [restrict, hr] using congrFun h r
  · intro h
    funext r
    by_cases hr : kept d r <;> simp [restrict, hr, h r]

/-- R takes row coefficients to their row combination. Its injectivity is
exactly independence of the c rows before restriction. -/
def FullRowRank (R : Coeff c →ₗ[ZMod 2] Vector J) : Prop := Function.Injective R

noncomputable def restrictedRows (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :=
  (restrict d).comp R

def rowVanishes (R : Coeff c →ₗ[ZMod 2] Vector J) (u : Coeff c) (d : Draw J) : Prop :=
  ∀ r, kept d r → R u r = 0

def badRows (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) : Prop :=
  ∃ u, u ≠ 0 ∧ rowVanishes R u d

lemma rowVanishes_iff (R : Coeff c →ₗ[ZMod 2] Vector J) (u : Coeff c) (d : Draw J) :
    rowVanishes R u d ↔ restrictedRows R d u = 0 :=
  (restrict_eq_zero_iff d (R u)).symm

lemma goodRows_injective (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J)
    (h : ¬ badRows R d) : Function.Injective (restrictedRows R d) := by
  intro x y hxy
  have hz : restrictedRows R d (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have heq : x - y = 0 := by
    by_contra hn
    exact h ⟨x - y, hn, (rowVanishes_iff R (x - y) d).mpr hz⟩
  exact sub_eq_zero.mp heq

lemma badRows_iff_not_injective (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :
    badRows R d ↔ ¬ Function.Injective (restrictedRows R d) := by
  classical
  constructor
  · rintro ⟨u, hu, hv⟩ hi
    apply hu
    apply hi
    simpa using (rowVanishes_iff R u d).mp hv
  · intro hn
    by_contra hb
    exact hn (goodRows_injective R d hb)

lemma goodRows_rank (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J)
    (h : ¬ badRows R d) : Module.finrank (ZMod 2) (LinearMap.range (restrictedRows R d)) = c := by
  rw [LinearMap.finrank_range_of_inj (goodRows_injective R d h)]
  simp [Coeff, Module.finrank_pi]

lemma rowVanishes_probability (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (R : Coeff c →ₗ[ZMod 2] Vector J) (hR : FullRowRank R)
    (u : Coeff c) (hu : u ≠ 0) :
    probability (J := J) β (rowVanishes (J := J) (c := c) R u) ≤ β := by
  classical
  have hRu : R u ≠ 0 := by
    intro h
    exact hu (hR (h.trans (map_zero R).symm))
  have hex : ∃ r, R u r ≠ 0 := by
    by_contra h
    apply hRu
    funext r
    exact not_ne_iff.mp (not_exists.mp h r)
  obtain ⟨r, hr⟩ := hex
  have hsub : ∀ d : Draw J, rowVanishes R u d → ¬ kept d r :=
    fun d hv hk => hr (hv r hk)
  exact (probability_mono β hβ hβ1 (rowVanishes R u) (fun d => ¬ kept d r) hsub).trans
    (coordinate_removed_bound β hβ hβ1 r)

/-- Finite union bound; no independence assumption about the union's events. -/
lemma probability_cover {A : Type*} [DecidableEq A] (β : ℚ)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (s : Finset A)
    (E : Draw J → Prop) (F : A → Draw J → Prop)
    (hcov : ∀ d, E d → ∃ a ∈ s, F a d) :
    probability β E ≤ ∑ a ∈ s, probability β (F a) := by
  classical
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : E d
  · obtain ⟨a, ha, had⟩ := hcov d hd
    simp only [if_pos hd]
    calc
      _ = (if F a d then FiniteSampling.trialMass (blockMass β) J d else 0) := by simp [had]
      _ ≤ _ := by
        apply Finset.single_le_sum (f := fun b => if F b d then
          FiniteSampling.trialMass (blockMass β) J d else 0) _ ha
        intro b _
        split_ifs
        · exact drawMass_nonneg β hβ hβ1 d
        · exact le_rfl
  · simp only [if_neg hd]
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact drawMass_nonneg β hβ hβ1 d
    · exact le_rfl

/-- The exact manuscript unconditional bound, with c=0 allowed. -/
theorem badRows_probability (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (R : Coeff c →ₗ[ZMod 2] Vector J) (hR : FullRowRank R) :
    probability β (badRows R) ≤ ((2 ^ c - 1 : ℕ) : ℚ) * β := by
  classical
  let s : Finset (Coeff c) := Finset.univ.erase 0
  have hcover : ∀ d, badRows R d → ∃ u ∈ s, rowVanishes R u d := by
    rintro d ⟨u, hu, hv⟩
    exact ⟨u, by simp [s, hu], hv⟩
  calc
    _ ≤ ∑ u ∈ s, probability β (rowVanishes R u) :=
      probability_cover β hβ hβ1 s _ _ hcover
    _ ≤ ∑ _u ∈ s, β := by
      apply Finset.sum_le_sum
      intro u hu
      exact rowVanishes_probability β hβ hβ1 R hR u (Finset.mem_erase.mp hu).1
    _ = _ := by simp [s, Coeff, Fintype.card_fun, ZMod.card]

/-- Failure of full row rank of the restricted, zero-padded actual matrix. -/
theorem restricted_rank_failure_probability (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (R : Coeff c →ₗ[ZMod 2] Vector J) (hR : FullRowRank R) :
    probability β (fun d => Module.finrank (ZMod 2)
      (LinearMap.range (restrictedRows R d)) ≠ c) ≤ ((2 ^ c - 1 : ℕ) : ℚ) * β := by
  apply (probability_mono β hβ hβ1 _ _ (fun d hd => ?_)).trans
    (badRows_probability β hβ hβ1 R hR)
  by_contra hb
  exact hd (goodRows_rank R d hb)

/-- Pair a coefficient vector with an actual vector in U. -/
def evaluate (v x : Vector J) : ZMod 2 := ∑ r, v r * x r

/-- Vanishing of retained coefficients is exactly vanishing of the functional
on the actual selected coordinate subspace, not a substitute abstract event. -/
lemma vanishing_on_retained_iff (d : Draw J) (v : Vector J) :
    (∀ r, kept d r → v r = 0) ↔
      ∀ x : Vector J, x ∈ retained d → evaluate v x = 0 := by
  classical
  constructor
  · intro hv x hx
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : kept d r
    · simp [hv r hr]
    · simp [hx r hr]
  · intro hv r hr
    let x : Vector J := fun t => if t = r then 1 else 0
    have hx : x ∈ retained d := by
      intro t ht
      by_cases htr : t = r
      · subst t; exact False.elim (ht hr)
      · simp [x, htr]
    have he := hv x hx
    simpa [evaluate, x, mul_ite] using he

lemma rowVanishes_on_retained (R : Coeff c →ₗ[ZMod 2] Vector J)
    (u : Coeff c) (d : Draw J) :
    rowVanishes R u d ↔ ∀ x : Vector J, x ∈ retained d → evaluate (R u) x = 0 :=
  vanishing_on_retained_iff d (R u)

/-- An explicit matrix constructor: R(u) is the sum of u_i times row i. -/
noncomputable def rowCombination (A : Fin c → Coord J → ZMod 2) :
    Coeff c →ₗ[ZMod 2] Vector J where
  toFun := fun u r => ∑ i, u i * A i r
  map_add' := by
    intro x y
    funext r
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

/-- Matrix-form export of the unconditional rank failure bound. -/
theorem matrix_restricted_rank_failure_probability (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (A : Fin c → Coord J → ZMod 2) (hA : FullRowRank (rowCombination A)) :
    probability β (fun d => Module.finrank (ZMod 2)
      (LinearMap.range (restrictedRows (rowCombination A) d)) ≠ c) ≤
      ((2 ^ c - 1 : ℕ) : ℚ) * β :=
  restricted_rank_failure_probability β hβ hβ1 (rowCombination A) hA

lemma evaluate_add_left (v w x : Vector J) :
    evaluate (v + w) x = evaluate v x + evaluate w x := by
  simp [evaluate, add_mul, Finset.sum_add_distrib]

lemma evaluate_add_right (v x y : Vector J) :
    evaluate v (x + y) = evaluate v x + evaluate v y := by
  simp [evaluate, mul_add, Finset.sum_add_distrib]

lemma evaluate_smul_left (a : ZMod 2) (v x : Vector J) :
    evaluate (a • v) x = a * evaluate v x := by
  simp [evaluate, mul_assoc, Finset.mul_sum]

lemma evaluate_smul_right (a : ZMod 2) (v x : Vector J) :
    evaluate v (a • x) = a * evaluate v x := by
  simp [evaluate, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- The row combinations as actual linear functionals on the sampled V. -/
noncomputable def rowFunctionals (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :
    Coeff c →ₗ[ZMod 2] Module.Dual (ZMod 2) (retained d) where
  toFun := fun u => {
    toFun := fun x => evaluate (R u) x
    map_add' := by intro x y; exact evaluate_add_right (R u) x y
    map_smul' := by intro a x; exact evaluate_smul_right a (R u) x }
  map_add' := by
    intro u v
    ext x
    change evaluate (R (u + v)) x = evaluate (R u) x + evaluate (R v) x
    rw [map_add, evaluate_add_left]
  map_smul' := by
    intro a u
    ext x
    change evaluate (R (a • u)) x = a * evaluate (R u) x
    rw [map_smul, evaluate_smul_left]

/-- Joint evaluation of the c row forms on U, with codomain the dual of
the coefficient space. Its kernel is exactly their common zero subspace W. -/
noncomputable def ambientEvaluation (R : Coeff c →ₗ[ZMod 2] Vector J) :
    Vector J →ₗ[ZMod 2] Module.Dual (ZMod 2) (Coeff c) where
  toFun := fun x => {
    toFun := fun u => evaluate (R u) x
    map_add' := by
      intro u v
      change evaluate (R (u + v)) x = evaluate (R u) x + evaluate (R v) x
      rw [map_add, evaluate_add_left]
    map_smul' := by
      intro a u
      change evaluate (R (a • u)) x = a * evaluate (R u) x
      rw [map_smul, evaluate_smul_left] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro u
    exact evaluate_add_right (R u) x y
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro u
    exact evaluate_smul_right a (R u) x

noncomputable def ambientKernel (R : Coeff c →ₗ[ZMod 2] Vector J) :
    Submodule (ZMod 2) (Vector J) := LinearMap.ker (ambientEvaluation R)

noncomputable def restrictedEvaluation (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :=
  (ambientEvaluation R).comp (retained d).subtype

/-- W intersect V, represented internally as a subspace of V. -/
noncomputable def intersectionInRetained (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :=
  (ambientKernel R).comap (retained d).subtype

lemma intersection_eq_kernel (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :
    intersectionInRetained R d = LinearMap.ker (restrictedEvaluation R d) := by
  ext x
  rfl

lemma rowFunctionals_injective (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J)
    (h : ¬ badRows R d) : Function.Injective (rowFunctionals R d) := by
  intro u v huv
  have hz : rowFunctionals R d (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hv : rowVanishes R (u - v) d := by
    apply (rowVanishes_on_retained R (u - v) d).mpr
    intro x hx
    exact congrArg (fun f : Module.Dual (ZMod 2) (retained d) => f ⟨x, hx⟩) hz
  have heq : u - v = 0 := by
    by_contra hn
    exact h ⟨u - v, hn, hv⟩
  exact sub_eq_zero.mp heq

/-- The sampled evaluation map is the transpose of the row-functional map
under the finite-dimensional double-dual equivalence. -/
lemma restrictedEvaluation_dual (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) :
    restrictedEvaluation R d = (rowFunctionals R d).dualMap.comp
      (Module.evalEquiv (ZMod 2) (retained d)).toLinearMap := by
  ext x u
  rfl

lemma goodRows_evaluation_surjective (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J)
    (h : ¬ badRows R d) : Function.Surjective (restrictedEvaluation R d) := by
  rw [restrictedEvaluation_dual]
  exact (LinearMap.dualMap_surjective_of_injective (rowFunctionals_injective R d h)).comp
    (Module.evalEquiv (ZMod 2) (retained d)).surjective

/-- Numeric codimension of W intersect V inside V, using the actual kernel. -/
noncomputable def intersectionCodim (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J) : ℕ :=
  Module.finrank (ZMod 2) (retained d) -
    Module.finrank (ZMod 2) (intersectionInRetained R d)

lemma goodRows_intersectionCodim (R : Coeff c →ₗ[ZMod 2] Vector J) (d : Draw J)
    (h : ¬ badRows R d) : intersectionCodim R d = c := by
  have hrange : LinearMap.range (restrictedEvaluation R d) = ⊤ :=
    LinearMap.range_eq_top.mpr (goodRows_evaluation_surjective R d h)
  have hdim := (restrictedEvaluation R d).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Subspace.dual_finrank_eq] at hdim
  have hc : Module.finrank (ZMod 2) (Coeff c) = c := by simp [Coeff, Module.finrank_pi]
  rw [hc] at hdim
  unfold intersectionCodim
  rw [intersection_eq_kernel]
  omega

/-- Manuscript transversality event, now stated as the numeric codimension of
the actual W intersect V. W is fixed for this unconditional probability. -/
theorem intersection_codim_failure_probability (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (R : Coeff c →ₗ[ZMod 2] Vector J) (hR : FullRowRank R) :
    probability β (fun d => intersectionCodim R d ≠ c) ≤ ((2 ^ c - 1 : ℕ) : ℚ) * β := by
  apply (probability_mono β hβ hβ1 _ _ (fun d hd => ?_)).trans
    (badRows_probability β hβ hβ1 R hR)
  by_contra hb
  exact hd (goodRows_intersectionCodim R d hb)

end PvNP.RealizableHardness.TripleRestrictionRank
