import PvNP.RealizableHardness.Formula

/-!
Positive formulas are monotone, and the all-true assignment satisfies
every one of them. Turning additional variables on cannot make a satisfied
formula false, and it cannot lower an all-true average.

If a witness `x` satisfies every formula and a pointwise extension `y`
still has weight at most `σ * s`, then `y` is a counterexample to the
no-promise `satisfaction < γ` whenever `γ ≤ 1`. This does not show that
every function fails `MapReducesVia`, and it does not prove Theorem 1
or Corollary 2.
-/
namespace PvNP.RealizableHardness.ActualPositiveFormulaMono

open PvNP.RealizableHardness

/-- Every positive formula is true when every variable is true. -/
theorem eval_all_true {V : Type*} (p : Formula V) :
    Formula.eval (fun _ => true) p = true := by
  induction p with
  | var v => simp [Formula.eval]
  | and p q ihp ihq => simp [Formula.eval, ihp, ihq]
  | or p q ihp ihq => simp [Formula.eval, ihp, ihq]

theorem eval_mono {V : Type*} {x y : V → Bool}
    (h : ∀ v, x v = true → y v = true) (p : Formula V) :
    Formula.eval x p = true → Formula.eval y p = true := by
  induction p with
  | var v =>
      intro hx
      simp only [Formula.eval] at hx ⊢
      exact h v hx
  | and p q ihp ihq =>
      intro hx
      simp only [Formula.eval, Bool.and_eq_true] at hx ⊢
      exact ⟨ihp hx.1, ihq hx.2⟩
  | or p q ihp ihq =>
      intro hx
      simp only [Formula.eval, Bool.or_eq_true] at hx ⊢
      rcases hx with hp | hq
      · exact Or.inl (ihp hp)
      · exact Or.inr (ihq hq)

theorem weight_le_of_extension {V : Type*} [Fintype V] {w : V → ℚ}
    {x y : V → Bool} (hw : ∀ v, 0 ≤ w v)
    (h : ∀ v, x v = true → y v = true) :
    weight w x ≤ weight w y := by
  unfold weight
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases hx : x v
  · have hy : y v = true := h v hx
    simp [hx, hy]
  · have hxfalse : x v = false := by simpa using hx
    simp [hxfalse]
    split
    · exact hw v
    · exact le_rfl

theorem not_sound_of_monotone_extension
    {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    (w : V → ℚ) (F : I → Formula V) (s sig gam : ℚ)
    (x y : V → Bool)
    (hxy : ∀ v, x v = true → y v = true)
    (hall : ∀ i, Formula.eval x (F i) = true)
    (hcost : weight w y ≤ sig * s)
    (hγ : gam ≤ 1) :
    ¬ (∀ z, weight w z ≤ sig * s →
        average (fun i => Formula.eval z (F i)) < gam) := by
  intro hno
  have hallY : ∀ i, Formula.eval y (F i) = true :=
    fun i => eval_mono hxy (F i) (hall i)
  have havg : average (fun i => Formula.eval y (F i)) = 1 := by
    have hfun : (fun i => Formula.eval y (F i)) = fun _ => true :=
      funext hallY
    rw [hfun]
    exact average_true
  have hlt := hno y hcost
  rw [havg] at hlt
  exact not_lt_of_ge hγ hlt

end PvNP.RealizableHardness.ActualPositiveFormulaMono
