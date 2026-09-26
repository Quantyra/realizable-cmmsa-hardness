import PvNP.RealizableHardness.ActualPositiveFormulaMono

/-!
Checks call the shipped monotonicity lemmas.
-/
namespace PvNP.RealizableHardness.ActualPositiveFormulaMonoChecks

open PvNP.RealizableHardness
open ActualPositiveFormulaMono

example :
    Formula.eval (fun _ : Fin 2 => true)
      (Formula.and (Formula.var ⟨0, by decide⟩)
        (Formula.or (Formula.var ⟨1, by decide⟩) (Formula.var ⟨0, by decide⟩))) = true :=
  eval_all_true _

example {V : Type*} {x y : V → Bool}
    (h : ∀ v, x v = true → y v = true) (p : Formula V)
    (hx : Formula.eval x p = true) :
    Formula.eval y p = true :=
  eval_mono h p hx

example :
    Formula.eval (fun _ : Fin 2 => true)
      (Formula.or (Formula.var ⟨0, by decide⟩) (Formula.var ⟨1, by decide⟩)) = true := by
  have hx :
      Formula.eval (fun i : Fin 2 => decide (i.val = 0))
        (Formula.or (Formula.var ⟨0, by decide⟩) (Formula.var ⟨1, by decide⟩)) = true := by
    simp [Formula.eval]
  refine eval_mono ?_ _ hx
  intro v hv
  cases v using Fin.cases with
  | zero => simp
  | succ i => rfl

example {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    (w : V → ℚ) (F : I → Formula V) (s sig gam : ℚ)
    (x y : V → Bool)
    (hxy : ∀ v, x v = true → y v = true)
    (hall : ∀ i, Formula.eval x (F i) = true)
    (hcost : weight w y ≤ sig * s)
    (hγ : gam ≤ 1) :
    ¬ (∀ z, weight w z ≤ sig * s →
        average (fun i => Formula.eval z (F i)) < gam) :=
  not_sound_of_monotone_extension w F s sig gam x y hxy hall hcost hγ

end PvNP.RealizableHardness.ActualPositiveFormulaMonoChecks
