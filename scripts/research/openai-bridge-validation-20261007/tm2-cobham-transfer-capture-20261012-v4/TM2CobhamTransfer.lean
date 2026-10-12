import OAI.Computability.UniqueGames.Machines.Runtime

/-!
# Whole-configuration resource invariant for the finite TM2 to Cobham transfer

This file records the first source theorem in the TM2-to-local-Cobham route.
It reasons about the actual pinned upstream `Turing.FinTM2` transition system;
it does not clone that parser or assume a local `FP` witness.

The complete transfer still requires a finite-alphabet block encoding, a local
`Complexity.TM` implementation of each encoded transition, exact initialization
and output decoding, an absorbing halt state, a concrete all-clock polynomial
bound, and the resulting actual `Complexity.CobhamFP` membership. Those are not
asserted here.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

/-- Total stack payload is the sum of the lengths of every stack in an actual
TM2 configuration. It deliberately includes all stacks, not just the input
and output stacks. -/
def totalStackLength (tm : Turing.FinTM2) (cfg : tm.Cfg) : Nat :=
  ∑ k : tm.K, (cfg.stk k).length

/-- One actual TM2 clock step grows the whole stack payload by at most the
finite program's maximum pushes, once per stack. Pop operations and all
state-only operations are covered by the pinned `stepStackLength` lemma. -/
theorem step_totalStackLength_le (tm : Turing.FinTM2) (a b : tm.Cfg)
    (hstep : tm.step a = some b) :
    totalStackLength tm b ≤ totalStackLength tm a +
      ∑ _k : tm.K, Runtime.programPushBound tm := by
  unfold totalStackLength
  calc
    (∑ k : tm.K, (b.stk k).length) ≤
        ∑ k : tm.K, ((a.stk k).length + Runtime.programPushBound tm) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Runtime.stepStackLength tm k a b hstep
    _ = (∑ k : tm.K, (a.stk k).length) +
        ∑ _k : tm.K, Runtime.programPushBound tm := Finset.sum_add_distrib

/-- The same bound holds at every clock, including clocks after the TM2 run
has halted, because the actual option-valued transition is absorbing at `none`.
The budget is the caller's clock index; no caller-supplied runtime/FP premise
is introduced. -/
theorem execution_totalStackLength_le (tm : Turing.FinTM2)
    {start finish : tm.Cfg} {budget : Nat}
    (execution : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    totalStackLength tm finish ≤ totalStackLength tm start +
      budget * (∑ _k : tm.K, Runtime.programPushBound tm) := by
  exact Runtime.executionSizeBound tm.step (totalStackLength tm)
    (∑ _k : tm.K, Runtime.programPushBound tm)
    (by
      intro a b hstep
      exact step_totalStackLength_le tm a b hstep)
    execution

/-- A successful option-valued execution is the same final configuration as
the total transition which holds a halted configuration fixed. The option
iterator is used only through its successful exact-step equation; extending
past the halt is handled separately by the absorbing total transition. -/
theorem absorbingIter_eq_of_bindIter_eq {sigma : Type}
    (step : sigma -> Option sigma) (clock : Nat) {start finish : sigma}
    (hexec : (fun state : Option sigma => state.bind step)^[clock] (some start) =
      some finish) :
    (fun state : sigma => (step state).getD state)^[clock] start = finish := by
  induction clock generalizing start finish with
  | zero => simpa using hexec
  | succ clock ih =>
      rw [Function.iterate_succ_apply'] at hexec <;>
        rw [Function.iterate_succ_apply']
      cases hprefix : (fun state : Option sigma => state.bind step)^[clock]
          (some start) with
      | none => simp [hprefix] at hexec
      | some mid =>
          have hstep : step mid = some finish := by
            simpa [hprefix] using hexec
          rw [ih hprefix]
          simp [hstep]

/-- Once the option transition reports `none` at a configuration, its total
`getD` extension holds that configuration fixed at every later clock. -/
theorem absorbingIter_eq_at_later_clock {sigma : Type}
    (step : sigma -> Option sigma) {start finish : sigma}
    (clock : Nat) (halted : step finish = none)
    (hexact : (fun state : sigma => (step state).getD state)^[clock] start = finish)
    {later : Nat} (hle : clock <= later) :
    (fun state : sigma => (step state).getD state)^[later] start = finish := by
  induction later with
  | zero =>
      have : clock = 0 := by omega
      subst clock
      simpa using hexact
  | succ later ih =>
      by_cases hle' : clock <= later
      · rw [Function.iterate_succ_apply']
        simp [ih hle', halted]
      · have heq : later + 1 = clock := by omega
        simpa [heq] using hexact

/-- Combine the exact successful-step equation with halt absorption. This is
the machine-runtime bridge used to identify the Cobham iterator at every
clock at least the certified execution budget. -/
theorem absorbingIter_eq_of_EvalsToInTime {sigma : Type}
    (step : sigma -> Option sigma) {start finish : sigma} {budget later : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget)
    (halted : step finish = none) (hbudget : budget <= later) :
    (fun state : sigma => (step state).getD state)^[later] start = finish := by
  exact absorbingIter_eq_at_later_clock step execution.steps halted
    (absorbingIter_eq_of_bindIter_eq step execution.steps execution.evals_in_steps)
    (Nat.le_trans execution.steps_le_m hbudget)

/-- The pinned TM2 halt configuration has no outgoing option transition, so
every absorbing iteration after a certified run is exactly its `haltList`. -/
theorem absorbingTM2Run_eq_haltList_after (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    {budget later : Nat}
    (execution : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some (Turing.haltList tm output)) budget) (hbudget : budget <= later) :
    (absorbingStep tm)^[later] (Turing.initList tm input) = Turing.haltList tm output := by
  exact absorbingIter_eq_of_EvalsToInTime tm.step execution
    (by simp [Turing.haltList, Turing.FinTM2.step, Turing.TM2.step]) hbudget

end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer
