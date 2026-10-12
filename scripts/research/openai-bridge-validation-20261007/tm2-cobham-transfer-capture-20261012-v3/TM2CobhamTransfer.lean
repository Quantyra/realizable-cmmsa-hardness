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

end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer