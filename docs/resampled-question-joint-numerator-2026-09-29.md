# Actual clique-resampled YES numerator

`ActualResampledQuestionMarginal.lean` proves the manuscript's source-specific
one-coordinate law. For every fixed copied occurrence instance `I`, copy count,
`J,t,h,k`, every `i : Fin k`, and nonempty eligible-question, center, leaf, and
presented-leaf fibres, with `t ≤ 2h` and `h ≤ J`, the actual
`originalLawFromTagged` draw has a uniform i-th initial full presented leaf.
The actual uniform independent class-representative choice then has a uniform
i-th full presented leaf, and its projected (U'_i) is uniform over eligible
copied row questions. The proof consumes the exact transverse-center count,
the fixed-center leaf count, and the reverse incidence count in
`ActualTaggedYesReverseIncidence.lean`; it uses the actual tagged joint law and
the proved equivalence to `OriginalDraw`.

`resampledU_badRow_joint_le` further assumes a linear assignment `f` satisfying
`PositiveErrorAssignment I copies f ε₁`, `0 ≤ ε₁`, and a nonempty copied row
type. For every `i`, it proves

\[
  \Pr_{\mathrm{original}}[U'_i\text{ has a bad copied row}]
  \Pr_{\mathrm{raw}}[\mathrm{legitimate}] \le J\epsilon_1.
\]

The legitimacy factor is retained: the bound is the raw joint numerator used
by Equation (21), not a claim that the eligible conditional probability alone
is at most (J\epsilon_1). No independence among coordinates is assumed.

The missing YES bridge is a **single common (m+1)-block raw/conditioned
experiment** whose original and clique-resampled bad-block events project to
these proved marginals, together with the pointwise theorem that all (m+1)
blocks having good equations makes the *composed* verifier accept under one
honest legal table. `ActualHonestTaggedTransport.honestOriginalAccepts_of_goodU`
proves the single original-block implication; it does not by itself identify
the composed verifier event. The positive-error assignment's existence from
the outer YES contract is also conditional. Thus Equation (21) and core
Theorem 1 are not closed by this increment. It changes no NO-soundness bound.

Verification: `lake --old build
PvNP.RealizableHardness.ActualResampledQuestionMarginalChecks` passed (3446
jobs). The Checks file imports the reverse-incidence dependency, checks the
named theorems, and prints only `propext`, `Classical.choice`, and `Quot.sound`
as axioms. The requested three-lens review remains to be recorded before any
route-final status.
