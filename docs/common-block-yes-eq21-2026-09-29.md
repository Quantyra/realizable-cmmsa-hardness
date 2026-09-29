# Common-draw YES composition for Equation (21)

`ActualCommonBlockYesComposition.lean` uses one actual declared
`OriginalDraw` to carry all `m+1` equation blocks. Coordinate zero is its
original copied-row question `U`; coordinate `i+1` is the eligible question
`U'_i` projected from its independently sampled i-th class representative.
`anyBadBlock` is the union of these bad-equation events on **that same draw**.
No independence among block events is used.

For one ambient linear assignment `f` fixed before the draw,
`honest_accepts_of_all_good` proves that good equations in all blocks imply
`originalAccepts` for the single globally legal
`honestOriginalAssignment I copies f`. Its proof uses the already established
original-block honest transport; the original good block alone suffices for
that implication under this table construction.

`all_bad_blocks_scaled_le` combines the previously proved original and
per-coordinate resampled marginals. Assuming the exact copied-row
`PositiveErrorAssignment I copies f ε₁`, `ε₁≥0`, positive copied-row count,
nonempty raw ordered and eligible question types, nonempty presented leaves,
nonempty center and leaf fibres, `t≤2h`, and `h≤J`, it proves

\[
  \Pr_{\mathrm{OriginalDraw}}[\text{any of the }m+1\text{ blocks is bad}]
  \Pr_{\mathrm{raw}}[\mathrm{legitimate}]
  \le (m+1)J\epsilon_1.
\]

This is a scalar product of the **conditioned declared draw** bad-event
probability and the raw legitimacy mass. The theorem does **not** identify
that product with the probability of a common raw joint event.

`common_draw_yes_failure_le` additionally assumes positive copies and source
degree, `J>0`, a later arbitrary `τ>0`,
`ε₁≤τ/[100(m+1)J]`, and the actual raw bad mass `a≤1/4`. Using the exact
identity `Pr_raw[legitimate]=1-a`, it proves the fixed honest table's actual
declared-draw rejection probability is at most `τ/75`, as in manuscript
Equation (21). The module target build passed (3446 jobs), and
`ActualCommonBlockYesCompositionChecks` passed (3447 jobs). The Checks file
prints only `propext`, `Classical.choice`, and `Quot.sound` as axioms for the
three named theorems.

The existence of an encoded outer YES assignment in this exact ambient
linear-map representation remains conditional. This result does not prove the
full encoded SAT-to-CMMSA reduction, core Theorem 1, or any NO-soundness
bound. It reduces the remaining **YES composition** gap; the NO gap is
unchanged.

## Three-lens bounded review

| Lens | Verdict | Boundary |
| --- | --- | --- |
| Proof adversarial | **GO-WITH-NOTES** | The common `OriginalDraw` carries `U` and every actual `U'_i`. All-good acceptance for the fixed legal table invokes the original `U` implication; the `m+1`-block union is conservative. The copied-row error assignment and all listed nonempty fibres remain premises. |
| Complexity theory | **GO-WITH-NOTES** | The later `ε₁≤τ/[100(m+1)J]` and raw bad mass `a≤1/4` yield the declared-draw Eq21 rejection bound. Existence of the ambient outer assignment `f`, encoded padding, and the full SAT-to-CMMSA reduction remain external or unproved. |
| Non-claims boundary | **GO-WITH-NOTES** | Multiplying the declared conditioned-draw event probability by raw legitimacy mass is not identified with a common raw joint event. The core certificate is **INCOMPLETE**, and the NO-soundness gap is unchanged. |

This three-lens outcome closes only the bounded declared-draw YES comparison.
