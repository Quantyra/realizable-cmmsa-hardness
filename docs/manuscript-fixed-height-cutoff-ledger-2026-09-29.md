# Fixed-height cutoff ledger for the conditional Theorem 1 certificate

The manuscript does not specify one closed-form `h_min(m)`. Section 10 of
`paper/body.tex` (lines 860–866) requires the selected height to exceed every
fixed lower bound established earlier for that `m`, with `ξ=1/m²` and
`ρ=1/(4000m²)`. The selected `m`, `ρ`, outer NO constant `κ`, integer `A`,
height `h`, `J`, and alphabet `R` are fixed before an arbitrary later PCP YES
error `τ` (lines 783–801). Therefore the cutoff must be independent of `τ`.

`ActualManuscriptCutoffLedger.lean` separates two kinds of entries:

| Entry | Source condition | Lean status |
| --- | --- | --- |
| `Rof m + 4`, `16` | Robust-local proof, `h≥r+4` and `h≥16`, lines 580–583; `Rof m = 10m/ρ` for fixed `ρ`. | Explicit in the finite floor. |
| `4m` | Sufficient for `2hm(ξ−1000ρ)≥5`, good-question amplification, line 702. | Explicit guard; arithmetic lemma in the new module. |
| Inverse and robust history | Inverse spectral/moment/selection cutoffs, lines 401–515; refresh history `B_nF_n<1/2`, lines 552–583. | Named cutoff witnesses; their sufficiency has **not** been proved. |
| Covering and posterior | Exceptional advice, joint-law, rank, and conditional agreement estimates, lines 590–729. | Named cutoff witnesses; their sufficiency has **not** been proved. |
| Maximal count and outer decoder | Threshold ladder `B_r` cutoff, lines 731–740; `K_U,K_M,B_U,B_M`, fixed `κ,A`, and decoded-success comparison, lines 755–783. | Named cutoff witnesses; their sufficiency has **not** been proved. |
| Compilation | `σ≥8`, sampling/list error, strict NO threshold, encoded weighting, lines 809–857. | Selector already requires `σ_base≥8`; other numerical cutoffs are named but unproved. |

The selector theorem is pointwise in an **arbitrary fixed ledger** and proves
that all of its finitely many entries are eventually met. It does not prove
that the listed entries exhaust the manuscript, nor that the currently
uninstantiated witnesses satisfy their source inequalities. In particular,
`ActualCertifiedManuscriptParameters.manuscriptSourceFloor m = m+2` remains a
placeholder and its exported `certifiedM` is not yet the manuscript-selected
parameter. The first remaining numeric theorem must have the following order:
for every fixed `m≥256`, fix `ξ=1/m²`, `ρ=1/(4000m²)` and the source constants;
take the **fixed** outer NO constant `κ>0`; choose integer `A` with `20<κA`;
then exhibit a finite `h_min(m,κ,A,source constants)` such that **every**
`b_m`-divisible `h≥h_min` satisfies **each** inverse, robust-history,
covering/posterior, ladder, decoder, and compilation inequality used in
`paper/body.tex` at `n=2J`, `J=2^(2^(Ah²))`. Only after these choices may an
arbitrary fixed `τ>0` be chosen, without changing `h`, `J`, or `R`. Neither a
cutoff selected before `κ,A` nor an unnamed assertion that `h` is large
establishes this theorem.

This ledger does not reduce the missing NO-soundness decoder gap.

## Lean check and bounded review

`lake build PvNP.RealizableHardness.ActualManuscriptCutoffLedgerChecks`
completed successfully (3264 jobs). The checks display the exact types of
`amplification_margin_of_four_mul_m`, `ready_of_floor`, and
`selected_ledger_eventually`. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for the first and third theorems, and
only `propext` for `ready_of_floor`. There is no `sorry` or manuscript
external axiom in these theorems.

| Lens | Bounded ledger verdict | Core cutoff verdict |
| --- | --- | --- |
| Proof adversarial | GO-WITH-NOTES for finite-max selector and amplification arithmetic | NO-GO until every named source witness is instantiated and proved sufficient. |
| Complexity theory | GO-WITH-NOTES for fixed-before-`τ` quantifier order | NO-GO for a source-to-CMMSA runtime or reduction claim. |
| Non-claims boundary | GO-WITH-NOTES for explicit conditional fields | NO-GO for calling `certifiedM` the manuscript selector. |

This is bounded evidence only. Planning review-debt story S3126 remains open;
the ledger is not a route-final three-lens closeout and does not reduce the
remaining numeric NO-soundness gap.
