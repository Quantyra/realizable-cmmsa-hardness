# Non-claims boundary review: frozen A9 ambient reindex increment

Verdict: **GO-WITH-NOTES**

Reviewed 2026-10-04 as the top-level non-claims-boundary reviewer. No finding blocks bounded acceptance of the stated partition and charge theorems. This report completes only the non-claims lens; it neither supplies the other mandatory lenses nor closes S3132 or certifies the full manuscript.

## Scope and evidence identity

Read the two requested Lean modules, the session reports, statement-fidelity and README wording, all three captured author reports, the accepted-run claim boundary and warning-policy records, manuscript A8/A9/A10 and surrounding status/aggregation text, and the relevant S3132 master-plan entries. Applied the planning repository's `docs/formal-three-lens-closeout-protocol.md` and `docs/protocol.md`, particularly “Formal research closeout”, claim-boundary expansion, and warning-baseline requirements. The destination repository has no `docs/protocol.md`; the planning repository's file supplies that protocol.

The current source and Checks SHA-256 hashes independently match `session-20261004-reindex/report.json`:

- Source: `5B4958CE0B86D02F578457715F05382EF6037535C5CDB7177F48945FF1E8A2BE`.
- Checks: `82785615ADB3E40F10A47F78293090B3572C208764151D07E7E5C0F6C57A4F5C`.
- Accepted compiler run: `cmmsa_a9_ambient_20261004T192626Z_83a1ebb0`.

No Lean, Lake, or elan was run locally; no nested reviewers were dispatched. Compiler and axiom conclusions below rely on retained evidence, not an independent compiler replay. Only this report was created.

For references below, **source** means `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean`; **session** means `docs/a7-certification-20261003/a9-ambient-reindex-gcp/session-20261004-reindex`; **master plan** means `C:/Users/Dan/Desktop/Projects/IGH/Quantyra-Planning/stories/S3126-realizable-hardness-formal-proof-and-paper.md`. JSON references identify exact keys rather than unstable formatting-dependent line numbers.

## Findings by severity

### Critical / high

None found in the reviewed frozen increment. No reviewed module or closeout wording asserts GA-4, a switching lemma, Frege/PHP lower bounds, circuit lower bounds, or a P-versus-NP resolution. The manuscript's wider mathematical argument is explicitly a submission draft with incomplete Lean formalization and no formal certification (`paper/body.tex:6`); its later proof prose must be read under that status.

### Medium — bounded acceptance terminology requires its recorded qualification

`session/report.txt:3` says “Acceptance: GREEN”; `session/report.json` sets `bounded_acceptance_green: true`. These labels are broader in isolation than a completed material-milestone acceptance. They are adequately bounded by the report's compiler-closeout title (`report.txt:1`), explicit absence of three-lens reviews and open route-final/full-certification status (`report.txt:25`), and JSON keys `three_lens_reviews`, `full_manuscript_or_story_closeout_claim`, and `S3137`. The accepted-run `manifest.json.snapshot`, key `claims_boundary`, also says S3132 remains open and there is no route-final certification.

When reused in a later closeout, describe this as **compiler/no-regression acceptance**, then report bounded milestone acceptance separately with the actual three-lens table. Frozen “NOT RUN” statements describe the compiler-session state; this new report does not retroactively make all three lenses complete. **Nonblocking for the bounded result; blocks any inference of route-final or story completion from GREEN alone.**

### Medium — “analytic A9” denotes partition and multiplicity charge only

The module header (`source:5`) and `session/statement-fidelity.md:1` are defensible shorthand for the exact reindexing of the A8 right-side summand. The actual declarations expose the narrower result: the predecessor source has rank and both incidence conditions (`source:28–35`); the target retains rank-k final maps and their actual fibers (`source:37–41`); the sum partition is for fixed A, B, i, j, k (`source:100–112`). Its summand is the uniform mean of squared typed output energies (`source:74–80`).

The exact charge retains `2^(6*D*k)` on both sides, and the coarse charge retains exponent `3*D*(i+j+k)+6*D*k` (`source`, theorems `a9Ambient_fixed_fiber_exact_charge` and `a9Ambient_fixed_fiber_coarse_charge`; `session/report.txt:23`; `statement-fidelity.md:3–8`). This is cardinality charging of a fiber-constant energy, not a new estimate deriving the graph factor or the A8 fourth-moment inequality. Exact charge requires hA/hB/hY/hi/hj; coarse charge additionally requires `a+b+k ≤ D`. The parameter D is not, in these declarations, a discharged degree bound for f.

The manuscript still needs the analytic A8 inequality and subsequent exponent/aggregation steps (`paper/body.tex:1269–1294`, `1311–1337`). In particular the sharper manuscript count `2^(d(i+j+k))` (`paper/body.tex:1310`) is not this increment's exported coarse bound. **Nonblocking; do not summarize this milestone as full analytic A8–A11 or HC46 certification.**

### Low — README warning shorthand is incomplete and uses the wrong count terminology

`session/README.md:8` calls 748 dependency plus 13 prior owned warnings “warning headers” and omits the expanded dependency baseline. The more precise `session/report.txt:19–21` and `report.json.warning_policy` disclose 37 additional unchanged dependencies, 343 additional diagnostic occurrences per build stage, and 329 additional actual warning headers. They also distinguish diagnostic occurrences from header counts. The accepted stage header counts are 652, 981, 981, and 1 (`warning_policy.warning_stage_results`), while legacy diagnostic counts are 761, 1104, 1104, and 1.

The primary closeout is honest: legacy zero-total-warning remains red; candidate-owned headers and inherited regressions are zero; warning debt remains S3137 debt. The retained accepted-run `audit.json` still has `green: false` and `certified: false`, with warnings as its failure reason. No zero-warning claim is justified. **Nonblocking under the recorded no-regression policy.** Future summaries should use the full expanded baseline and distinguish headers from diagnostic occurrences; preserve the frozen evidence unchanged.

### Informational — planning status is conservative, not falsely complete

The master plan's earlier ambient milestone remains a separate equivalence/count acceptance (`master plan:3276–3294`); the reconciliation lists S3132 as partial and identifies analytic A9/A8/A11/W6/positive-degree A7 and actual outer/star construction as remaining work (`master plan:3305`, `3312`). This frozen reindex increment advances that next obligation only within its exported partition/charge scope. The planning text does not claim it has closed S3132. S3137 assembly, source/runtime integration, warning-policy decision and final reviews remain outstanding (`master plan:3310`; `session/report.txt:25`; `report.json.S3137`).

## Allowed claims

- The retained GCP evidence reports all four accepted compiler stages exiting zero, zero errors/unsolved goals, and the five Checks declarations using only `Classical.choice`, `Quot.sound`, and `propext` (`report.txt:11–17`; Checks file). This is exact-module compiler/axiom evidence, not full-manuscript evidence.
- For arbitrary complex f in the stated finite binary-matrix setting, the actual predecessor index is equivalent to the dependent rank-k final-map/fiber index, and the specified energy sum is exactly preserved under that partition. Nonnegativity is proved for the defined averaged squared energy.
- Under the explicit dimension, rank and index hypotheses, one fixed-final fiber contributes exactly its Gaussian/graph cardinality times the same energy and the same graph factor. With hfin it is bounded by `2^(3*D*(i+j+k)+6*D*k)` times that energy.
- The accepted compiler evidence satisfies the recorded warning no-regression policy with retained warning debt. Bounded milestone acceptance still requires the orchestrator's complete mandatory review record. S3132 remains partial and S3137/full manuscript certification remains incomplete.

## Forbidden claims

- Zero total warnings, a clean legacy audit, or a complete three-lens/final certification inferred from compilation, push receipts, or this single review.
- A8's fourth-moment estimate, the derivation of its graph factor, A10/A11 aggregation, W6 application, positive-degree A7, full HC46, or completed outer-game/star soundness-completeness proved by this increment.
- The stronger manuscript multiplicity exponent, omitted graph factors, omitted hfin or other hypotheses, a globally composed reduction, polynomial encoded runtime, or Theorem 1/Corollary 2 assembly inferred from these declarations.
- GA-4 discharge, a switching lemma, arbitrary AC0/bounded-depth collapse, Frege/PHP or circuit lower bounds, P=NP/P≠NP, or unconditional full realizable-hardness certification. No claim-boundary expansion is authorized by this report.

## Bounded acceptance disposition

No non-claims finding requires withdrawal or blocks acceptance of the exact partition/nonnegativity/exact-charge/coarse-charge increment. Carry the notes into the orchestrator's milestone closeout, retaining the distinction between compiler success, bounded theorem acceptance, partial S3132, and incomplete full manuscript certification. The other required lenses and final certification obligations are outside this report's authority.
