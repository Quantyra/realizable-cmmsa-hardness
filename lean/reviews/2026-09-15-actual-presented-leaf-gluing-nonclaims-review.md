# Actual presented-leaf gluing: non-claims-boundary review

Date: 2026-09-15  
Verdict: **GO-WITH-NOTES**  
Reviewed source commit: `e599567a629f6e4eb960b4b2543960095293d1d3`  
Reviewed certification commit: `6422609d04c6632035892431b7c77af0b6db7b08`

## Scope and bounded claim

This is a read-only top-level non-claims-boundary review of `ActualPresentedLeafGluing.lean`, its Checks module, and the canonical cloud certification under `research/evidence/2026-09-15-actual-presented-leaf-gluing-fresh-run`.

The accepted claim is limited to the following formal content over the actual occurrence-allocation source:

- `PresentedLeaf I J h` packages a good row question `U` of cardinality `J`, a submodule `L` of the question coordinate space with finrank `2 * h`, and the stated transverse intersection with the equation span.
- `RawLeafLabel`, `RespectsAt`, `LeafVertex`, and `LeafLabel` define a functional label over the presented domain and require an existential presentation whose equation vectors receive the actual row RHS values.
- `H_eq_of_domain_eq` proves that two presentations of the same domain have equal equation spans.
- `respectsAt_iff_of_domain_eq` proves that RHS-respect descends across two presentations of the same domain.
- `actual_existsUnique_gluedLeafRhsFunctional` proves existence and uniqueness of a linear functional on `P.domain ⊔ equationSpan I.support U'` that restricts to the supplied respecting raw label on `P.domain` and evaluates every equation vector indexed by the good question `U'` to `I.rowRhs`.

The increment is force-bearing for the next label-transport step: it constructs the actual leaf-domain label object, discharges presentation independence for the RHS condition, and supplies the unique enlarged-domain functional that a one-way transport map can consume.

## Exact boundary findings

No reviewed source, Checks fixture, or certification closeout claims or proves a leaf relation `Rel`, label transport, transport identity or inverse, transport coherence, an alphabet size of `2^(2h)`, center restriction, representative sampling, stationarity, actual-star acceptance, outer soundness, source hardness, a randomized reduction, runtime or asymptotic bounds, novelty, publication readiness, `P = NP`, or `P ≠ NP`. Those remain outside this increment.

In particular:

- `LeafLabel` is a subtype of linear functionals with an existential respecting presentation. It is not yet a finite encoded alphabet and has no cardinality theorem.
- The glued functional is a mathematical existence-and-uniqueness theorem. Its use of classical extension machinery does not establish a computable or polynomial-time label transformer.
- Same-domain RHS descent is presentation independence for `RespectsAt`; it is not a transport theorem between different leaf domains.
- The theorem assumes an already supplied `PresentedLeaf`, good target question, raw label, and proof that the label respects the source presentation. It does not construct leaves, samples, centers, or accepted stars.

The certification `README.md` and `closeout.md` correctly call the receipt a target-fresh certification and explicitly deny that it is a three-lens review or completion of the manuscript theorem. Their object-hash explanation is appropriately bounded: cloud objects differ from the local cached objects because all project objects were rebuilt in a fresh Linux target while the local cache came from a different target and operating-system context. The receipt relies on exact frozen source identity, locked revisions, target freshness, successful kernel elaboration, stable evidence, and axiom reporting rather than cross-platform byte equality.

## Fixtures

The Checks module contains both required branches.

- The nonempty fixture uses an actual `Instance 1 1`, a singleton good row question, actual RHS `1`, and an explicitly constructed respecting raw label. It constructs a `LeafLabel` and invokes `actual_existsUnique_gluedLeafRhsFunctional` at its exact exported signature. The RHS condition is nonvacuous and nonzero.
- The empty fixture uses the empty question, bottom presentation, and zero raw label and invokes the same exported theorem at its exact signature. Its universal row condition is intentionally vacuous and checks the empty boundary case.

The nonempty fixture has `h = 0`, `L = ⊥`, and `U' = P.U`; therefore it does not exercise a positive-rank leaf subspace or a genuinely larger target equation span. This limits fixture coverage, but does not weaken the general theorem or make its nonempty RHS check vacuous. A later transport increment should include a fixture with distinct source and target presentations or questions so that the new transport branch itself is exercised.

## Certification and integrity

The provenance gate passed before compilation. The transferred complete-history bundle had SHA-256 `FD98C5DB3B89F6C04552916E9E6315D806F26B8A596694278DA2E9EBBFC27A21` locally and remotely; remote bundle verification passed; the checkout was clean and detached at the exact source commit.

The frozen source hashes independently match the current committed files:

| Artifact | SHA-256 |
|---|---|
| `ActualPresentedLeafGluing.lean` | `D19126D4962A13AF182462F56548FE74252100108D5BC1C9EF1C51EAEEBD1452` |
| `ActualPresentedLeafGluingChecks.lean` | `E76DB5B1AF64E31131E785CAB057F194DF3428CE67E159693C61EE3B4AB0564E` |
| cloud main object | `3AE5AB5229E44A73D0AB545987E93E028E5F0C522DF88149ED10983F51E82C4B` |
| cloud Checks object | `A6F2D6F0D0B023265916D4BD7F58DDE23D9A35F1A1A34208D65BE96538D31165` |

The source commit and both source hashes were asserted initially, before and after every one of the 17 compile stages, and finally: 36 stable assertions. The complete 15-module reachable project-source closure, main, and Checks all exited `0` in a new target under Lean `4.34.0-rc2`. The first cache-preparation failure occurred before main compilation, changed the build route, and is bounded separately in the receipt.

The source scan of the frozen main and Checks files found no `sorry`, `admit`, `native_decide`, or explicit source-level `axiom`. Checks reports only `propext`, `Classical.choice`, and `Quot.sound` for `H_eq_of_domain_eq`, `respectsAt_iff_of_domain_eq`, and `actual_existsUnique_gluedLeafRhsFunctional`; no project-specific axiom is reported. The canonical local evidence manifest contains 139 rows, independently rehashes with zero mismatches, and has SHA-256 `3EADD48379297AAD61EF5ADF24D73498770D1529A32969D008FE6D742E502BED`.

The builder snapshot records `quantyra-lean-builder-01` as `TERMINATED`, with only private address `10.128.0.2` and no external access configuration. Estimated cumulative GCP spend is `$0.340771`, leaving `$249.659229` below the `$250` operational ceiling. The stopped 200 GiB disk continues to accrue an estimated `$0.657533/day`; the estimate is not an invoice.

## Consumer and remaining path

The immediate manuscript consumer is leaf equivalence and one-way transport, using the unique glued functional to move a label to the next actual leaf domain while retaining the actual RHS constraints. The remaining headline path is:

`leaf equivalence and one-way transport → identity, inverse, and coherence → presentation descent and repeated-address semantics → center restriction → representative sampler and stationarity → actual-star acceptance → outer soundness and source hardness → reduction/runtime/asymptotics → manuscript reconciliation, publication-readiness review, generated PDF, metadata, and final release evidence`.

The GO-WITH-NOTES verdict accepts this increment at its exact bounded scope. It does not authorize broader manuscript claims, DOI metadata changes, release, or public announcement.
