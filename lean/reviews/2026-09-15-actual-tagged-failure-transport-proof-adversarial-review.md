# Proof-adversarial review: actual tagged failure transport

Date: 2026-09-15  
Verdict: **GO-WITH-NOTES**

## Frozen review target

- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedFailureTransport.lean`
  - expected SHA-256: `F3455245210FF8FA22421FD2EE886FB730B3854284F253F4C1082DF0AFFDAC16`
  - independently observed SHA-256: `F3455245210FF8FA22421FD2EE886FB730B3854284F253F4C1082DF0AFFDAC16`
- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedFailureTransportChecks.lean`
  - expected SHA-256: `E712882B84A5DF306EC95CD7212507F9D3B020609679F394AB417997FB448B69`
  - independently observed SHA-256: `E712882B84A5DF306EC95CD7212507F9D3B020609679F394AB417997FB448B69`
- Certification directory: `research/evidence/2026-09-15-actual-tagged-failure-transport-fresh-run/`
  - canonical `artifact-hashes.txt` SHA-256 and pointer value: `4AEDC064895353B3ADF044A15F62F00F91346BBAF752774E9EC167FDCAB3F398`
  - pointer-file SHA-256: `FDCEB5DC572695991954829BB0D3B4397E17F3BF80B39066908B063433C38C65`
  - all 25 manifest rows were independently rehashed and matched their recorded byte sizes and SHA-256 values.

## Findings

1. **The tagged and base failure events are pointwise equivalent.** `actualTaggedFailureIndicator_eq_baseProjection` rewrites `taggedCopy.badRow` under `repeatAssignment` using `taggedCopy_badRow` and `restrictAssignment_repeatAssignment`. Both directions preserve the same witness `j : Fin J`; no probability, independence, or distributional assumption enters this step. The resulting base tuple is exactly `baseProjection u`, so the theorem proves equality of the two `0/1` indicators rather than merely an inequality.

2. **The tuple failure bound is a valid union bound.** `actualBaseFailureIndicator_le_sum` isolates a witnessing failed coordinate when the existential event holds and bounds its indicator by the nonnegative sum of coordinate indicators. When the event is false, the left side is zero and the coordinate sum is nonnegative. Repeated coordinates cause no problem: the proof is a union bound and may overcount them, as the manuscript estimate permits.

3. **The coordinate-fibre sum has the correct exponent.** For `j : Fin J`, `sum_eval_eq_card_pow_mul_sum` gives a bijection

   `(Fin J -> E) ~= E x ({i : Fin J // i != j} -> E)`.

   The complementary coordinate type has cardinality `J - 1`, so every fixed value at `j` has exactly `card(E)^(J-1)` extensions. At `J = 1` this is `card(E)^0 = 1`. At `J = 0` the theorem cannot be instantiated because there is no `j : Fin 0`; the consuming uniform-mean theorem handles `J = 0` separately and proves both sides zero. Thus truncated subtraction is never used illegitimately.

4. **The denominator algebra is sound.** For `J > 0`, positivity of `m` implies a nonempty actual row type. The proof rewrites

   `card(Fin J -> RowId) = card(RowId)^J`

   and uses `card(RowId)^J = card(RowId)^(J-1) * card(RowId)` before cross-multiplying only by positive denominators. Combining the coordinate-fibre identity with the indicator union bound yields exactly

   `E_q[failure(q)] <= J * violations(x) / card(RowId)`.

   The separate `J = 0` branch correctly gives zero failure probability over the singleton empty tuple.

5. **The actual-source extension rate uses the required source assumption without strengthening it.** `actualSourceExtension_failureRate_le` assumes `0 < m`, `0 <= eta`, and

   `sourceViolations(y) <= eta * m`.

   It uses the compiled equality `sourceExtension_violations` and the actual construction's `m <= rows.length`. Because `eta` is nonnegative, enlarging the denominator from the original `m` source rows to all actual rows can only reduce the failure rate. It introduces no satisfiability, independence, regularity, or exact-row-count premise beyond the compiled construction facts.

6. **The final composition has exactly the advertised `4/3 * J * eta` form.** `actualTaggedGoodFailureMean_sourceExtension_le` first replaces tagged failure by its base projection, invokes the certified good-question/base-projection transport bound, applies the ordered-tuple union bound, and finally applies the source-extension failure-rate theorem. All multiplications preserve inequalities using explicit nonnegativity of `J`, `eta`, and `4/3`. The public assumptions are exactly `4 <= T`, `0 < m`, `0 <= eta`, the source assignment `y`, and its source-violation bound. There is no hidden hypothesis that conditioning leaves base rows uniform; the prior transport theorem supplies the needed inequality instead.

7. **The kernel and certification evidence are coherent.** Main and Checks both exited 0 under Lean `4.34.0-rc2` with `LEAN_NUM_THREADS=1`. The isolated target was seeded with hashed dependencies while excluding both reviewed targets, and neither target object preexisted. Sources were stable before and after compilation. The independently observed object hashes are:
   - main: `C442B43E6F1523EE12CEA6709DA37CDCB48295C175CA6BEE9FA6E3556A1E7F81`;
   - Checks: `29AE123326A75ABCD57EF53415417053D11ED3B8D01D3D64C5317B30B51B0265`.

   Direct source scans and the evidence scan found no `sorry`, `admit`, `native_decide`, or explicit axiom declaration. Every reviewed theorem reports only `propext`, `Classical.choice`, and `Quot.sound`; no user-defined axiom appears. The sole main-module compiler message is a nonsemantic `letI` style warning, and the sole Checks warning concerns tactic sequencing.

8. **The fixtures test useful local branches but leave the headline instance weak.** Checks cover zero-coordinate failure, a satisfied one-coordinate tuple, a genuinely failed one-coordinate tuple, the `J = 0` final theorem, the `J = 1` uniform tuple bound, and the source-extension rate theorem. This supports the empty and nonempty algebra branches. The only direct fixture for `actualTaggedGoodFailureMean_sourceExtension_le` uses `J = 0`, so its conclusion is vacuous. The universally quantified theorem and its compiled proof remain valid, but a future Checks revision should instantiate the final theorem with a nonzero `J` and a source having both satisfied and violated rows. That would exercise the complete composition rather than only its constituent lemmas.

## Manuscript and dependency boundary

This increment rigorously supplies the single-question failure transport needed inside manuscript completeness lines 1137-1164. From a source assignment satisfying at least a `1-eta` fraction of its original equations, it proves that a good ordered tagged question contains some failed equation with mean at most

`(4/3) * J * eta`.

This matches the manuscript's conditioning and per-question union-bound mechanism, with `4/3` stronger than the displayed coarse factor `1/(1-a) <= 2` when `a <= 1/4`. It also confirms that equality-gadget rows added by the actual occurrence construction do not worsen the honest source extension's normalized failure rate.

It does **not** yet prove all of lines 1137-1164:

- the manuscript's stronger bad-mass branch `a <= tau/100` or its exact padding choice;
- the ordered-tuple to unordered set/subspace quotient and constant `J!` fibre law;
- the definition and uniform stationarity of each clique-resampled `U'_i`;
- the equal-dimension and equal-transverse-extension assertions;
- the aggregate union bound over the original question and all manuscript-resampled questions, including the manuscript parameter `(m+1)`;
- the arithmetic from the selected `epsilon_1` to `tau/75`, actual-star acceptance, the randomized reduction, or the headline hardness theorem.

The symbol `m` in this Lean module is the source instance's number of original equations. It must not be identified silently with the manuscript's count of resampled cliques in `(m+1)J epsilon_1`; that later sampler parameter needs its own formal binder and aggregate-event theorem.

The immediate consuming obligation should define the concrete collection of original and resampled questions, prove each has the required good-question marginal, and union-bound their failure indicators. If the manuscript's questions are sets or subspaces rather than ordered tuples, the constant-fibre ordered-to-unordered transport must be inserted before that assembly.

## Disposition

**GO-WITH-NOTES.** Accept the frozen module as the canonical actual-source-to-conditioned-tagged single-question failure bridge. Its event equivalence, fibre count, union bound, denominator manipulation, source-extension normalization, and `4/3 * J * eta` composition are mathematically sound and kernel checked. Keep its single-question/ordered-tuple scope explicit, add a nonvacuous final-theorem fixture in a later Checks-only increment, and do not cite it as establishing clique-resampling stationarity or the full manuscript completeness bound.
