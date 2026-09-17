# Proof-adversarial review: tagged question-mass bridge

**Verdict: GO-WITH-NOTES.** The frozen increment correctly proves the unconditioned independently tagged tuple equivalence, its exact full-space and base-event fibre counts, the exact same-tag characterization of copied-row conflict in all three `rowConflict` branches, the resulting not-good characterization and conflict-fibre equivalence, and the generic tagged bad-tuple count and rational mass upper bounds. The natural-number arithmetic covers `J = 0` and `K = 0`; the rational theorem correctly requires `K > 0` and a nonempty base row type. I found no inverse failure, missing conflict branch, event mismatch, subtraction error, invalid cancellation, denominator-orientation error, cast defect, or certification blocker.

The notes are material scope boundaries. The factor `K` gives a `1/K` improvement in the proved upper bound, but the module does not prove that the full tagged bad-event probability is exactly the base bad-event probability divided by `K`. It also does not prove that the base projection remains uniform after conditioning on tagged goodness. In general that conditioned projection is biased because different base tuples admit different numbers of good tag functions.

## Frozen artifacts and evidence

| Artifact | SHA-256 |
|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedQuestionMassBridge.lean` | `B258BB7FE60CFC4D7AA17F45427B94060B3F896D9A5565DE2EA07B2D7C349CBE` |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedQuestionMassBridgeChecks.lean` | `35CFE1C0AE7B8C9C9309973D86E21BCC514BFDBFDFA01AD43CE2593B0CA655A6` |
| canonical `bundle-manifest.txt` | `735382C87BD28B428F3076B7718DC7432E62CBCF63A41C0FD43C03AC0540E89F` |

I independently recomputed both source hashes, the bundle-manifest hash, and every one of the 33 byte-count/SHA-256 entries in `artifact-hashes.txt`; all match. The canonical evidence directory is `research/evidence/2026-09-15-tagged-question-mass-bridge-fresh-run/`. Its before/after records show stable source bytes.

Main and Checks exited `0` with empty stderr. Their newly emitted object hashes are respectively `93670709D4269EAD91230A4CB7A89351E75D89DECBC6D5061E254B2F19027EA2` and `FE510A8CA3F46FA4D76EA9D695081EE743B957EC3FE6D8DC9571352E862B3649`. The isolated target was seeded with 2,800 recorded dependency outputs from the prior tagged-source certification while excluding the two current objects; both were absent before sequential main-then-Checks compilation. This is a fresh build of the reviewed modules against pinned compiled dependencies, rather than a clean source rebuild of every transitive dependency.

The forbidden scan has no matches for `sorry`, `admit`, `native_decide`, or a source-level user axiom. Its exit code `1` is the expected `rg` no-match result and is correctly recorded as clean. Checks reports no axioms for `tagProjection` and `baseProjection`; the other declarations use only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies, with the tuple equivalence and its two application lemmas omitting `Classical.choice`. Main has four unused-`simp`-argument linter warnings and Checks has none. The preserved preflight diagnostic records an earlier malformed search-path command, and the prior Checks failure summary records repairs to the concrete fixture only; the canonical commands and exit receipts show that neither diagnostic is a failure of the frozen main or Checks build.

The reviewed files and evidence directory are untracked above repository commit `d077535dcfa8a97ec8887c205a7e8f4fa73ebe28`. The content hashes freeze the reviewed bytes; this review does not claim that those bytes are already committed.

## Tuple equivalence, inverses, and cardinality

`taggedTupleEquiv` maps a tagged tuple `u : Fin J -> Fin K × Row` to the coordinatewise pair

```text
(j |-> (u j).1, j |-> (u j).2).
```

Its inverse zips a tag function and a base-row function pointwise. The left inverse reduces each product entry to its two projections; the right inverse is definitional after destructuring the outer pair. The two `[simp]` application theorems expose exactly these maps. No permutation, quotient, shared-tag restriction, or loss of coordinate dependence occurs.

`taggedTuple_card` transports cardinality across this equivalence and gives the product of the two function-space cardinalities. Consequently the sample carrier is the intended independently tagged global law: every coordinate has its own tag, rather than one tag being selected for the entire tuple.

For any finite base event `A : Finset (Fin J -> Row)`, `baseProjectionEventEquiv` restricts the same equivalence to tuples whose base projection lies in `A`. Its inverse pairs an arbitrary tag function with an element of `A`, and both subtype inverses are exact. `baseProjection_event_card` therefore proves

```text
card {u : Fin J -> Fin K × Row | baseProjection u in A}
  = K^J * card A.
```

This includes all raw edge cases. If `J = 0`, there is one tag function even at `K = 0`, because `0^0 = 1`; the event is present exactly when its unique empty base tuple lies in `A`. If `J > 0` and `K = 0`, both the tagged function space and every event fibre are empty, and `0^J * card A = 0`. No positivity assumption is needed for this cardinality theorem.

## Exact tagged conflict characterization

`taggedCopy_rowConflict_iff` proves

```text
rowConflict (I.taggedCopy K).support (k,q) (l,r)
  iff k = l and rowConflict I.support q r.
```

The proof covers each disjunct of `rowConflict` exactly:

1. Equality of copied rows gives tag equality from the first projection and base-row equality from the second projection.
2. A copied support element common to both rows has both tag forms `(k,a)` and `(l,b)`, forcing `k = l` and `a = b`; the common base variable witnesses base support overlap.
3. A copied witness row `(m,s)` meeting both supports forces `k = m` and `l = m`; stripping tags from the two witness variables gives the required base cross-row witness.

Conversely, copied pair equality, copied support overlap, and a copied cross witness are constructed at the common tag. The proof neither drops the row-equality branch nor treats only direct support intersection. For `K = 0` the universally quantified statement is vacuous because no copied row exists, which is the correct boundary.

Rewriting the previously certified `not_goodOrderedQuestion_iff_conflicting_pair` with this iff yields `taggedCopy_not_good_iff`: a tagged tuple is bad exactly when two distinct coordinates have equal tags and conflicting base rows. The coordinate inequality remains explicit, so row self-conflict does not make a length-one tuple bad.

`taggedConflictFibreEquiv` then fixes `(k,q)` and sends each conflicting copied row to its base row. The conflict iff forces the copied row's tag to equal `k`, making the inverse `(k,r)` exact. Hence each copied conflict neighbourhood has exactly the base conflict-neighbourhood cardinality, not `K` times that cardinality.

## Raw count and zero-size cases

Given a uniform bound `C` on every base conflict-neighbourhood cardinality, `tagged_bad_ordered_question_count_le` applies the generic bad ordered-question union bound to `I.taggedCopy K`. The conflict-fibre equivalence supplies the same `C`, and product-cardinality simplification gives

```text
badCard <= J * (J - 1) * C * (K * card Row)^(J - 1).
```

The event is exactly `not GoodOrderedQuestion (I.taggedCopy K).support`; there is no substitution of a base-bad event. The coefficient counts oriented distinct coordinate pairs, as in the consumed generic theorem.

The theorem is valid at both raw boundaries. At `J = 0`, the coefficient is zero and the sole empty tuple is good, so `badCard = 0`. At `K = 0` and `J > 0`, there are no tagged tuples. For `J = 1` the coefficient `J * (J - 1)` is zero even though the displayed power has exponent zero; the bad set is empty because no distinct coordinate pair exists. No use of `0^0` creates a false positive.

The cross-multiplied theorem proves

```text
badCard * (K * card Row)
  <= (J * (J - 1) * C) * card (Fin J -> Fin K × Row).
```

Its `J = 0` branch derives `badCard = 0` from the raw count. If `J > 0` and `K = 0`, it proves both the tuple-space cardinality and the bad cardinality are zero. In the remaining branch, positivity of `J` justifies

```text
(K * card Row)^(J - 1) * (K * card Row)
  = (K * card Row)^J,
```

and no natural-number factor is cancelled. The proof does not need positivity of `card Row` for this count theorem; if the row type is empty, the same zero-cardinality arithmetic remains valid.

## Rational normalization

`tagged_bad_ordered_question_uniform_mass_le` assumes `0 < K` and `0 < card Row` and proves

```text
badCard / card (Fin J -> Fin K × Row)
  <= (J * (J - 1) * C) / (K * card Row)
```

over `Rat`. `exact_mod_cast Nat.mul_pos hK hRow` correctly proves positivity of the right denominator. Rewriting the full tuple cardinality as `(K * card Row)^J` and using `pow_pos` correctly proves positivity of the left denominator for every `J`, including `J = 0`. The call to `div_le_div_iff₀ hT hR` uses the full-space denominator first and the row-carrier denominator second, generating exactly the already proved cross-multiplied inequality.

The explicit `J = 0` rational branch proves the bad numerator is zero. For `J > 0`, `Nat.cast_sub` is justified by `1 <= J`, so the rational expression `J - 1` agrees with the cast of natural truncated subtraction. `exact_mod_cast` then transports the natural cross inequality without reversing it or cancelling a possibly zero factor. There is no rational theorem for `K = 0`, appropriately avoiding a zero tag denominator and any probability interpretation of totalized division by zero.

## Fixture audit

Checks certifies four proposition-level fixtures:

- a singleton base event for `J = 2`, `K = 2`, and three base rows has fibre cardinality `4 = 2^2`;
- the complete tagged tuple space in that example has cardinality `36 = (2 * 3)^2`;
- a one-row source at `J = 2`, `K = 2` has exactly two bad tuples among four, namely the two constant-tag tuples;
- the rational mass theorem applies to the same one-row source with `C = 1`.

The exact bad-count fixture is nonvacuous and simultaneously exercises row self-conflict, the distinct-coordinate requirement, equal-tag detection, and unequal-tag rescue. The normalized fixture checks theorem application rather than computing a sharp rational equality; the generic proof is the kernel-checked evidence for denominator arithmetic and all `J`. There is no conditioned-law fixture, consistent with that theorem being absent.

## What the factor `1/K` does and does not establish

The increment proves an upper bound with denominator `K * card Row`, so relative to the same conflict-degree union bound on the base carrier it gains a factor `1/K`. It does not prove

```text
Pr[tagged tuple is bad] = Pr[base tuple is bad] / K.
```

A base tuple can contain several conflicting coordinate pairs. The tagged bad event is the union of the corresponding equal-tag events, whose overlaps prevent an exact global `1/K` formula. The exact fibre theorem concerns the unconditioned base-projection event, not the bad event.

Nor does the unconditioned fibre count imply uniformity of the base projection after conditioning on tagged goodness. For a fixed base tuple `r`, the number of retained tag functions is the number of proper `K`-colourings of its coordinate conflict graph. That number depends on the conflict pattern. A base-conflicting tuple may be retained when its conflicting coordinates receive different tags, while a conflict-free base tuple retains every tag function. Therefore the conditioned pushforward can weight base tuples differently and is not established as the uniform base-good-tuple law.

## Direct consumer and disposition

The direct consumer should instantiate `tagged_bad_ordered_question_uniform_mass_le` for `Finite3LinSource.ofActual I` using the certified actual conflict bound `C = 157`, choose an explicit positive fixed `K`, and derive a useful strict retained-good-mass bound such as

```text
Pr[tagged GoodOrderedQuestion]
  >= 1 - 157 * J * (J - 1) / (K * card I.RowId) > 0.
```

That consumer should also use `baseProjection_event_card` only for the unconditioned product law. A separate repeated-game/star-distribution transport theorem is required before the copied source can feed actual-star acceptance; it must state the law actually preserved and must not assert uniform conditioned base projection. Structural support/incidence facts, actual-source value specialization, the fixed-`K` encoded producer, conditioning loss, and ordered-to-subset or clique-resampling laws remain separate obligations.

**GO-WITH-NOTES.** Accept the tuple equivalence and event fibre, all three branches of the tagged conflict iff, the not-good and conflict-fibre equivalences, the raw and cross-multiplied counts including their empty cases, and the positive-denominator rational normalization. The notes prevent promotion of the upper-bound factor into an exact full-event `1/K` identity or a conditioned-uniformity claim.
