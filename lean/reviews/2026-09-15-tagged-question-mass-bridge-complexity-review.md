# Tagged question-mass bridge: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for S3138  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment proves the correct finite product semantics for independently tagged ordered questions and the correct `1/K` improvement in the conservative conflict union bound. For a base row universe of size `M` with conflict fibres bounded by `C`, the certified endpoint is

```text
Pr[tagged ordered question is bad]
  <= J(J-1)C / (K M).
```

The factor is mathematically correct. A tagged row `(k,q)` can conflict only with rows `(k,r)` in the same tag, so its conflict fibre has the same size as the base conflict fibre, while the sampled row universe grows from `M` to `K M`. There is no missing factor of `K` in the numerator.

This is a force-bearing advance toward manuscript retained mass: it supplies the quantitative dilution that plain untagged counting lacked. It does not itself choose `K`, instantiate the actual constant `C = 157`, prove a positive good-mass lower bound, or justify conditioning and star transport. S3138 and the manuscript headline therefore remain open.

## Frozen artifacts and evidence

| Artifact | Reviewed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedQuestionMassBridge.lean` | `B258BB7FE60CFC4D7AA17F45427B94060B3F896D9A5565DE2EA07B2D7C349CBE` | Exact requested frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/TaggedQuestionMassBridgeChecks.lean` | `35CFE1C0AE7B8C9C9309973D86E21BCC514BFDBFDFA01AD43CE2593B0CA655A6` | Exact requested frozen Checks source. |
| `research/evidence/2026-09-15-tagged-question-mass-bridge-fresh-run/bundle-manifest.txt` | `735382C87BD28B428F3076B7718DC7432E62CBCF63A41C0FD43C03AC0540E89F` | Exact requested evidence manifest. |

The evidence records fresh target objects for the main and Checks modules, main/Checks exits `0/0`, empty stderr, and unchanged before/after source hashes. The run used Lean `v4.34.0-rc2` and 2,800 recorded seeded dependency objects, excluding the two reviewed target objects. The forbidden scan is empty. The printed declarations use only the standard inherited axioms `propext`, `Classical.choice`, and `Quot.sound`; there is no user-declared axiom. This is target-fresh certification against recorded cached dependencies, not a full rebuild of every transitive dependency from source.

## Independent tag/base semantics

The equivalence

```text
(Fin J -> Fin K x Row)
  ~= (Fin J -> Fin K) x (Fin J -> Row)
```

is the right global carrier. A uniform point of the left side is exactly a uniform tag function together with a uniform base-row function. Since a uniform function `Fin J -> Fin K` assigns each coordinate independently and uniformly, this is the independently tagged law required by S3138, rather than a law that chooses one common tag for the whole `J`-tuple.

`taggedTuple_card` proves the product cardinality, and `baseProjection_event_card` proves the constant-fibre identity

```text
# {u | baseProjection u in A} = K^J * #A.
```

Consequently, when `K > 0` and `Row` is nonempty so normalized uniform laws exist, the base projection of the unconditioned tagged law is exactly uniform. The fibre theorem is stronger than a heuristic marginal claim: every base tuple has exactly `K^J` tagged lifts.

The module does not introduce a probability-measure object or export a named pushforward/independence theorem. Its equivalence and equal-fibre cardinality theorem nevertheless certify the exact finite uniform product semantics needed for the unconditioned count. A later probabilistic API may package this result, but it must not replace the per-coordinate tag function by one shared tag.

## Conflict characterization and combinatorial factor

`taggedCopy_rowConflict_iff` proves

```text
rowConflict(taggedCopy I K) (k,q) (l,r)
  <-> k = l and rowConflict(I) q r.
```

This includes all three base conflict branches: equal row identity, direct support intersection, and the cross-row witness. Different tags make the copied variables disjoint, so none of those conflicts crosses tags. `taggedCopy_not_good_iff` then gives the exact bad-event witness: two distinct sample positions whose tags agree and whose base rows conflict.

For each fixed tagged anchor `(k,q)`, the conflict fibre is equivalent to the base conflict fibre at `q`. Hence if every base fibre has size at most `C`, every tagged fibre still has size at most `C`, although the tagged universe has size `K M`. The generic ordered-pair count therefore yields

```text
#bad <= J(J-1) C (K M)^(J-1).
```

There are `J(J-1)` ordered pairs of distinct positions. This is conservative because a bad tuple may have multiple witnesses and, for the symmetric conflict relation, the reverse position pair witnesses the same conflicting pair. That double counting is harmless and matches the previously accepted base bound. Dividing by the exact total `(K M)^J` gives

```text
Pr[bad] <= J(J-1)C/(K M)
```

under `K > 0` and `M > 0`. The proof handles `J = 0` and `K = 0` separately at the count level and imposes positivity only for the normalized rational statement. For `J = 0` or `J = 1`, the bad event is empty and the displayed numerator is zero.

For the actual post-regularization source, the accepted incidence argument gives `C = 157`. After the route-facing specialization, the exact certified form should be

```text
Pr[bad] <= 157 J(J-1)/(K * card I.RowId).
```

With the copied outer equation count defined as

```text
N_outer = K * card I.RowId = K * I.rows.length,
```

this is precisely the manuscript form `157 J(J-1)/N_outer`, and therefore `O(J^2/N_outer)` for fixed bounded-occurrence constant. `N_outer` must remain distinct from the raw variable count `N`, the raw equation count `m`, and the uncopied semantic row count.

## Exact pair dilution versus full bad-tuple probability

The phrase “a `1/K` improvement” needs a precise scope.

For one fixed ordered pair of sample positions, the dilution is exact. If `B` is the number of ordered conflicting base-row pairs, then the tagged pair event has `K B` conflicting tagged pairs among `(K M)^2` pairs, while the base event has `B` conflicting pairs among `M^2`. Thus

```text
Pr[tagged conflict at fixed positions]
  = (1/K) * Pr[base conflict at fixed positions].
```

The Checks fixture with one base row, `J = 2`, and `K = 2` witnesses this sharply: two of the four tagged tuples are bad, so the tagged bad probability is `1/2`, exactly half the base probability `1`.

For the union over all position pairs, no exact identity of the form

```text
Pr[tagged tuple bad] = (1/K) * Pr[base tuple bad]
```

is proved or generally true. A base tuple may have several conflicting pairs, and the events that their endpoint tags agree overlap according to the tuple's conflict graph. The theorem correctly uses a union bound, so its result is an upper bound with a `1/K`-improved denominator, not an exact formula for arbitrary tuple bad probability.

## Retained mass and conditioning boundary

This increment supplies the missing quantitative engine for retained mass, but does not finish the retained-mass theorem. To obtain the manuscript tolerance `a <= min(tau/100, 1/4)`, the route still must:

1. instantiate `Row := I.RowId` and `C := 157`;
2. discharge positive base row count;
3. choose an explicit positive fixed `K` satisfying

   ```text
   157 J(J-1)/(K * card I.RowId) <= min(tau/100, 1/4);
   ```

4. derive `Pr[good] >= 1-a > 0`; and
5. connect that finite ratio to the exact sampler used by the downstream reduction.

The manuscript's claim that the required number of copies depends only on fixed parameters also needs the precise small-input policy. If the starting family has a uniform positive lower bound on `card I.RowId`, a fixed `K` can be selected from that bound. Otherwise the construction needs the stated additive padding or a threshold branch, with the encoded producer proving the resulting output size and running time.

Conditioning on tagged goodness does not preserve the uniform base-row projection. For a base tuple `r`, form the conflict graph on positions, with an edge for each conflicting base-row pair. The number of tag functions that make the tagged lift good is exactly the number of proper `K`-colorings of that graph. Thus the conditioned base marginal is weighted in proportion to this coloring count. Base-good tuples have `K^J` lifts, while many base-bad tuples also survive by placing conflicting positions in different tags. The conditioned projection is therefore generally neither uniform over all base tuples nor supported only on base-good tuples.

This does not invalidate conditioning on legitimate tagged questions in the copied universe. It means the downstream star/repeated-game argument must be rebuilt or transported on that tagged universe. A theorem that simply projects the conditioned law back to the original base game would be false.

## Remaining star and complexity obligations

Before this padding can feed the manuscript star construction, the route still needs:

- a route-facing actual-source theorem with `C = 157`, copied `N_outer`, and an explicit retained-mass lower bound;
- support-size-three, incidence-degree-at-most-four, same-tag intersection, and cross-tag disjointness facts at the exact star consumer interface;
- a conditioned tagged-question sampler and ordered-to-legitimate-subset transport in the copied universe;
- proof that clique/equivalence-class resampling has the claimed uniform legitimate tagged-question marginal;
- transport of `H_U`, equation side conditions, labels, RHS satisfaction, and honest failure across tagged star questions and all resampled questions;
- the fixed-`K` encoded producer, decode correctness, all-word FP theorem, and polynomial output-size/runtime bound; and
- the remaining imported/local star, maximal-pair, reduction, and claim-boundary obligations already recorded by the manuscript ledger.

The previously certified semantic optimum theorem proves that tagged disjoint copies preserve the post-regularization finite 3-LIN value. Combined with this increment, the route now has both semantic value preservation and the correct unconditioned mass dilution. It still lacks their encoded and conditioned-star composition.

## S3138 and headline limits

S3138 may record the following obligations as discharged at the generic semantic/counting level:

- exact global tagged/base tuple equivalence;
- exact constant-fibre base projection under the unconditioned uniform carrier;
- exact same-tag/base-conflict characterization; and
- the generic normalized bound `J(J-1)C/(K * card Row)`.

S3138 must remain **Active** for the actual specialization, explicit `K`, positive retained mass, copied-star distributional transport, structural consumer bundle, `N_outer` interface, and encoded polynomial producer. The stop-loss against proceeding directly from copy cardinality to conditioning remains applicable, although this increment is substantive progress rather than packaging drift.

The exact accepted claim is:

> For a finite 3-LIN semantic source whose base row-conflict fibres have size at most `C`, independently and uniformly tagging each coordinate of a uniform ordered `J`-row tuple with one of `K > 0` tags preserves a uniform base projection and bounds the probability of a bad tagged tuple by `J(J-1)C/(K * card Row)`, provided the base row carrier is nonempty.

Do not strengthen this to exact `1/K` scaling of the full bad event, uniformity of the conditioned base projection, a completed retained-law/star transport theorem, an encoded polynomial reduction, hardness, a proof-system or circuit lower bound, P versus NP, novelty, manuscript completion, or publication readiness.
