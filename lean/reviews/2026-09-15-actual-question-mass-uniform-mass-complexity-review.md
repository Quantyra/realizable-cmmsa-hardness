# Uniform ordered-question mass: complexity-theory and manuscript review

Date: 2026-09-15  
Lens: top-level complexity theory / manuscript alignment  
Verdict: **GO-WITH-NOTES**

## Scope and frozen artifacts

This review is read-only with respect to the Lean sources. It checks the probability interpretation and manuscript role of the frozen rational mass theorem. I made no Lean edit, ran no compilation, and performed no commit, push, release, or public action. This review file is the only artifact written.

- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridge.lean`: SHA256 `414E679659581296AAEADB421729C0318D149428C6AC671EF217589EF55B433D`.
- `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualQuestionMassBridgeChecks.lean`: SHA256 `DF51EE8B4EA3BD46188AB71638DBD216EF852A2D57A247F15B0C9EE79B45A502`.
- Canonical evidence: `research/evidence/2026-09-15-actual-question-mass-uniform-mass-fresh-run/`.
- Evidence manifest `artifact-hashes.txt`: SHA256 `D42A3A37835210C8053884563008C7131DF81535BF5BA2F226B14D0B7373636F`.
- Manuscript `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md`: SHA256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`.
- Planning ledger `C:/Users/Dan/Desktop/Projects/IGH/Quantyra-Planning/docs/research/pvnp/full-theorem-obligation-ledger.md`: SHA256 `E091ABA41D68B30DB7F18EC2644BC27A78F2A2BFD2BB1F1BFD0C1B77A1ED48C2` at review time.

The evidence records main and Checks exits `0`, empty stderr, stable before/after source hashes, and newly generated target objects with hashes `D73F668AF001299D08991A8AC8C8A4B89CD8A10E292D3B0E9975AFF40AB0C6EF` and `7A7FC8438937806A724DA9E1D5A16BEEA6C38BD91F65E21DCB449355EE0859CF`. The target used 2,794 recorded dependency objects seeded from the preceding canonical run. The forbidden-token scan found no `sorry`, `admit`, `native_decide`, or user-declared axiom. Every printed declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact theorem and probability meaning

The new endpoint is

```lean
theorem actual_bad_ordered_question_uniform_mass_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (J : Nat) (hrows : 0 < Fintype.card I.RowId) :
    (((Finset.univ : Finset (Fin J → I.RowId)).filter
      (fun u => ¬ GoodOrderedQuestion I.support u)).card : ℚ) /
        (Fintype.card (Fin J → I.RowId) : ℚ) ≤
      ((J * (J - 1) * 157 : Nat) : ℚ) /
        (Fintype.card I.RowId : ℚ)
```

Let `M = Fintype.card I.RowId`. The sample space `Fin J → I.RowId` has cardinality `M^J`. Its uniform measure is exactly the joint law of `J` independent uniform row-identity draws with replacement: every ordered tuple has mass `1/M^J`. The left side is therefore exactly the bad-event probability under that law, represented in `ℚ`, rather than an estimate for a different distribution.

The event is also the intended deterministic event. `GoodOrderedQuestion I.support u` requires `u` to be injective and its image to satisfy the manuscript's pairwise support-disjointness and no-cross-equation-pair conditions. Consequently the numerator counts all and only the illegitimate ordered draws for the current incidence representation.

The theorem's algebra is sound. The intermediate declaration proves

```text
#bad * M ≤ J(J-1)157 * M^J.
```

It handles `J = 0` separately and uses `M^(J-1) * M = M^J` only for positive `J`. The final proof establishes positivity of both denominators and cross-multiplies in `ℚ`. Thus it does not use natural-number division, truncate the ratio, cancel a possibly zero factor, or silently assume `J ≥ 2`. For `J = 0` and `J = 1`, the right numerator is zero and the earlier theorem proves the bad set empty.

## Positive-row assumption

The sole new premise, `hrows : 0 < Fintype.card I.RowId`, is mathematically necessary for the displayed general sampling interpretation and for division by `M`. It is stated openly and used exactly to prove `0 < M` and `0 < M^J` in `ℚ`.

It is not discharged by this increment. An arbitrary `Instance N m` permits `m = 0`; in that case its original-row and gadget-row indices can both be empty. The outer-hardness construction should supply a positive equation count, or padding should construct a positive row universe, but Lean still needs an explicit bridge from that source premise to `hrows`. The fixture proves positivity only for its concrete two-row example. That fixture validates application shape and does not discharge positivity for the actual producer family.

The assumption is stronger than required for the isolated `J = 0` case, whose function space is a singleton even when `M = 0`. This harmless uniform statement is aligned with the manuscript regime, where fixed positive `J` rows are sampled from a nonempty outer instance.

## Constant `157`

The coefficient is preserved correctly from the certified actual-source specialization:

```text
1 + 3D + 9D² = 1 + 3·4 + 9·4² = 157.
```

Here `D = 4` is the occurrence-indexed incidence bound on the same `I.RowId` universe that is sampled. For each fixed first row, `157` bounds the conservative conflict neighbourhood: the equal row, direct support intersections, and cross conflicts mediated by a third row. The global count unions over `J(J-1)` ordered position pairs. Dividing by `M^J` therefore yields

```text
Pr[bad] ≤ 157 J(J-1) / M.
```

The theorem does not claim `157` is sharp or that the right side is at most one. It becomes a useful small-error estimate only after the construction makes `M` sufficiently large relative to the fixed `J` and target loss.

## Manuscript boundary

The result supplies the normalization step underlying manuscript lines 1148--1154: a uniform independent ordered-row bad probability of order `J²/M`. It does not yet establish the manuscript's retained legitimate law or conditioning claim.

1. **Copy padding remains open.** Lean needs a copied row, variable, support, and RHS construction with disjoint copy tags. It must prove that row count grows by the copy factor, support size remains three, incidence remains at most four, cross-copy conflicts do not arise, the representation stays polynomial in size, and the relevant source value and YES/NO promises are preserved. The copied row count must also be identified with, or quantitatively compared to, the manuscript's `N_outer`.

2. **The target retained mass remains open.** Given a chosen `a`, the next theorem must combine the rational bound with a padding inequality to show `Pr[bad] ≤ a`, hence `Pr[good] ≥ 1-a > 0`, with `a ≤ min(tau/100, 1/4)`. The present upper bound alone can exceed one and does not establish positive good mass.

3. **Conditioning remains open.** The manuscript uses `Pr[failure | good] ≤ Pr[failure]/(1-a)`. That needs a defined finite conditional law, a positive good-event denominator, and the corresponding inequality. An efficient rejection sampler or another polynomial-time implementation of the conditioned law is also outside this theorem.

4. **Ordered tuples and question objects remain distinct.** The theorem samples ordered functions with replacement and then restricts to injective good tuples. If the manuscript's later `U` is treated as an unordered `J`-row set or its span object, Lean must prove that every legitimate set has exactly `J!` orderings and that the image pushforward is uniform. If the formal star retains an ordered tuple, it must instead prove that later constructions are invariant under, or consistently retain, that order. Neither bridge follows merely from the ratio.

5. **Clique-resampled marginals remain open.** Manuscript lines 1155--1158 claim that each `U'_i` is uniform over legitimate `U` after resampling inside an equivalence class, based on equal dimensions and equal numbers of transverse extensions. This is a separate finite fibre-counting or measure-preservation theorem. Initial uniformity after conditioning does not by itself prove the resampled marginal.

6. **Weighted laws remain open.** The star-projection CSP later has edge and occurrence weights. This theorem concerns only the initial uniform product law on row identities. It cannot be applied unchanged to an arbitrary weighted or nonuniform row law. Such a transfer needs the claimed uniform marginal, or a new weighted incidence/maximum-atom estimate.

The direct dependency path is therefore

```text
positive actual row count
  → disjoint-copy padding and value preservation
  → choose M so 157 J(J-1)/M ≤ a
  → positive retained good mass
  → conditioning loss
  → ordered-to-question pushforward
  → clique-resampling marginal and later weighted tables.
```

Beyond this path, the full manuscript still requires the RHS functional and dimension statement, minimal label transport, the actual star and acceptance theorem, rational table construction, polynomial-time/probability bridge, headline randomized-reduction assembly, learning corollary, and final manuscript reconciliation.

## Decision

**GO-WITH-NOTES.** The frozen theorem is a correct rational normalization of the certified `D = 4` bad ordered-tuple count. Its left side is precisely the bad probability for independent uniform ordered row draws, its positivity premise is explicit and used correctly, and `157` is the correct inherited conservative coefficient.

The notes are remaining manuscript dependencies rather than defects in this theorem. Positive row count for the actual producer, copy padding and value preservation, a parameterized retained-mass theorem, conditional-law control, ordered-to-subset transport, clique-resampling uniformity, and weighted-law compatibility are still unproved. This increment does not establish those statements, actual-star acceptance, a hardness reduction, P versus NP, full manuscript completion, or publication readiness.
