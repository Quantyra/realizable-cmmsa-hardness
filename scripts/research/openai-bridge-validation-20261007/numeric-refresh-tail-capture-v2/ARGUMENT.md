# Actual dual-label tail and bounded preserving history

Status: disjoint continuation of the immutable refresh product and tail captures. The source in this offer contains a named uncompiled Real finite-sum Markov/tail candidate `actual_match_tail_bound`, a finite candidate-union inequality, strict-tail event with the zero-coordinate case, positive-mass table existence, and a bounded adaptive finite-choice path. It does not yet instantiate the concrete manuscript candidate cardinality, prove the potential stop, or state the many-Q conclusion.

## Actual-law moment and strict tail

Fix the coordinate ambient, dimension `d`, arbitrary target table `G`, and a finite set `Z` of distinct actual `d`-spaces. Let `Y(F)` be the number of `L ∈ Z` whose freshly drawn dual label equals `G(L)`, and `M=|Z|`. The predecessor source's `refreshMoment_eq` gives, for the uniform law on the actual product `LeafTable`,

```text
E[2^Y] = (1 + 2^-d)^M ≤ exp(2^-d M).
```

This moment uses one independent coordinate for each distinct subspace, with a fiber of exactly `2^d` dual labels. The prescribed target fixes one value in each constrained fiber. No ambient functional is sampled and no repeated leaf creates another coordinate.

Write `p=2^-d`. For `M=0`, `Y=0` for every fresh table, so the strict event `Y>2pM` is empty. For `M>0`, Markov applied to the positive variable `2^Y` gives

```text
Pr[Y > 2pM] ≤ E[2^Y] / 2^(2pM)
             ≤ exp(-(2 log 2 - 1)pM)
             ≤ exp(-pM/3).
```

The threshold is Real-valued and the event remains strict, including when `2pM` is an integer. The last inequality is `log 2 > 2/3`, from the pinned `Real.log_two_gt_d9`. The source candidate expresses `2^Y` as `exp(Y log 2)`, uses monotonicity of `exp` on the strict event, sums over the finite uniform product, casts the rational exact moment to Real, and divides by a positive exponential. It then applies the pinned logarithm inequality. The candidate is uncompiled and is not kernel evidence.

## One-state all-candidate preservation

For one fixed pre-refresh state `(T₀,X)`, freeze the complete finite universe of all manuscript zoom descriptions `(Q,W,g)` before drawing the fresh table. For each candidate, let `Z=X∩Zoom(Q,W)` and `M=|Z|`. If `M < p |Zoom|`, its refreshed matching contribution has density below `p` deterministically. Otherwise the Gaussian lower bound gives

```text
M ≥ 2^-d · 2^((d-r)(n-r-d)),
pM ≥ 2^E/4,
E = -4h + 2 + (2h-r)(n-r-2h),  d=2h.
```

The strict Real tail above bounds each candidate's exceptional fresh tables by `exp(-2^E/12)`. The full universe has at most `16(r+1)^2 2^(n(r+1))` members, counting all `a+c=r`, all subspaces `Q,W`, and all linear maps `g:W→F₂`. The finite union inequality in `ExactRefreshTail.lean` applies before the inverse output is observed, so it covers any inverse output chosen adaptively from the refreshed table. It does not rely on independence between that output and the table.

Thus the one-step failure mass is at most

```text
F_n = 16(r+1)^2 2^(n(r+1)) exp(-2^E/12).
```

The fixed-floor numerical prerequisite `F_n<1` is separately supplied by the captured Real robust-cutoff offer; it is not reproved here. Once the actual candidate family is instantiated and its cardinal bound connected to this expression, strict inequality makes the complement of the failure union have positive mass. `exists_preserving_fresh_table` extracts a table from that complement for every fixed pre-refresh state. It refreshes every coordinate in `X` and preserves `T₀` outside `X` by the predecessor's exact update equations.

## Bounded successful history and the original potential

Use a horizon `B=ceil(8·2^(rn)/e)+1`. At each state, choose any fresh table in the positive-mass complement of the complete candidate failure union, update the accumulated set, and then compute the next inverse output from that chosen table. `preservingRun` and `preservingHistory` encode finite recursive choices whose state can depend on the entire earlier prefix. This proves existence of a preserving path once the per-state bound is instantiated; it does not establish the separate random-history event statement `Pr[any failure]≤B F_n`.

On a preserving state, any selected inverse zoom has at most `2p` agreement from refreshed coordinates. If its total current-table agreement exceeds `e`, at least `e-2p≥e/2` lies outside `X`, where the table is the original table by `refresh_outside`. The zoom's global mass is at least `2^-rn/4`. Therefore each successful nonterminal step adds more than `e·2^-rn/8` to `μ(X)`. Since `μ(X)≤1`, `B` such steps are impossible. The process stops with density below `epsilon_A/2`; no monotonic decrease of density is assumed.

The ordinary accepted-star event changes only if one of its `m` leaf occurrences lies in `X`. Each occurrence has uniform marginal among all actual `d`-spaces by the exact incidence count, including repetitions. Hence its change is at most `m μ(X)`, and `μ(X)>epsilon_A/(2m)`.

Deduplicate the successful inverse advice spaces `Q`. Assign one witnessing successful visit to each distinct `Q`; each contributes its own dimension pair `(a,c)`, with `a+c=r`. The union of all `d`-spaces in `X` is covered by the families containing these recorded `Q`s. Gaussian counts yield

```text
μ(X) ≤ Σ_(a,c) N_(a,c) 2^(4h²-an),
Σ_(a,c) f_(a,c) > epsilon_A 2^(-4h²)/(8m),
f_(a,c)=N_(a,c)/T_a.
```

On complements with initial density at least `4S`, this is at least `4S·2^(-4h²)/(8m)`. The mass of such complements is at least `4S` when mean initial density is at least `8S`. Set the contribution to zero on the other complements and average under the full, unconditioned complement law. Then `Σ_(a,c) E[f_(a,c)] ≥ 2S²·2^(-4h²)/m`, so a dimension pair has mean at least the manuscript's weaker `2S²·2^(-4h²)/(m(r+1)^3)`. Successful complements are never renormalized.

## Remaining formal and research obligations

The new Lean module does not yet prove the Real Markov estimate, plug the concrete `(Q,W,g)` carrier into the generic all-candidate union theorem, connect the captured `F_n<1` cutoffs, formalize the potential stopping argument and incidence/counting composition, or state the final many-Q theorem. The argument above remains a mathematical derivation, not kernel-checked evidence. Source decoding, H-extension transports, native GCP compilation and profiles, and the required independent review gates remain open.
