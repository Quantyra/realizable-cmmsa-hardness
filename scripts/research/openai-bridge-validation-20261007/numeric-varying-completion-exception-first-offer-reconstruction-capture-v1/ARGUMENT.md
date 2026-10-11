# Varying-completion advice exception: mathematical argument

## Scope and claim status

This offer concerns an arbitrary draw-indexed family `H : Draw J → Submodule (ZMod 2) (Vector J)` with `finrank H(s) ≤ J`. The family may depend on the entire draw. It proves a bound on actual conditional advice mass and then transports that bound through the actual prior/joint/posterior law. It does not assume independence between `H(s)` and `s`, does not replace the draw-indexed family by an independent subspace, and does not assume any target event mass bound. The companion application file binds the theorem to the actual visible-completion pullback and proves the pointwise event equivalence in the same draw and advice coordinates.

The source-level inputs are the pinned `TripleRestrictionRank`, `TripleRestrictionDimension`, `GrassmannIncidence`, `GrassmannCounting`, `RobustSourceLineContainment`, `DropCountTail`, `PosteriorReweighting`, `PosteriorDensity`, and `AdviceExceptions` modules from the Full114 archive. The full archive SHA-256 is `70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`; mathlib pin is `e06eff5f95374108acfaf19f1ff7473aa7771df2`. The four directly imported exception/counting modules were byte-checked against the exact Full114 archive. The actual pullback is a separate uncompiled candidate dependency whose source hash is preserved in the manifest; this offer does not promote that parent to accepted status. No local compiler, Lake, cloud, or Git action is claimed.

## Drawwise actual conditional kernel bound

Fix a draw `s`, write `R = retained(s)`, and let `H_s = H(s)`. The actual advice kernel `kernel(s,Q)` is zero unless `Q ≤ R`; on that support it is the reciprocal of `incidenceCount(s,a)`. By `GrassmannCounting.incidenceCount_eq` and `card_contained`, this denominator is exactly the cardinality of the ambient `a`-Grassmannian slice `{Q : Grass(Vector J,a) // Q ≤ R}`. Via `containedEquiv R`, this is precisely the set of `a`-subspaces of `R`; hence the kernel event mass is the uniform fraction of those subspaces whose ambient intersection with `H_s` is nonzero.

Restrict the possibly draw-dependent exception space to the actual retained space: `H'_s = H_s.comap R.subtype`. Its dimension is at most `finrank H_s ≤ J`. On supported advice `Q ≤ R`, the intersection `Q ∩ H_s` is nonzero iff the restricted subspaces `Q.comap R.subtype` and `H'_s` have nonzero intersection. This is a direct elementwise equivalence: a witness in the ambient intersection is already in `R` because `Q ≤ R`, and a witness in the restricted intersection maps to one in both ambient spaces. Thus no distributional assumption on `H_s` is used.

When `a = 0`, every advice subspace is bottom, so the exception event is empty and the actual conditional mass is exactly zero. This case is handled explicitly rather than invoking the positive-dimension incidence theorem. For `1 ≤ a`, apply `RobustSourceLineContainment.transverseException_mass_le_dyadic` inside `R` to `H'_s` and dimension `a`. Let `n_s = finrank R = 3J - 2*dropCount(s)`. The supplied hypotheses `dropCount(s) ≤ T` and `J+a+1 ≤ 3J-2T` imply `J+a+1 ≤ n_s`; since `finrank H'_s ≤ J`, its required slack hypothesis follows. The kernel event count is identified with the restricted Grassmann count using the contained-space equivalence, while the denominator is `gaussian (finrank R) a` by the actual incidence-count identity. The theorem exponent satisfies `2J-2T-a-1 ≤ n_s-finrank(H'_s)-a-1`. Therefore the target power is at most the theorem power and its reciprocal is at least the theorem reciprocal; the dyadic upper bound follows in the correct direction. This is a per-draw bound for the actual draw-specific `H_s`.

## Actual joint mass

For any fixed draw, the kernel is a normalized probability law on advice (`kernel_normalized`) and is nonnegative. Therefore the exception mass is at most one on every draw. Split the actual prior sum into draws with `T < dropCount(s)` and draws with `dropCount(s) ≤ T`. The first part is bounded by the actual prior tail `priorTail β J T`; on the second use the drawwise dyadic bound just proved. Since the actual prior is normalized, the second part is at most the dyadic bound. Consequently the actual joint exception mass

`Σ_s prior(β,s) * Σ_Q [Q ∩ H(s) ≠ ⊥] kernel(s,Q)`

is at most `priorTail β J T + 1/2^(2J-2T-a-1)`. This is an upper bound on an actual joint-law sum, not an inference from bounds on a different event.

## Posterior averaging, zero marginals, and Markov

For each advice `Q`, define its posterior exception mass as the actual conditional draw mass of the draw-dependent event `Q ∩ H(s) ≠ ⊥`. Averaging this value under the actual advice marginal equals the joint exception mass above. Expand both finite sums and commute their order. At each `(s,Q)`, if the advice marginal is positive, use `PosteriorReweighting.bayes_mass`; if it is zero, use `joint_zero_of_marginal_zero` together with the posterior's zero-denominator convention. Thus zero-marginal atoms contribute zero on both sides and no conditioning on positive-marginal advice is silently introduced.

For any threshold `ζ > 0`, pointwise Markov gives `ζ * 1_{ζ < posteriorException(Q)} ≤ adviceMarginal(Q) * posteriorException(Q)`. Summing and using the posterior-average identity bounds the actual marginal mass of bad-posterior advice by `(priorTail + dyadic)/ζ`. Finally `AdviceExceptions.ambient_event_transfer` moves this event from the actual marginal advice law to the uniform ambient advice law, adding exactly `adviceTV β J a`. Therefore the ambient bad-posterior mass is at most `(priorTail β J T + 1/2^(2J-2T-a-1))/ζ + adviceTV β J a`.

## Verification boundary

The offer must expose the restriction/intersection equivalence, the kernel-to-contained-Grassmann count identity, the drawwise kernel-mass theorem including `a=0`, actual joint bound, posterior expectation identity with zero-marginal handling, Markov bound, and ambient-transfer corollary. All substantive public declarations need `#check` and `#print axioms` in a separate full-checks file. Exact package owners and declarations are to be checked against the actual Full114 archive. No compilation or native acceptance is claimed by this author offer.
