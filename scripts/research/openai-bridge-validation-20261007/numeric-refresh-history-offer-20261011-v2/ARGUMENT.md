# Actual refresh history: numeric tail and stopping boundary

Status: uncompiled source candidate, disjoint successor to the captured actual-candidate v1. This offer does not claim kernel acceptance or completion of E002/S3137.

`ActualRefreshHistory.lean` imports the actual table tail and the full finite candidate type from `ActualRefreshCandidates`. Its `candidate_tail_uniform` theorem translates the strict actual product-law tail into the manuscript's common `exp(-2^E/12)` tail, conditional on the precise large-intersection inequality for every member of the full candidate carrier. `actual_union_bound_of_card` then applies the already-fixed-before-refresh finite union and explicit candidate-cardinality bound. `actual_positive_mass_refresh` extracts a positive-mass fresh table from a strict bound below one, with no assumption of a favorable table and no dependence on a later inverse output.

The definitions `actualPreservingHistory` and `actualPreservingHistory_protects_every_candidate` instantiate the previously generic finite-choice recursion with the actual candidate-failure sets. The transition may depend on each selected table, and the theorem protects every candidate at each prior state. Its statewise lower-intersection and cardinality estimates are uniform premises; no inverse result is assumed. The theorem `active_steps_cannot_fill_horizon` proves the deterministic endpoint: if every active step grows accumulated mass by more than `epsilon·2^(-rn)/8`, a horizon with total guaranteed growth above one cannot remain fully active while its mass stays at most one. It is an existence-path statement. It does not imply the separate random-history failure event bound `B_n F_n`.

## Exact mathematical interfaces still needed

The source deliberately leaves two concrete manuscript estimates as premises in the theorem inputs:

1. For every admissible `(a,Q,P)` with large actual intersection, show `2^-d |X∩Zoom(Q,P)| ≥ 2^E/4`, where `E=(2h-r)(n-r-2h)+2-4h`, using the actual Gaussian zoom count and the ambient lower bound on `|X|`.
2. Prove `Fintype.card (Candidate V d r) ≤ 16(r+1)^2·2^(n(r+1))` from the actual decoded-pair carrier, dimension split `a+c≤r`, Gaussian upper counts, and `2^(n-c)` functionals on each W.

The captured exact Gaussian-ratio source supplies the proof route: use `gaussian_ratio_eq` at `m=b`, `gaussian_self b`, and `normalizedFrame_mono` for the exact lower; use the normalized-frame split at the last factor for the upper `4·2^(b(N-b))`. The actual Zoom-to-Gaussian cardinality bridge and the finite dependent-subtype cardinality calculation are not yet encoded here. Once these are proved, the captured robust-real cutoff gives `F_n<1` uniformly at every state, and this source's positive-mass refresh theorem can be iterated over the actual state.

## Remaining full research obligations

The abstract growth endpoint still needs to be connected to the actual fixed-coordinate inverse output, the refreshed table on all of X, and the original table preserved outside X. Then prove that the chosen table avoids every candidate event at each adaptively reached state, and that each inverse step enlarges X by the whole zoom while adding more than `epsilon·2^(-rn)/8` original-table agreement. The original many-Q conclusion additionally requires distinct-Q deduplication, the Gaussian force-count estimate, averaging over the unconditioned complement law, source decoding, and certification. The existence construction does not establish the separate random-path `B_nF_n` estimate.

## Validation boundary

Static source review only. No Lean, lake, or transitive compilation was invoked locally. Sol remains the sole native compiler and Git custodian. All predecessor capture hashes remain unchanged; this is a new disjoint offer.