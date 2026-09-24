# Astra strategy kill test: support-stratified bad-star bound

**Verdict: GO as a next-step strategy; not yet a Lean result.**

Let `k = d - t`, `q = 2^N - 1`, `r = 2^k - 1`, and use the intended fixed-line probability `p = r / q`. Counting a support of size `s`, choosing the first `s - 1` nonzero relation entries freely, and fixing the last entry gives the proposed upper bound

`B = sum_{s=2}^m binom(m,s) q^(s-1) p^s`.

Substituting `p = r/q` and applying the binomial identity gives

`B = ((1+r)^m - 1 - m*r) / q = (2^(m*k) - 1 - m*(2^k - 1)) / (2^N - 1)`.

For natural `m`, `k`, and `E`, with the present theorem's `k >= 1`, if `N >= m*k + E + 2`, then the numerator is strictly below `2^(m*k)` and `2^N - 1 > 2^(N-1)`. Therefore

`B < 2^(m*k) / 2^(N-1) <= 2^(-E-1)`,

which is half of the target `2^(-E)`. This matches the manuscript dimension guard. Conversely, `m*k > N` rules out joint directness by dimensions: an injective sum map from an `m*k`-dimensional direct sum into an `N`-dimensional quotient cannot exist.

The calculation assumes the stated source specialization of `p` and the support/relation overcount. Its numerical/source instantiation, finite union bound, and connection to a global bad-star event are missing in Lean; this note does not close them.
