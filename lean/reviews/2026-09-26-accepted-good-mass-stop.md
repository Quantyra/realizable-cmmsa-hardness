# Accepted-good-mass kill withdrawn

Date: 2026-09-26. The failure claim in the earlier text of this note is
withdrawn. Theorem 1 and Corollary 2 are not claimed. No replacement
carrier, palette, or conditional wrapper is opened. The inequality is
not proved.

## Inequality under test

`Pr[accept ∧ rankGood] ≥ Pr[accept] − q` with `q < S/2`,
where `S = 2^{-E}` and `E = badExponent nRows (hBlock L nRows)`,
at `selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `2 * h`, center rank `t = leafT nRows h`,
and `r = 2`. The selector gives `256 ≤ nRows`, `bOf nRows ∣ h`, and
`h ≥ nRows + 2`.

The joint source law draws the center from `centerLaw`, then independent
physical transverse rank-`2h` leaves of that center, then labels.
Acceptance is `starAcceptsCenter` of one shared source label against those
leaves. Rank-good is joint directness of those same leaves.

## Why the earlier kill does not go through

Same-question `LeafVertex.Rel` holds only for equal domains, so acceptance
implies equal domains, and a rank-good pair has distinct quotient images.
The events are disjoint, so the inequality reduces to `Pr[accept] < S/2`.

`2^{-4 (h - h / bOf nRows)}` is the agreement probability only on the
uniform law over label triples of one fixed equal-domain star.
`agreementExponent_lt_badExponent` shows that quantity is strictly above
`S/2`. That space is not the joint source law.

On the joint source law the two leaves are independent uniform extensions
of the drawn center. Acceptance still requires those extensions to
determine the same domain. For leaves taken in one complement of the
equation span, distinct extensions determine distinct domains, so

`Pr[accept] ≤ Pr[equal domain] = 1 / gaussian(2 * J - t, 2 * h - t)`,

where `J = blocks A h = 2 ^ (2 ^ (A * h ^ 2))` and
`2 * h - t = leafK nRows h ≥ 2`. That Gaussian count is larger than
`2^{E + 1}` at these parameters, so `Pr[accept]` can sit strictly below
`S/2`. A `q` between `Pr[accept]` and `S/2` then repairs the inequality.
Disjointness does not kill it.

This note does not claim the inequality fails, and it does not claim a
proof. The deleted wrapper `selected_presented_starAccepts_rankGood` is
not a proof. The GCP receipt `gcp_actual_star_presented_starAccepts_b4da0c3`
replays that wrapper only.
