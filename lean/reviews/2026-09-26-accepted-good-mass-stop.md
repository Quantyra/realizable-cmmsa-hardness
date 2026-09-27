# Stop: same-experiment accepted-good mass

Date: 2026-09-26. Outcome B. Theorem 1 and Corollary 2 are not claimed.
No replacement carrier, palette, or conditional wrapper is opened.
`selected_presented_starAccepts_rankGood` is deleted. It divided `starLaw`
by a label-fibre card, and its acceptance compared one leaf with itself.
The GCP receipt `gcp_actual_star_presented_starAccepts_b4da0c3` replays that
deleted wrapper. It is not a pass of the inequality below.

## Failed inequality

`Pr[accept ∧ rankGood] ≥ Pr[accept] − q` with `q < S/2`,
where `S = 2^{-E}` and `E = badExponent nRows (hBlock L nRows)`,
at `selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `2 * h`, center rank `leafT nRows h`,
and `r = 2`. The selector gives `256 ≤ nRows`, so `2 ≤ nRows`,
`bOf nRows ∣ h`, and `h ≥ bOf nRows`.

Acceptance is `starAcceptsCenter` of one shared source `LeafLabel` against
the queried rank-`2h` `PresentedLeaf`s of that same question. Rank-good is
joint directness of those leaves: the two quotient increments span
`2 * (2 * h - leafT nRows h)`.

## Kill

`bOf m = 4000 * m^2` and `leafT m h = 2 * (h - h / bOf m)`.
`badExponent m h = 2 * m * (h - 1000 * (h / bOf m))`.

For one question set, `LeafVertex.Rel` of two presented leaves holds only
when their domains are equal: both equation spans are the equation span of
that question, and that span sits inside each domain, so
`domain ⊔ H = domain`. A rank-good pair has two different images in the
quotient by that span, so the domains differ. The events are disjoint.
The inequality then requires `Pr[accept] < S/2`.

The draws on which `starAcceptsCenter` is not already false are the
equal-domain draws. A center of rank `t = leafT nRows h` has `2^t`
restrictions. Independent agreement of the source with both query labels
has probability `2^{-2t} = 2^{-4 (h - h / bOf nRows)}` when those
restrictions are uniform. For `256 ≤ nRows` and `q = h / bOf nRows`,

`4 (h - q) < 2 * nRows * (h - 1000 * q) = E < E + 1`,

because `E - 4(h - q) = h (2 nRows - 4) - h / (2 nRows) + h / (1000 nRows^2)`
and `2 nRows - 4 ≥ 508`. Thus `2^{-4(h-q)} > 2^{-(E+1)} = S/2`.
Agreement on that locus is strictly heavier than `S/2`, and the rank-good
event does not meet it. No `q < S/2` repairs the inequality.

Stop.
