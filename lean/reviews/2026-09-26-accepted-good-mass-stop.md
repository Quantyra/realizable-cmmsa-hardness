# Stop: same-experiment accepted-good mass

Date: 2026-09-26. Outcome B. Theorem 1 and Corollary 2 are not claimed.
No replacement carrier, palette, or conditional wrapper is opened.
The deleted wrapper `selected_presented_starAccepts_rankGood` is not this
kill. The GCP receipt `gcp_actual_star_presented_starAccepts_b4da0c3`
replays that wrapper and is not a pass of the inequality below.

## Failed inequality

`Pr[accept ∧ rankGood] ≥ Pr[accept] − q` with `q < S/2`,
where `S = 2^{-E}` and `E = badExponent nRows (hBlock L nRows)`,
at `selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `2 * h`, center rank `t = leafT nRows h`,
and `r = 2`. The selector gives `256 ≤ nRows`, `bOf nRows ∣ h`, and
`h ≥ nRows + 2`, so `h ≥ bOf nRows` and `h / bOf nRows ≥ 1`.

## Sample space

The law is uniform on label triples of one fixed equal-domain star. It is
not a conditioning of a larger leaf draw. Every point is a labeling of
this star:

- one question, hence one equation span `H`
- one hub `PresentedLeaf` and two query `PresentedLeaf`s, all three with
  that same domain, so all three `LeafVertex`s are that domain and
  `LeafVertex.Rel` holds
- one center `K` of rank `t` inside the hub's transverse summand `L`, with
  `K ∩ H = ⊥`, used as the center subspace of each query
- `Ω = LeafLabel(hub) × LeafLabel(query₁) × LeafLabel(query₂)`
- each triple has mass `1 / |Ω|`

Acceptance is `starAcceptsCenter` of the hub label against the two query
labels on `K`. Rank-good requires joint increment rank `2 * (2 * h - t)`.
All three leaves determine the same quotient image, so the joint increment
has rank at most `2 * h - t`. And `2 * h - t = leafK nRows h = 2 * (h / bOf nRows) ≥ 2`,
so `2 * h - t < 2 * (2 * h - t)`. Rank-good contains no point of `Ω`.
Thus `Pr[accept ∧ rankGood] = 0`.

## Probability on this law

A `LeafLabel` matches the row right-hand side on `H`. The domain is
`L ⊔ H` and `L ∩ H = ⊥`, so gluing is a bijection
`LeafLabel ≃ (L →ₗ[ZMod 2] ZMod 2)` and `|LeafLabel| = 2^{2h}`.

`K ≤ L` has rank `t`, so restriction `(L →ₗ ZMod 2) → (K →ₗ ZMod 2)` is
surjective and every fiber has size `2^{2h - t}`. For any fixed hub label,
each query matches it on `K` with probability `2^{-t}`. The two queries
are independent coordinates of `Ω`, so

`Pr[accept] = 2^{-2t} = 2^{-4 (h - h / bOf nRows)}`.

This is the probability of the uniform law on `Ω`. It is not
`Pr[equal domain]` times a conditional probability of a larger draw.

## Exponent

`agreementExponent_lt_badExponent` proves that `256 ≤ nRows`,
`bOf nRows ∣ h`, and `0 < h / bOf nRows` give

`4 * (h - h / bOf nRows) < badExponent nRows h + 1`.

The selector supplies those hypotheses. Therefore

`Pr[accept] > 2^{-(E + 1)} = S/2`.

Every `q < S/2` leaves `Pr[accept] - q > 0 = Pr[accept ∧ rankGood]`.
The inequality fails on this law.

Stop.
