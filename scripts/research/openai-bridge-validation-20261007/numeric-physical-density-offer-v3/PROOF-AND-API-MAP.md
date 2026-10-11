# Proof and API map: selected physical density with row validity

## Profiles

The v3 source preserves the complete captured v2 source and Checks requests. It adds the public theorem `ActualNumericPhysicalDensity.selected_physical_density_with_rows`, with the same instance, selector, sampler, padding, fixed center/raw table arguments and original strict physical-score premise as `selected_physical_density`.

The new conclusion returns a single `TaggedRepresentativeChoice s`, universal row-respect for the corresponding `taggedSelectedDomainTable I copies raw s` on every `TaggedPresentedLeaf`, and the unchanged uniform-`TaggedGoodU` mass sum at threshold `8 * successMargin (badExponent m h)` for that very table. It does not assume row-respect as an input.

## Proof route

1. Reuse the captured private selected-parameter, geometry and slack lemmas. The same exact selector output `m` supplies `m >= 256`, the Hnum height floor, divisibility and the physical density geometry/slack.
2. Convert the original strict score premise `(1/2)^Q < physicalMass` to `alpha=(1/2)^(Q+1) <= physicalMass`. Apply `ActualTaggedOrderedClassCollisionBound.tagged_sample_exists_selected_le_twoNegJ` to choose one representative witness `s` with `physicalMass <= taggedSelectedMass(s) + 2^(-J)`. Rewrite the physical law by `ActualTaggedOrderedFullLawForce.orderedStarLaw_eq_taggedSampleLaw`. The recorded slack `2^(-J)+16*S<=alpha` gives selected mass at least `16*S`.
3. For this same witness, rewrite selected acceptance sample-by-sample with `ActualTaggedSelectedDecoderBridge.taggedSelectedAccepts_iff_taggedAccepts`. The ordered-law equality and `ActualTaggedFixedUDensityForce.ordered_canonical_eq_uniformU_mean` identify the selected mass with the uniform-U mean of `conditionalCanonicalDensity` for `T_s=taggedSelectedDomainTable I copies raw s`.
4. The existing `[0,1]` finite-average lemma `high_density_mass` turns mean at least `16*S` into eligible-U mass at least `8*S`; its output is the complete unconditioned uniform-law sum for that exact `T_s`.
5. For each presented leaf `P`, `taggedSelectedDomainTable_apply` rewrites `T_s(P.domain)` to `taggedSelectedLeafLabel I copies raw s P`. Then `taggedSelectedLeafLabel_respectsRows` proves `P.respectsRows` for that value. The same `s` appears in both the density sum and all row-validity proofs.

`TaggedLeafTable` alone has no row-validity predicate. The new theorem exposes the selected representative witness needed by this downstream property. It keeps the selected star count independent of the `Instance N rows` source-row count.

## Exact dependencies

The parent is immutable `numeric-physical-density-capture-v2` (index `6D95E2F441AB49926E359E8C444245915B738DAAB77FB1C2ABBBB1469B50C087`, source `3C5855E51A55A760AB0FB4745690D60B1985212CE79816FF86622933651B2380`). Its original declaration bodies and Checks requests are retained; v3 only adds three direct imports/opens and the new theorem/check requests.

New Full114 project dependencies, all verified against the exact `input-archive.tar.gz` member bytes:

- `ActualTaggedOrderedClassCollisionBound.tagged_sample_exists_selected_le_twoNegJ`, source SHA-256 `9DE71B12E30D3464C5A2420A9845015A73723B00BB208F80D17ADDFDBB935CA4`.
- `ActualTaggedOrderedFullLawForce.orderedStarLaw_eq_taggedSampleLaw`, source SHA-256 `A09A2CC8E9B4DAD48A10815890E6E42EB20ED830347AB925E759BBE4CEE91C69`.
- `ActualTaggedSelectedDecoderBridge.taggedSelectedAccepts_iff_taggedAccepts`, `taggedSelectedDomainTable_apply`, and `taggedSelectedLeafLabel_respectsRows`, source SHA-256 `D428F9A1822A364C057A3209017B19916FF323F717590398A0F3CCC21898AB22`.

The density identity and `[0,1]` averaging lemma are in `ActualTaggedFixedUDensityForce` (Full114 source SHA-256 `FFC1A93E4A1FAEBCA783D21DA946A6D8F4EEFBDB5C7C72150149A32F22B574CB`). Full dependency identities, captured numeric pins and archive pins are enumerated in `manifest.json`.

## Claims boundary

This is an uncompiled source offer. It exports a valid selected canonical table without strengthening the physical-score premise. It does not prove robust refresh/many-Q amplification, an inverse implication for each refreshed table on a fixed complement, a decoded source-NO contradiction, SAT-instance construction, runtime bounds, or native acceptance. The existing v2 theorem remains unchanged. No conditioned or reweighted law replaces the unconditioned ordered law.
