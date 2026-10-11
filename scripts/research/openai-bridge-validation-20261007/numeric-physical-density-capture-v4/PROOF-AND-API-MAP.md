# Proof and API map: selected physical density with row validity (v4)

## Profiles and conclusion

The source preserves the v3 captured source and the complete v2 declaration bodies. It retains `selected_ordered_carriers_nonempty` and `selected_physical_density`, and exports `selected_physical_density_with_rows`. Its public statement is unchanged from v3: from the same fixed source instance and fixed global tables under the original strict physical-score premise, it returns one representative choice `s`, proves row-respect for the exact selected canonical table on every presented leaf, and retains the complete uniform-`TaggedGoodU` mass bound at threshold `8 * successMargin (badExponent m h)` for that same table. The selector output `m` remains independent of source occurrence-row count `rows`.

## Proof route

The theorem first obtains the numeric selector parameters and derives the existing geometry and slack. The original strict physical score gives the `Q+1` lower bound; the captured class-collision theorem selects one `s` with a collision loss at most `2^-J`. Rewriting the ordered sample law yields selected mass at least `16*S` for `S = successMargin (badExponent m h)`.

For that fixed witness, the proof rewrites `taggedSelectedMass` using `taggedSelectedAccepts_iff_taggedAccepts I copies C raw s` and changes the law with `orderedStarLaw_eq_taggedSampleLaw I copies hcenter hleaf`. `ordered_canonical_eq_uniformU_mean I copies hcenter hleaf C Tsel` identifies the result with the uniform-U mean of the canonical density for `Tsel = taggedSelectedDomainTable I copies raw s`. The two acceptance calls supply all explicit arguments `I copies C Tsel`; `orderedStarLaw` supplies its explicit block parameter `J`.

The high-density step is proved inline. It sets `mu` to the uniform law, `beta = 16*S`, and `delta` to the conditional canonical density. The existing pointwise bound `0 <= delta U <= 1` and nonnegative `mu.mass U` give
`mu.mass U * delta U <= mu.mass U * (beta/2 + if beta/2 <= delta U then 1 else 0)`
by splitting on the threshold. Summing over the finite `TaggedGoodU` type and simplifying with `mu.normalized` gives `mean(delta) <= beta/2 + mass({U : delta U >= beta/2})`. Since the mean is at least `beta`, linear arithmetic yields that threshold mass at least `beta/2 = 8*S`. This duplicates the body of the dependency's private `high_density_mass` proof locally; it does not call or expose that private theorem.

For each presented leaf, the proof makes the local `Tsel` abbreviation explicit with `change`, rewrites its application using `taggedSelectedDomainTable_apply`, and invokes `taggedSelectedLeafLabel_respectsRows`. The row-respecting property is therefore established for the same representative choice and table used in the density sum.

## Exact dependencies

The immutable parent is `numeric-physical-density-capture-v3`, index SHA-256 `0E583EB62D091F532968E2B4E3C4D42FB1A927851FE0564A56FF5B39A91B52D2`, with parent source SHA-256 `D12265E38E7BFF59CA80B95FBF4031C660916F24C0D7BA76B2F042B38F1CBA34`. The v4 Checks file is byte-identical to v3. Existing theorem declarations and the old v2 bodies are retained.

The added APIs are pinned to the exact Full114 input archive (`70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`):

- `ActualTaggedOrderedClassCollisionBound.tagged_sample_exists_selected_le_twoNegJ`, SHA-256 `9DE71B12E30D3464C5A2420A9845015A73723B00BB208F80D17ADDFDBB935CA4`.
- `ActualTaggedOrderedFullLawForce.orderedStarLaw_eq_taggedSampleLaw`, SHA-256 `A09A2CC8E9B4DAD48A10815890E6E42EB20ED830347AB925E759BBE4CEE91C69`.
- `ActualTaggedSelectedDecoderBridge.taggedSelectedAccepts_iff_taggedAccepts`, `taggedSelectedDomainTable_apply`, and `taggedSelectedLeafLabel_respectsRows`, SHA-256 `D428F9A1822A364C057A3209017B19916FF323F717590398A0F3CCC21898AB22`.
- `ActualTaggedFixedUDensityForce.ordered_canonical_eq_uniformU_mean` and `conditionalCanonicalDensity_nonneg_le_one`, SHA-256 `FFC1A93E4A1FAEBCA783D21DA946A6D8F4EEFBDB5C7C72150149A32F22B574CB`. The same source contains private `high_density_mass`; v4 reproduces its finite-sum argument inline instead of referencing that private declaration.

The remaining project dependency, captured numeric pins, Full114 toolchain and archive identities are carried forward in `manifest.json` and match the immutable v3 parent. No additional theorem premise is introduced.

## Claims boundary

This is an uncompiled source offer. It claims no Lean acceptance, certification, or native result. The high physical score remains a premise on the same fixed instance and fixed tables. This theorem does not establish robust many-Q amplification, a fixed-complement inverse implication for every refreshed table, a source-NO decoded contradiction, SAT-instance construction, runtime bounds, or native acceptance.
