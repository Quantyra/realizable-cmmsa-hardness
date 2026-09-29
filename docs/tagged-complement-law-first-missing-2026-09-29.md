# Tagged fixed-U complement law: first missing theorem

Status: **INCOMPLETE**. This note isolates the law identity needed between the
proved fixed-table class-collision comparison and the changed-ambient robust
8S decoder. It proves no new NO bound.

For every actual occurrence instance, copy count, eligible fixed `U`, fixed
center table `C`, and one globally predrawn selected full-domain leaf table
`T'`, `ActualTaggedMZSideDraw.sideConditionalDensity I copies U t h k C T'`
is the exact source-side draw: a uniform transverse center `K` followed by
independent uniform transverse `2h`-leaves containing that same `K`.
`conditionalCanonicalDensity_eq_side` already transfers the selected tagged
canonical density to this source law without changing either fixed table.
The representative-selection theorem in `ActualTaggedFixedUDensityForce`
charges the explicit class-collision loss before this transfer.

The first missing theorem is manuscript Lemma `complement` as an **observed
joint-law identity** for each such fixed `U`: the pushforward of `(K,L_i)`
under `(K,L_i) ↦ (K,H_U+L_i)` equals the law that draws a uniform complement
`A` of `H_U`, then a uniform `t`-space `K≤A`, then independent uniform
`2h`-spaces `L'_i≤A` containing `K`, and observes
`(K,H_U+L'_i)`. Its corollary must identify the above
`sideConditionalDensity` with the uniform-complement average of ordinary
complement star acceptance using the **same** `C,T'` and full queried domains
`H_U+L'_i`. The identity concerns the observed domains and acceptance, not
the unobserved raw leaf presentations. It must hold for arbitrary fixed
eligible `U`, `C`, and `T'`, before the random complement/center/leaves.

Existing ingredients are close but do not supply this law equality:

* `ActualTaggedConditionalDomainCollision.tagged_conditional_presentation_fiber_card`
  gives the constant `2^(J*(2h-t))` number of transverse presentations of a
  fixed full domain containing a fixed center.
* `ActualTaggedConditionalGraphCount.card_conditional_complements` gives
  the corresponding count of complements containing a fixed center.
* `ActualTaggedMZSideDraw.centerEquivSide`, `leafEquivSide`, and
  `taggedAccepts_iff_sideAccepts` identify the coordinate-side draw and its
  full-domain acceptance event.

What remains is a finite incidence/disintegration proof joining these
counts: uniform `(K,A)` incidence in either sampling order, uniform full
domain law conditional on `K`, independence of all `k` full-domain leaves,
and preservation of the fixed-table acceptance indicator. A pointwise
presentation-fibre count alone does not imply that joint product-law
identity. No theorem currently states the ordinary complement star density
or its average in the tagged module, so there is no existing target that can
be invoked by the robust decoder proof.

The numeric NO-soundness gap is unchanged. The fixed-table representative
selection and explicit class-collision charge remain valid upstream.
Even after this identity, the changed-ambient inverse/refreshing/counting
theorem at the manuscript's double-exponential `J` and its 8S application
remain separate missing steps; the visibly external MZ fixed-U contract is
restricted to the source PCP schedule and does not certify them.
