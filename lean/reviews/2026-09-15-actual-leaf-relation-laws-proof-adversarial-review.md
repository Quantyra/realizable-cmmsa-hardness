# Actual leaf relation laws proof-adversarial review

Date: 2026-09-15  
Repository: `C:\Users\Dan\Desktop\Projects\formal-pvnp`  
Frozen source commit: `e77fda3102152ca111daf3464af4a45931178f81`  
Certification evidence commit: `6da7f1ce41535cceea462bd4c756dbf08f84034d`  
Disposition: **GO-WITH-NOTES**

This is a read-only top-level proof-adversarial review of the frozen
`ActualLeafRelationLaws` main-and-Checks increment. It audits the private-coordinate
lemma, the three-question span bridge, its actual-source specialization, reflexive,
symmetric, and transitive leaf relation laws, canonical transport identity and
inverse, proof-argument independence, dependent subtype casts, fixtures, axiom
profiles, forbidden-source scan, and target-fresh certification. It does not establish
transport composition, presentation descent for packaged `LeafLabel` values,
repeated-address semantics, center restriction, representative sampling,
stationarity, star acceptance, outer soundness, source hardness, or the headline
reduction.

## Frozen identity and certification

- Main source SHA-256:
  `87BE216E92B19AD2044BF5DB1551A3D36BE3993ABBD456FDCF16FA379274610C`.
- Checks source SHA-256:
  `EBCFCE831F66382614D9D0EF9FBD30D566E0B019BC9C955F943FD61658C90626`.
- Cloud main object SHA-256:
  `2AD7B111371F0523DD0AC037F519919A4224F5317EDCE980CF380A6D214C3F13`.
- Cloud Checks object SHA-256:
  `EDB86FCD8906B7296900346248C2CA564C5DC27CEB937293AC38C9B48C2A0357`.
- Canonical 130-row artifact manifest SHA-256:
  `7D7F000045660B422CEF18FCCA2A427B3D2421D7D17659782C172D113E51CBDB`.
- Certification closeout SHA-256:
  `DAA257807E67660F4851FCBCDDED4AE4648F7F3F5A97707FE89AEDC0B606B27F`.

I independently rehashed the current main source, Checks source, and artifact
inventory; all three equal the assigned hashes. The certification source assertions
bind detached HEAD `e77fda3102152ca111daf3464af4a45931178f81` and both frozen source hashes before
and after every build stage. All 19 stages exited zero. The fresh target rebuilt the
complete 17-module reachable project-source closure, then main and Checks, under Lean
`4.34.0-rc2` with `LEAN_NUM_THREADS=1`. Main used 2.28 seconds and Checks 11.78
seconds; the recorded run maximum was about 3.45 GB RSS. Locked external package
objects and the locked Lean toolchain were retained inputs, so this is a target-fresh
project-source certification rather than a rebuild of Mathlib from source.

There is one provenance-record defect. The committed `transfer-gate.log` is stale:
it records the preceding `bba6dbb...` one-way transport bundle and its old source
hashes, rather than this increment's `e77fda3...` gate. The committed `gate.sh`, local
bundle verification, transfer receipt, source assertions, and compile harness all name
the correct relation-laws commit and hashes. Most significantly, the compile harness
itself aborts before any stage unless the remote checkout is clean, HEAD is exactly
`e77fda3...`, and both source hashes match; it repeats those checks around every
stage. Thus the kernel build is bound to the frozen source, but the closeout should not
claim that the raw committed log independently demonstrates the relation-laws bundle
SHA comparison. Future certification runs must use an increment-scoped gate-log path,
delete any pre-existing log, and assert that its expected commit and hashes occur
before compilation. This evidence defect does not change the checked theorem objects,
but it is a required closeout repair for strict archive-transfer traceability.

## Exact theorem and assumption audit

`row_private_outside_two_questions` assumes a three-element row, pairwise row
intersection at most one, and three `GoodQuestion` predicates. For a row in the
middle question but absent from both endpoint questions, it finds a coordinate in
that row outside both endpoint supports and outside every other middle row. The proof
uses at most one endpoint-support coordinate from each endpoint, so their union
occupies at most two of the row's three coordinates. Middle-question disjointness
then excludes all other middle rows. No global satisfiability, RHS premise, source
assignment, or generic lattice law is introduced.

`equationSpan_inf_sup_coordinateSpace_le` proves

```text
equationSpan U2 ⊓ (coordinateSpace U1 ⊔ coordinateSpace U3)
  ≤ equationSpan U1 ⊔ equationSpan U3.
```

It expands a vector in the middle equation span as a finite linear combination.
For each middle-only row, the private coordinate isolates that row's coefficient;
membership in the endpoint coordinate-space sum makes the vector zero at that
coordinate, forcing the coefficient to zero. The remaining coefficient support is
contained in `U2 ∩ (U1 ∪ U3)`, whose equation vectors lie in the endpoint span
sum. This is a coefficient argument over the actual equation-vector representation,
not an inference from distributivity of the submodule lattice. I tried to falsify it
by allowing one coordinate to be shared with each endpoint and by making those two
coordinates distinct. The third coordinate remains private exactly because row size
is three; the proof correctly handles the tight case. Dropping row size three,
linearity, or middle-question disjointness would invalidate the route, and all three
are explicit premises.

`actual_equationSpan_inf_sup_coordinateSpace_le` supplies those two incidence
premises from `I.support_card` and `I.pair_intersection`. It retains all three actual
`GoodQuestion` arguments. It does not replace the generic theorem with an unproved
actual-source assertion.

## Relation transitivity and attempted falsification

The relation is

```text
P.Rel Q := P.domain ⊔ Q.H = Q.domain ⊔ P.H.
```

Reflexivity is definitional after commutation of identical terms, and symmetry is
equality symmetry. Transitivity is the high-risk result. Given `x ∈ P.domain`, the
first relation writes `x = q + p` with `q ∈ Q.domain` and `p ∈ P.H`; the second
writes `q = r + k` with `r ∈ R.domain` and `k ∈ Q.H`. Since both `x` and `p`
lie in `coordinateSpace P.U`, `q` does too. Since `r` lies in
`coordinateSpace R.U`, the correction `k = q - r` lies in the sum of the two endpoint
coordinate spaces. The actual three-question bridge therefore puts

```text
k ∈ P.H ⊔ R.H.
```

Regrouping then gives `x ∈ R.domain ⊔ P.H`. Repeating the argument with the
endpoints reversed supplies the opposite inclusion and hence the relation equality.
Every use of an equation space as part of a domain is justified by `H_le_domain`.

This proof does not assume that arbitrary submodule joins distribute over
intersections. The only nontrivial intersection-to-sum step is the explicit
coefficient theorem above, specialized to the actual incidence structure. The
subtraction/addition rewrites are valid over the ambient `ZMod 2` vector space (and
in fact the abelian-group rearrangement itself does not rely on characteristic two).
The orientations of both relation rewrites and both final supremum inclusions are
correct. I found no counterexample satisfying the displayed assumptions.

## Identity, inverse, casts, and proof irrelevance

`transportCompatible_refl` uses the already-certified unique glued functional on
`P.domain ⊔ P.H`. Because `P.H ≤ P.domain`, both the source and target restrictions
are the same map on `P.domain`. The local equality of `Submodule.inclusion` maps is
proved extensionally; it changes only membership witnesses and not vector values.
`transportedLabel_identity_canonical` then applies transport uniqueness in the
correct equality direction.

`transportCompatible_symm` starts from a witness on `P.domain ⊔ Q.H` and restricts
it along the relation equality to `Q.domain ⊔ P.H`. Its new left restriction is the
old target label, its RHS clause for `P.U` follows from the old source restriction and
the explicit `RespectsAt P` premise, and its new right restriction is the old source
label. The subtype conversions retain the same underlying equation vectors. No
inverse functional or ambient extension is assumed.

`transportedLabel_inverse_canonical` applies transport uniqueness to this reversed
compatibility witness, so transport to `Q` and back to `P` returns the original raw
label. This is a two-step inverse law, not yet the three-object composition/coherence
law required by later consumers.

`transportedLabel_proof_irrel` uses `congr` to eliminate alternative proofs of the
same relation and `RespectsAt` propositions. Those arguments are proof terms in
`Prop`; Lean proof irrelevance makes the resulting dependent inclusions equal. It
does not claim independence from different presentations, domains, questions, or
labels. I found no value-changing cast concealed by this proof.

## Fixtures, axioms, and forbidden mechanisms

The nonempty fixture uses three distinct singleton questions from an actual
occurrence-allocation instance. It proves their question sets pairwise distinct and
invokes the exact transitivity theorem across all three, then exercises canonical
identity and inverse transport with an actual RHS-respecting label. This is a genuine
nonempty type-level consumer. Its `L` submodules are all bottom, however, so each
relation equality reduces to commutativity of equation-span joins. The fixture does
not behaviorally force the private-coordinate correction used in the general
transitivity proof, nor does it cover positive-dimensional `L`. The general theorem
is still kernel-checked at full quantification, but a later composition/coherence
fixture should use nonzero or unequal `L` data if constructible without adding
assumptions.

The empty fixture separately covers `J = h = 0`, zero domain, reflexivity,
transitivity, and identity transport. Its RHS condition is correctly vacuous and is
not used as evidence for the nonempty branch.

The nested-comment-aware source scan is clean for `sorry`, `admit`, `native_decide`,
and explicit source-level `axiom`. Printed axiom profiles for all eleven reviewed
theorems contain only `propext`, `Classical.choice`, and `Quot.sound`. No project axiom
or unsafe proof mechanism appears. The maps are noncomputable mathematical objects;
these laws do not supply an executable polynomial-time transport implementation.

## Disposition and remaining boundary

**GO-WITH-NOTES.** The mathematical increment passes adversarial review. I found no
false transitivity inference, hidden generic-lattice distributivity, omitted incidence
assumption, circular transport premise, reversed identity or inverse equality,
value-changing subtype cast, theorem weakening, forbidden proof token, or nonstandard
axiom. It is force-bearing: the actual incidence bridge converts the manuscript leaf
relation from a one-way transport condition into an equivalence relation and proves
canonical identity and inverse laws for transported raw labels.

Acceptance notes:

1. Repair the certification evidence policy before the next closeout so an
   increment-scoped raw transfer log proves the current bundle SHA and cannot inherit
   the preceding increment's output. The current kernel build remains bound to exact
   HEAD and source hashes by the compile harness.
2. Composition/coherence across three presentations is not proved here. Relation
   transitivity alone does not show that direct transport equals two-step transport.
3. The laws concern `RawLeafLabel` plus explicit `RespectsAt` evidence. Packaged
   `LeafLabel` presentation descent and independence from presentation witnesses are
   still open.
4. The nonempty fixture has three distinct actual questions but `L = ⊥`, so it does
   not execute a nontrivial middle correction or positive-dimensional transverse
   component.
5. No finite encoding, enumeration, exact label cardinality, effective sampler, or
   runtime theorem follows from these noncomputable constructions.

The immediate manuscript consumer is direct-versus-composed transport coherence,
followed by presentation descent and repeated-address semantics. The remaining
headline path is:

```text
actual relation equivalence plus identity/inverse (accepted here)
  -> direct/two-step transport composition and coherence
  -> packaged LeafLabel presentation descent
  -> repeated-address semantics
  -> center restriction
  -> representative sampler and stationarity
  -> actual-star acceptance
  -> outer soundness and source hardness
  -> reduction assembly, runtime, and asymptotics
  -> manuscript reconciliation and release package
```

The certification receipt reports cumulative estimated GCP spend of
`$0.514970682121`; the builder is `TERMINATED`, has no external IP, and retains a
200 GiB persistent disk that continues to accrue storage cost. This review does not
establish star acceptance, NP-hardness, the complete manuscript theorem, `P = NP`, or
`P ≠ NP`.
