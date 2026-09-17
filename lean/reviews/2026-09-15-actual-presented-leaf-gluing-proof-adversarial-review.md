# Actual presented-leaf gluing proof-adversarial review

Date: 2026-09-15  
Repository: `C:\Users\Dan\Desktop\Projects\formal-pvnp`  
Frozen source commit: `e599567a629f6e4eb960b4b2543960095293d1d3`  
Cloud certification commit: `6422609d04c6632035892431b7c77af0b6db7b08`  
Disposition: **GO-WITH-NOTES**

This is a read-only top-level proof-adversarial review of the frozen
`ActualPresentedLeafGluing` main-and-Checks increment. The reviewed increment
defines actual-source presented leaves and labels, proves same-domain
equation-span equality and RHS presentation descent, and constructs the unique
RHS-respecting functional on `D ⊔ H_{U'}`. It does not prove leaf transport,
identity/inverse/coherence, presentation descent for a transported equivalence,
representative sampling, stationarity, star acceptance, source hardness, or a
headline reduction.

## Frozen identity and certification

- Main source SHA-256:
  `D19126D4962A13AF182462F56548FE74252100108D5BC1C9EF1C51EAEEBD1452`.
- Checks source SHA-256:
  `E76DB5B1AF64E31131E785CAB057F194DF3428CE67E159693C61EE3B4AB0564E`.
- Cloud main object SHA-256:
  `3AE5AB5229E44A73D0AB545987E93E028E5F0C522DF88149ED10983F51E82C4B`.
- Cloud Checks object SHA-256:
  `A6F2D6F0D0B023265916D4BD7F58DDE23D9A35F1A1A34208D65BE96538D31165`.
- Canonical `artifact-hashes.txt` SHA-256:
  `3EADD48379297AAD61EF5ADF24D73498770D1529A32969D008FE6D742E502BED`.
- Certification closeout SHA-256:
  `2EF5C4A96813E6B7EAFA82F2AD7A3C138FE30F05D5420C2C399EDA8AF06C51CD`.

The certification commit is a descendant of the frozen source commit, and the
current copies of both reviewed sources are byte-identical to the frozen
commit. I independently rehashed the canonical manifest and closeout; their
hashes match the assigned values. The evidence records 139 canonical artifact
rows with zero rehash mismatches.

The precompile transfer gate checked the complete-history bundle hash on both
sides, ran `git bundle verify`, checked out the exact detached source commit,
required a clean checkout, and checked both frozen source hashes. The harness
then asserted the exact HEAD and both source hashes initially and before and
after every stage, producing 36 matching assertions. This is a sound provenance
gate for the increment. It does not independently hash every imported source
between stages, but the clean detached checkout at the verified commit binds
those imports, and no evidence of dependency mutation was found.

The cloud run rebuilt the complete 15-module reachable project-source closure,
then main and Checks, into a fresh Linux target. All 17 stages exited `0` under
Lean `4.34.0-rc2` with `LEAN_NUM_THREADS=1`. Locked external package objects and
the locked toolchain were retained cache inputs, so this is not a from-source
rebuild of Mathlib or every external package. The receipt states that boundary
accurately.

Every cloud project object differs bytewise from the current local cached
object. The local and cloud targets also differ by operating system and build
context, so cross-context object-byte equality is not a logical certification
invariant. Exact frozen sources, pinned package revisions, the locked Lean
identity, successful fresh elaboration, recorded cloud object hashes, and the
independently rehashed evidence provide the relevant binding. The mismatch must
not be presented as reproducible object-byte identity.

## Manuscript correspondence and exact assumptions

The authoritative manuscript states that a leaf domain is `L + H_U`, where
`U` has `J` disjoint three-variable equations with the no-cross-equation-pair
property, `H_U` is their equation-vector span, `dim L = 2h`, and
`L ∩ H_U = {0}`. A label is a linear functional on that domain satisfying the
row right-hand sides on `H_U`.

`PresentedLeaf` represents exactly that local data for the actual occurrence
allocation:

- `U` is an actual-source row set with `GoodQuestion I.support U`;
- `card_U : U.card = J`;
- `L` lies in `coordinateSpace I.support U`;
- `finrank_L : finrank L = 2 * h`;
- `transverse : L ⊓ equationSpan I.support U = ⊥`;
- `H` is definitionally `equationSpan I.support U`; and
- `domain` is definitionally `L ⊔ H`.

`GoodQuestion` contains both pairwise disjointness and the manuscript's
no-cross-equation-pair condition. The actual source supplies support cardinality
three and pairwise row intersection at most one through prior compiled lemmas.
No satisfiability assignment, global RHS functional, or source YES premise is
added. `L_le` is the formal version of viewing `L` inside the `3J` coordinate
space of `U`, not an extra unrelated hypothesis.

`RawLeafLabel I D` is a linear functional `D →ₗ[ZMod 2] ZMod 2`.
`RespectsAt P hD f` imposes the actual RHS equation on every selected generator.
`LeafVertex` retains a domain together with existence of a valid presentation,
and `LeafLabel` retains a raw functional together with existence of a
presentation at which it respects the RHS. This matches the current manuscript
leaf-label object extensionally, subject to the missing finite-cardinality and
transport results noted below.

## Adversarial proof audit

### Same-domain equation-span equality

`H_eq_of_domain_eq P Q` proves `P.H = Q.H` from equality of the two represented
domains. For `x ∈ P.H`, domain equality puts `x` in `Q.domain`; the latter lies
in `coordinateSpace Q.U`. The certified span-intersection formula then reduces

`equationSpan P.U ⊓ coordinateSpace Q.U`

to the span of `P.U ∩ Q.U`, which is contained in `Q.H`. The reverse inclusion
is symmetric. This argument uses the actual-source incidence properties and
both good-question hypotheses; it does not infer equality merely from equal
dimensions or from transversality. Empty and overlapping questions are covered
by the same proof.

I found no counterexample within the signature. The conclusion would be false
for arbitrary row systems without the certified span-intersection property,
but the theorem is intentionally specialized to
`ActualOccurrenceAllocation.Instance`, whose support lemmas discharge it.

### RHS presentation descent and dependent casts

`respectsAt_iff_of_domain_eq` says that a fixed functional on a fixed domain
respects one valid presentation exactly when it respects another. The forward
proof extends the domain functional to the ambient vector space, restricts it
to `coordinateSpace P.U`, and invokes the certified compatible-RHS-functional
theorem for `P.U` and `Q.U`. Same-domain `H` equality ensures each `Q` equation
vector can be regarded in `P`'s coordinate space. Agreement on the certified
intersection transfers the ambient extension's value to the unique RHS
functional for `Q.U`.

The casts through `hP`, `hQ`, and `hD` affect only subtype membership proofs.
The underlying vectors remain the same `equationVector`, and the proof compares
their values after ambient inclusion. No proof-irrelevance assumption beyond
Lean's ordinary proposition treatment is used to identify different vectors.

This descent does not silently assume that the full source is satisfiable.
Only the selected good questions are involved. Their equations are internally
independent, and the span-intersection theorem shows that compatibility between
two questions is forced precisely on their common equation span. Actual row RHS
values agree there because common generators are the same actual rows.

### Unique gluing on `D ⊔ H_{U'}`

`actual_existsUnique_gluedLeafRhsFunctional` accepts a presented leaf `P`, any
actual good question `U'`, a raw label `f` on `P.domain`, and the explicit
premise that `f` respects `P`. It returns exactly one linear functional on

`P.domain ⊔ equationSpan I.support U'`

whose restriction to `P.domain` equals `f` and whose value on every selected
`U'` equation vector is the actual row RHS.

Existence is sound. An ambient extension of `f` supplies a coordinate-space
functional for `P.U`; the compatible-RHS theorem constructs the unique
RHS-functional `g` on `H_{U'}` and proves its agreement with that extension on
the relevant span/coordinate intersection. Since `P.domain` lies in the old
coordinate space, this gives agreement of `f` and `g` on
`P.domain ⊓ H_{U'}`. The generic supremum gluing theorem then supplies a map
on the exact sum.

Uniqueness has the correct scope. Any competitor's restriction to `H_{U'}`
satisfies the RHS on all generating equation vectors, so
`actual_existsUnique_rhsFunctional` identifies that restriction with `g`.
The generic gluing uniqueness theorem then identifies the full competitor.
The result does not claim uniqueness of an ambient extension, uniqueness of
`L`, or uniqueness of a presentation. It proves precisely the uniqueness of
the functional on the displayed supremum.

The local variable `hgunique` is obtained but unused; this is harmless because
the proof later uses the underlying RHS-functional uniqueness directly. There
is no weakened conclusion or hidden additional premise.

## Fixtures, axioms, and attempted falsification

The nonempty fixture uses an actual `Instance 1 1` with RHS equal to `1`, a
singleton good question, and the exact presented-leaf and label definitions.
It constructs a genuine RHS-respecting label and invokes the exact glued
functional theorem. Thus the label and RHS claims are not vacuous or hidden
behind a zero RHS.

The fixture's `L` is zero (`h = 0`) and it glues the same singleton question
already present in the domain. Consequently it does not regression-test a
positive-dimensional `L`, a distinct `U'`, a proper enlargement of the domain,
or a nontrivial overlap. The universally quantified proof covers those cases,
but a later transport increment should include a fixture with distinct
questions and actual enlargement; this would expose future cast or direction
errors more effectively. The empty fixture correctly verifies the degenerate
zero-domain branch. The two final reflexive examples consume same-domain and
descent theorems but do not test distinct presentations.

The source scan is clean for `sorry`, `admit`, `native_decide`, and explicit
source-level `axiom`. The three printed theorem profiles contain only
`propext`, `Classical.choice`, and `Quot.sound`. `Classical.choice` is expected
from linear-map extension and generic gluing. These results establish
mathematical existence; they do not by themselves supply executable or
polynomial-time label construction.

## Disposition and remaining boundary

**GO-WITH-NOTES.** No proof gap, unsound cast, hidden satisfiability premise,
false uniqueness claim, quantifier weakening, forbidden proof mechanism, or
cloud provenance defect was found. The increment is integrated and
force-bearing: it formalizes the actual manuscript domain `D = L ⊔ H_U`,
makes label validity independent of presentation, and supplies the unique
RHS-respecting extension to `D ⊔ H_{U'}` needed by transport.

The acceptance notes are:

1. The fixtures do not exercise a proper domain enlargement or two distinct
   presentations; add that coverage in the next transport/coherence consumer.
2. The manuscript's claim that there are exactly `2^(2h)` labels is not proved
   here. It needs the direct-sum/restriction equivalence and finite-cardinality
   argument.
3. The existential presentation in `LeafLabel` is now propositionally sound,
   but no canonical chosen presentation or computable representation is
   supplied.
4. Object-byte hashes differ across local and cloud contexts and must remain
   context-labelled. The cloud objects are the canonical certification objects
   for this frozen run.
5. The stopped 200 GiB persistent disk continues to accrue storage cost even
   while the VM is terminated; this is operational rather than mathematical.

The immediate manuscript consumer is the leaf-equivalence and one-way
transport theorem. The remaining headline path is:

```text
presented leaf and unique glued RHS functional (accepted here)
  -> leaf equivalence and one-way transport
  -> transport identity, inverse, and coherence
  -> transport presentation descent and repeated-address semantics
  -> center restriction
  -> representative sampler and stationarity
  -> actual-star acceptance
  -> outer soundness and source hardness
  -> reduction assembly, runtime, and asymptotics
  -> manuscript reconciliation and release package
```

The cloud receipt reports cumulative estimated GCP spend of `$0.340771`; the
builder state is `TERMINATED` with no external IP. This proof review makes no
claim that the manuscript theorem, NP-hardness, `P = NP`, or `P ≠ NP` has been
proved.
