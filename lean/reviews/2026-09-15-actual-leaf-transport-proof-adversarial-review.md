# Actual one-way leaf transport proof-adversarial review

Date: 2026-09-15  
Repository: `C:\Users\Dan\Desktop\Projects\formal-pvnp`  
Frozen source commit: `bba6dbb380fa5dde490c45fd7806ccb05aa1e8a8`  
Certification evidence commit: `419d70a629a560f0bf9a358dc433fa76aaf9fbbb`  
Certification evidence completion commit: `7e06ca3`  
Disposition: **GO-WITH-NOTES**

This is a read-only top-level proof-adversarial review of the frozen
`ActualLeafTransport` main-and-Checks increment and its target-fresh cloud
certification. The increment defines the manuscript leaf relation, proves the
dependent target-domain inclusion, constructs the one-way transported raw
label, proves target-RHS respect and compatibility, and proves the corresponding
unique-existence theorem. It does not prove identity, inverse, composition or
presentation-independence laws, finite label cardinality, repeated-address
semantics, representative sampling, stationarity, star acceptance, source
hardness, or the headline reduction.

## Frozen identity and certification

- Main source SHA-256:
  `F1548559AE3135E8F75F2E8C255B530582DDEFA2E6D58AE02FC53C02460EE3E8`.
- Checks source SHA-256:
  `D9BF5ED9B8CDCA2431584B4577C4C8BEE3011A82DC23FD819B02C22F96FBC3D9`.
- Cloud main object SHA-256:
  `1CEE9647728163F2BBC71D6AA429BEFD78AA1883BB24CDE9A307A060B6465AE2`.
- Cloud Checks object SHA-256:
  `C015F98C7F2172C704216A87A7E415AD832964FD899D3D4FFB5EB92D511C7FF2`.
- Remote artifact manifest SHA-256:
  `8A65E548F77536078D40FFBA7D61640ADD45E4A2D630BF47BFF6CEECEE6A1E3B`.
- Original local Windows-checkout artifact manifest SHA-256 at the assigned
  certification commit:
  `F6132331A74C0560C18156360AA0BBCD64EF82691A64C9F0BA702AD540F59BA3`.
- Current canonical local artifact manifest SHA-256 after the evidence-only
  completion commit:
  `0BD43BFD1113C6C8DB98230AB66061EFA1B67500BAAF33DD4C93ACC237EDF41E`.
- Current Windows-checkout certification closeout SHA-256:
  `3D96F9782112FE4E03EEEEE3BA02180532E05F7F9940A8EA68D5B6603BAA9E4E`.

I independently rehashed the current sources and obtained the assigned frozen
source hashes. The source files are byte-identical at the frozen source commit,
the assigned certification commit, the evidence completion commit, and the
current worktree. The two local manifest identities above are not competing
certification results. At `419d70a`, the committed LF blob of
`artifact-hashes.txt` hashes to
`070057230874FFC5462F33001ACA1402A4AB61FAE0EA488F30D0BDE2BA93F33A`,
while its then-canonical CRLF checkout hashes to the assigned `F613...`. The
later evidence-only commit adds the empty successful stage logs and a binary
attribute for the inventory, producing the current `0BD4...` canonical
inventory without changing either reviewed source or either cloud object.

The content-addressed transfer gate compared the bundle SHA-256 on both sides,
ran `git bundle verify`, checked out exact detached HEAD
`bba6dbb380fa5dde490c45fd7806ccb05aa1e8a8`, required a clean source checkout,
and compared both frozen source hashes before compilation. The harness then
rechecked HEAD and both source hashes initially, before and after all 18 stages,
and during finalization. The recorded 40 assertions agree.

The cloud run used Lean `4.34.0-rc2`, `LEAN_NUM_THREADS=1`, an initially empty
fresh target, and rebuilt the complete 16-module reachable project-source
closure followed by main and Checks. All 18 stage exit codes are zero. Locked
external package objects and the locked Lean toolchain were cache inputs, so
this is a fresh project-source target rather than a from-source rebuild of
Mathlib. Main took 2.04 seconds and Checks 16.30 seconds; peak RSS was about
3.48 GB.

The first postprocessing scan stopped because the English word `admit` occurs
inside a documentation comment. That diagnostic and nonzero postprocessing
exit are retained. No Lean compilation stage was repeated. The replacement
scanner removes nested block comments and line comments while preserving
strings, and its scan of main and Checks is clean for `sorry`, `admit`,
`native_decide`, and source-level `axiom`. This is an adequate comment-aware
repair rather than suppression of a proof token.

## Exact manuscript correspondence

The authoritative submission manuscript states that a leaf presentation has
domain `D = L + H_U`, and that two leaf vertices represented by `(L,U)` and
`(L',U')` are equivalent when

`L + H_U + H_U' = L' + H_U + H_U'`.

It then invokes unique side-condition-preserving label transport. With
`P.domain = P.L ⊔ P.H` and `Q.domain = Q.L ⊔ Q.H`, the Lean definition

```text
P.Rel Q := P.domain ⊔ Q.H = Q.domain ⊔ P.H
```

expands to precisely that equality, up to associativity and commutativity of
submodule supremum. Both presentations already share fixed parameters `J` and
`h`; their actual questions carry the previously certified `GoodQuestion`
conditions and actual row RHS values. No satisfiability assignment, ambient
global functional, or source YES premise is added here.

The direction is also correct. Given a source label `f` on `P.domain`, the
compiled gluing theorem constructs the unique RHS-respecting functional on
`P.domain ⊔ Q.H`. The relation rewrites this common space as
`Q.domain ⊔ P.H`, hence includes `Q.domain`. Restricting the common functional
along that inclusion produces the target label. This is the manuscript's
one-way operation from `P` to `Q`, not its inverse.

## Adversarial theorem audit

### Relation and dependent inclusion

`PresentedLeaf.rightDomain_le_common P Q hPQ` rewrites the target inclusion
using `hPQ` and closes it by `le_sup_left`. Before rewriting, the target really
is `Q.domain` and the common codomain really is `P.domain ⊔ Q.H`; after
rewriting, the goal is `Q.domain ≤ Q.domain ⊔ P.H`. No reversed inclusion or
unproved equality cast is hidden in the term.

`Rel` is propositionally symmetric by equality symmetry and is reflexive by
supremum commutativity, but this increment does not expose or prove the
equivalence laws. In particular, transitivity, identity, inverse, and coherence
must not be inferred from the present theorem. Those are legitimate next
obligations.

### Compatibility predicate

`TransportCompatible P Q hPQ f g` requires a functional `F` on the exact common
space `P.domain ⊔ Q.H` satisfying all three relevant facts:

1. restriction to `P.domain` is the supplied source label `f`;
2. every actual target equation generator receives `I.rowRhs e`; and
3. restriction to `Q.domain` through the relation-derived inclusion is `g`.

Thus compatibility is not merely equality on an arbitrary overlap or a
postulated target label. It captures the intended common-extension relation.
Its target-RHS clause plus the restriction equation implies that every
compatible `g` respects `Q`, although that general implication is not exported
as a separate theorem. The final unique-existence predicate explicitly includes
`RespectsAt Q rfl g`; this conjunct is redundant mathematically but harmless and
makes the consumer-facing statement match the label side condition.

### Construction and RHS preservation

`transportedLabel` chooses the unique common functional supplied by
`actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf`, then
restricts it to `Q.domain`. The gluing theorem consumes the actual source
presentation, target actual question, target goodness proof, source functional,
and explicit source RHS-respect proof. The construction does not assume the
desired target functional or transport conclusion.

`transportedLabel_respectsAt` reads the target-generator clause from the
chosen functional's specification. Lean's elaboration of the dependent subtype
inclusion is significant here: the compiled proof confirms that the target
equation vector embedded in the common space is the same vector obtained by
embedding it through `Q.domain`. I found no value-changing cast or mismatched
membership witness.

`transportedLabel_compatible` uses the same chosen common functional and proves
the two restriction equations plus target RHS behavior. The right restriction
is definitionally the constructed label, so `rfl` is justified. The theorem is
not deriving compatibility from a separately selected witness that might differ
from the one used to define the label.

### Uniqueness and proof-term dependence

For any compatible candidate `g`, `transportedLabel_unique` obtains its witness
`G`. The prior glued-functional theorem identifies `G` with the chosen `F`
because both restrict to `f` and satisfy every target RHS equation. Congruence
under composition with the target inclusion then identifies the two target
restrictions. The final equality direction is correct:

```text
g = G.comp inclusion = F.comp inclusion = transportedLabel ...
```

The uniqueness scope is neither too broad nor vacuous. It proves uniqueness
among labels arising as restrictions of a common extension that preserves the
target RHS. It does not claim that every arbitrary RHS-respecting functional on
`Q.domain` is the transport of `f`; such a claim would generally ignore the
source-overlap constraint. It also does not claim uniqueness of an ambient
extension beyond the displayed common supremum.

`existsUnique_compatibleTransport` combines existence, target respect, and
compatibility, then uses the stronger compatibility-only uniqueness theorem.
This proves an actual `∃!`, rather than packaging a chosen value without a
uniqueness proof.

The definition syntactically accepts proofs `hPQ` and `hf`. Because these
arguments inhabit propositions, Lean proof irrelevance makes alternative proof
witnesses propositionally equal; the unique common-functional specification
also removes mathematical choice ambiguity. Nevertheless, this increment does
not export proof-independence lemmas, identity, inverse, or composition laws.
Consumers should use the forthcoming coherence layer rather than silently rely
on definitional equality of transports built with different proof arguments.

### Axioms and proof mechanisms

Checks prints the exact signatures of `Rel`, the inclusion theorem,
`TransportCompatible`, the constructed label, its respect and compatibility
theorems, the uniqueness theorem, and the final `∃!`. Printed axiom profiles for
all proof theorems contain only `propext`, `Classical.choice`, and `Quot.sound`.
These are standard Lean/Mathlib logical dependencies and no project axiom is
introduced. `Classical.choice` is expected from the noncomputable chosen unique
functional.

The result is mathematical transport, not an executable implementation.
Nothing here proves a polynomial-time representation or algorithm for the
chosen functional. That distinction matters later for reduction/runtime claims.

## Fixture audit

The nonempty fixture uses an actual occurrence-allocation instance with two
original rows. The source question is `{Sum.inl 0}` and the target question is
`{Sum.inl 1}`; `source_target_questions_distinct` explicitly proves the two
questions unequal. Their RHS values are respectively one and zero. Each
question is separately proved good, and both presentations use the actual
equation spans. With `L = ⊥`, the relation is the commutativity of the join of
the two equation spaces. The fixture therefore exercises transport between
genuinely distinct actual questions, different source and target RHS
obligations, and a target-dependent inclusion. It invokes the exact final
`∃!` and target-respect theorems.

The fixture is intentionally low-dimensional (`h = 0`) and does not establish
that the two domain submodules are propositionally unequal, although their
question sets are. It also does not exercise nonzero `L`, nontrivial overlap, or
different presentations of the same leaf vertex. Those branches belong in the
coherence and presentation-descent fixtures; they are not assumptions missing
from the universally quantified current proof.

The empty fixture separately exercises `J = h = 0`, the empty question, zero
domain, and zero label. Its RHS predicate is vacuous, as it should be at the
empty boundary. It is not used as evidence for the nonempty theorem branch.

## Verdict and remaining boundary

**GO-WITH-NOTES.** I found no false statement, direction error, hidden
satisfiability premise, invalid dependent inclusion, circular compatibility
argument, weakened uniqueness, proof gap, forbidden proof token, nonstandard
axiom, or provenance-gate defect. The increment is force-bearing: it consumes
the actual presented-leaf/gluing result and produces the manuscript's one-way
RHS-preserving transport between related actual leaf presentations.

Acceptance notes:

1. Transport is currently stated for a raw label plus an explicit
   `RespectsAt` proof. A later wrapper must transport `LeafLabel` values and
   prove that the result is independent of the chosen presentation.
2. Identity, inverse, composition/coherence, and proof-argument independence
   are not part of this increment. They remain required before repeated-address
   semantics or representative sampling can safely consume transport.
3. The theorem gives noncomputable mathematical transport. Finite encoding,
   exact label count `2^(2h)`, enumeration, and runtime are still open.
4. The nonempty fixture has distinct actual questions and nonzero/different RHS
   data, but uses `L = ⊥`; positive-dimensional and overlapping cases are
   covered only by the general theorem signature.
5. The cloud object hashes are context-labelled certification objects. The
   recorded Windows cached objects differ bytewise and should not be advertised
   as cross-platform object reproducibility.

The immediate manuscript consumer is the identity/inverse/coherence and
presentation-descent layer for transported `LeafLabel` values. The remaining
headline path is:

```text
actual one-way raw-label transport (accepted here)
  -> identity, inverse, and composition/coherence
  -> LeafLabel packaging and presentation descent
  -> repeated-address semantics
  -> center restriction
  -> representative sampler and stationarity
  -> actual-star acceptance
  -> outer soundness and source hardness
  -> reduction assembly, runtime, and asymptotics
  -> manuscript reconciliation and release package
```

The certification receipt reports cumulative estimated GCP spend of
`$0.436993`; the builder is `TERMINATED`, has no external IP, and retains a
200 GiB persistent disk that continues to accrue storage cost. This review does
not establish star acceptance, NP-hardness, the complete manuscript theorem,
`P = NP`, or `P ≠ NP`.
