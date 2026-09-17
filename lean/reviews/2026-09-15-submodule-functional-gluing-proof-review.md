# Submodule-functional gluing proof-adversarial review

## Verdict

**GO-WITH-NOTES** for the exact generic theorem at commit
`52324cc3f6f307332c5ceca07668eb8c18e379c1` and its target-fresh
main-and-Checks certification. The result may be consumed as a gluing lemma.
It does not yet instantiate the manuscript's coordinate/equation-span maps or
discharge any actual-source, label-transport, star-acceptance, or headline
reduction obligation.

## Frozen artifact and evidence identity

- Main source SHA-256:
  `3AFDACA24136FB81140471BD7CB40398CE61A2D1896DD78973E25041D51E7D73`.
- Checks source SHA-256:
  `E41183DB2B49F958C7CA0FA753AB58721AD63D7ACAFA1DDD2715DB54CAE4DA52`.
- Main object SHA-256:
  `77D109A27663844EB3D553C7F23FBB4C064A34AFE9B0F977A5156B14DCC415E7`.
- Checks object SHA-256:
  `D40CF30A445FF7DFC18F927BAF4FED5657A8D5EBE8CE723AA7CE64F0D9D7518E`.
- Canonical `artifact-hashes.txt` SHA-256:
  `E63C8B32DE354264FA8A9AD3A8CAD5CBCE12E80C20ACB875B0E7D7BB395C88C0`.
- Certification closeout SHA-256:
  `D5BF6AD54858DFA30913897D5587D0EBC978E55C8447E760C8F380007B60E815`.

I independently rehashed all 26 rows in the artifact manifest: all named
artifacts exist and all recorded lengths and SHA-256 values match. The working
copies of both Lean sources equal the committed versions, and their hashes
match the certification freeze.

## Proof audit

The theorem has the expected universal-property statement: linear maps
`f : A -> W` and `g : B -> W` that agree on `A inf B` admit exactly one linear
map from `A sup B` restricting to `f` and `g`.

The use of `Classical.choose` is logically safe. For each `z` in `A sup B`,
`Submodule.mem_sup'` supplies an arbitrary decomposition `z = a + b`. The
local lemma `eval_of_decomp` compares the chosen decomposition with any other
one. It proves `leftPart z - a = b - rightPart z`, verifies that this common
vector belongs to both `A` and `B`, applies `hagree` on the resulting
intersection element, and uses linearity to conclude
`f (leftPart z) + g (rightPart z) = f a + g b`. Thus the value assigned to
`z` does not depend on which witnesses `Classical.choose` selected.

The addition and scalar laws use `eval_of_decomp` with the sums and scalar
multiples of the chosen parts. The supplied equality witnesses follow from
the original decomposition equations, so both laws are proved for the
choice-defined function rather than assumed.

The restriction proofs instantiate `eval_of_decomp` with `(a, 0)` and
`(0, b)`, respectively. The uniqueness proof decomposes every `z`, rewrites a
competitor through linearity, and uses both restriction identities pointwise.
This covers existence, both restriction equations, and uniqueness without a
gap.

`[Field K]` is sufficient for every operation used and matches the intended
`ZMod 2` consumer. The proof could likely be generalized to a commutative
ring/module setting, but that is an optional strengthening and not a defect in
the frozen statement. No finite-dimensional, complement, direct-sum, or
trivial-intersection assumption is hidden in the construction.

## Fixtures and certification

The Checks module invokes the theorem on a nonzero full-overlap example over
`Q`, separately exhibits a nonzero vector in that overlap, and exercises the
zero-sum branch. These fixtures rule out a purely vacuous agreement premise
and cover the degenerate domain. They do not provide a proper-submodule
fixture with nonunique decompositions; the general Lean proof itself handles
that branch through `eval_of_decomp`. Adding such a fixture would improve
regression diagnostics but is not required for acceptance.

The isolated target contained neither target object before compilation. Main
and Checks both exited `0`, sources remained stable, and the forbidden scan is
clean for `sorry`, `admit`, `native_decide`, and explicit `axiom`
declarations. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`. The evidence is a target-fresh build against immutable seeded
transitive dependencies, not a full dependency source rebuild; the closeout
states that boundary accurately.

## Claims boundary and notes

1. Accept this theorem only as the generic compatible-functional gluing
   mechanism on a submodule supremum.
2. The `Classical.choice` dependency is expected from the arbitrary
   decomposition construction and is exposed by the axiom profile.
3. The theorem proves no existence of the input maps and no agreement premise;
   those remain obligations of the actual manuscript instantiation.
4. This review does not certify label gluing, actual-star acceptance,
   stationarity, source hardness, randomized-reduction assembly, runtime, or
   any P-versus-NP conclusion.

