# Submodule-functional gluing non-claims review

**Verdict: GO-WITH-NOTES.** Commit `52324cc3f6f307332c5ceca07668eb8c18e379c1` proves and target-fresh certifies the exact generic statement that two fixed linear maps on submodules `A` and `B`, when equal on `A ⊓ B`, have a unique common linear map on `A ⊔ B`. This is a reusable algebraic bridge. It does not itself construct or identify the manuscript's actual leaf domain, labels, label transport, actual star carrier, star acceptance predicate, randomized reduction, hardness result, or any P-versus-NP conclusion.

## Frozen scope and independent checks

| Artifact | SHA-256 | Review result |
|---|---|---|
| `SubmoduleFunctionalGluing.lean` | `3AFDACA24136FB81140471BD7CB40398CE61A2D1896DD78973E25041D51E7D73` | Matches the frozen source and commit. |
| `SubmoduleFunctionalGluingChecks.lean` | `E41183DB2B49F958C7CA0FA753AB58721AD63D7ACAFA1DDD2715DB54CAE4DA52` | Matches the frozen Checks source and commit. |
| `artifact-hashes.txt` | `E63C8B32DE354264FA8A9AD3A8CAD5CBCE12E80C20ACB875B0E7D7BB395C88C0` | Matches `artifact-hashes-manifest.sha256`. |

I independently rehashed all 26 rows in `artifact-hashes.txt`: every listed file was present and every recorded size and SHA-256 matched. The source-before and source-after hashes agree. The final main and Checks exit codes are both `0`; their stderr logs are empty. The target objects did not preexist in the isolated output root. The emitted object hashes are `77D109A27663844EB3D553C7F23FBB4C064A34AFE9B0F977A5156B14DCC415E7` for the main module and `D40CF30A445FF7DFC18F927BAF4FED5657A8D5EBE8CE723AA7CE64F0D9D7518E` for Checks.

The certification is accurately described as a target-fresh compilation against 2,816 immutable seeded dependency files, with the target main and Checks objects excluded. The module imports only Mathlib modules and has no direct project dependency. This is not a full rebuild of Mathlib or every dependency from source. That limitation is disclosed in `README.md`, `provenance.txt`, and `closeout.md` and does not invalidate the certified local increment.

The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and explicit `axiom` declarations. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. The use of `Classical.choice` is consistent with choosing a decomposition of each element of `A ⊔ B`; the theorem introduces no custom axiom.

## Exact claim that is justified

For a field `K`, `K`-modules `V` and `W`, submodules `A B : Submodule K V`, and fixed linear maps `f : A →ₗ[K] W` and `g : B →ₗ[K] W`, the premise

```lean
∀ z : ↥(A ⊓ B), f ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩
```

implies existence and uniqueness of a linear map on `A ⊔ B` whose restrictions along the two canonical inclusions are exactly `f` and `g`. The uniqueness is uniqueness of the glued map on the sum for those fixed inputs. It is not uniqueness of `f`, `g`, a label, an ambient extension outside `A ⊔ B`, or a computational representation.

The proof chooses a decomposition `z = a + b`, defines the candidate value as `f a + g b`, uses agreement on the intersection to show independence from the chosen decomposition, and proves the two restriction equalities and uniqueness. The theorem assumes the compatibility condition; it does not derive compatibility for a manuscript instance.

## Fixture assessment

The principal fixture takes both domains to be the whole nonzero space `ℚ × ℚ`, and both maps to be the first-coordinate functional. Their intersection is therefore the whole space, so the compatibility premise controls every vector. A separate fixture exhibits `(1, 0)` in that intersection with functional value `1`, preventing the test from being merely a zero-map or zero-domain example. The final fixture checks the valid trivial-sum branch with two bottom submodules.

These fixtures exercise a nonzero common domain and the zero branch, and they invoke the exact exported theorem. They do not test two distinct partially overlapping submodules. That is acceptable for this generic theorem's certification, but no manuscript-specific intersection, equation span, coordinate space, or actual-source object appears in the source or Checks.

## Claims boundary

This increment may be described as:

- a kernel-checked generic submodule-functional gluing theorem;
- the algebraic mechanism that can consume a separately proved intersection-agreement premise;
- a candidate reusable bridge for later manuscript-specific label construction.

It may not be described as establishing any of the following:

- the actual leaf domain or label type;
- existence, uniqueness, consistency, or transport of manuscript labels;
- instantiation of `A`, `B`, `f`, or `g` by actual coordinate-space and equation-span data;
- actual star construction or acceptance;
- sampling, stationarity, rejection bounds, or source-to-star coupling;
- a randomized reduction, polynomial-time realization, source or target hardness;
- the manuscript headline theorem, publication readiness, novelty, or `P = NP` / `P != NP`.

The evidence closeout observes this boundary: it says the certification covers only the exact generic theorem and fixtures and explicitly excludes manuscript integration, actual-source instantiation, label transport, star acceptance, and the headline reduction. I found no overclaim in the source, Checks, or closeout evidence.

## Remaining consumer obligation

The next consumer must instantiate the two submodules and maps with the manuscript's actual objects, discharge agreement on their certified intersection, define the resulting label object, and prove the restriction equations needed by the subsequent transport or star-acceptance theorem. Until that wrapper compiles and is certified, this result remains a generic algebraic dependency rather than completion of the label-transport branch.

