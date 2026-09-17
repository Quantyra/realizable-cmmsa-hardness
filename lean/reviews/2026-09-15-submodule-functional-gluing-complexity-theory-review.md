# Submodule functional gluing: complexity-theory review

Date: 2026-09-15  
Review role: top-level read-only complexity-theory lens for the S3138 actual-star algebraic bridge  
Verdict: **GO-WITH-NOTES**

## Decision

The frozen increment proves the expected universal property of a submodule sum. Given linear maps `f : A -> W` and `g : B -> W` that agree on `A inf B`, there is exactly one linear map on `A sup B` whose restrictions to `A` and `B` are `f` and `g`. The agreement premise is the force-bearing compatibility condition: decompositions of an element of `A sup B` into an `A` part and a `B` part need not be unique, and agreement on the intersection is exactly what makes the glued value independent of that choice.

This is relevant to the manuscript because the already certified actual-source work supplies compatible functionals on a coordinate space for one question and an equation span for another. The theorem can glue those maps on the corresponding submodule sum once an actual wrapper instantiates its domains and overlap premise. It therefore supplies only the generic algebraic mechanism needed by the next bridge. It does not itself mention the actual source, instantiate `coordinateSpace` or `equationSpan`, define the manuscript leaf space `L + H_U`, construct or transport a label, or prove any star or reduction statement.

No finite encoding, algorithm, sampler, probability law, running-time theorem, PCP value statement, or complexity-class object occurs in the signature. The source is explicitly noncomputable and its construction selects decompositions using classical choice. Uniqueness of the resulting mathematical map does not provide an algorithm for computing it.

## Frozen artifacts and evidence

The reviewed Lean commit is `52324cc3f6f307332c5ceca07668eb8c18e379c1` (`prove unique submodule functional gluing`). `git diff --exit-code` confirms that both reviewed source files match that commit.

| Artifact | Independently observed SHA-256 | Assessment |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/SubmoduleFunctionalGluing.lean` | `3AFDACA24136FB81140471BD7CB40398CE61A2D1896DD78973E25041D51E7D73` | Matches the frozen main source. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/SubmoduleFunctionalGluingChecks.lean` | `E41183DB2B49F958C7CA0FA753AB58721AD63D7ACAFA1DDD2715DB54CAE4DA52` | Matches the frozen Checks source. |
| `research/evidence/2026-09-15-submodule-functional-gluing-fresh-run/artifact-hashes.txt` | `E63C8B32DE354264FA8A9AD3A8CAD5CBCE12E80C20ACB875B0E7D7BB395C88C0` | Independently rehashed evidence manifest; all 26 recorded rows match. |
| `research/evidence/2026-09-15-submodule-functional-gluing-fresh-run/closeout.md` | `D5BF6AD54858DFA30913897D5587D0EBC978E55C8447E760C8F380007B60E815` | Certification receipt reviewed. |
| `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness/paper/submission-manuscript.md` | `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240` | Manuscript dependency assessed, especially the star construction and joint-span gluing passages. |

The target-fresh certification compiled the frozen main and Checks modules sequentially with Lean `4.34.0-rc2` and `LEAN_NUM_THREADS=1`. Neither target object existed before compilation. Both stages exited zero, emitted no warnings or errors, and left the source hashes unchanged. The main and Checks object hashes are `77D109A27663844EB3D553C7F23FBB4C064A34AFE9B0F977A5156B14DCC415E7` and `D40CF30A445FF7DFC18F927BAF4FED5657A8D5EBE8CE723AA7CE64F0D9D7518E`.

This was a target-fresh build against immutable seeded Mathlib and transitive dependency objects. The module has no direct project dependency, so this certification does not rebuild the actual-source modules or the repository from source. The forbidden scan is clean for `sorry`, `admit`, `native_decide`, and explicit source-level axiom declarations. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim and assumption audit

`existsUnique_glue_on_sup` assumes a field `K`, modules `V` and `W`, submodules `A B : Submodule K V`, linear maps on those submodules, and pointwise agreement on `A inf B`. The field assumption is sufficient for the intended `ZMod 2` application. The result gives one and only one linear map

```text
F : (A sup B) -> W
```

whose composites with the canonical inclusions equal `f` and `g`.

The proof first chooses one decomposition `z = a + b` for every `z` in the sum. It proves that `f a + g b` is independent of the chosen decomposition: the difference between two left parts lies in both `A` and `B`, so the overlap hypothesis equates the corresponding difference values. It then proves additivity and scalar compatibility by comparing the selected decomposition with the natural sum or scalar multiple of selected parts. Finally, any competing extension is forced on every `z` because its value is the sum of its values on the included `A` and `B` parts.

The theorem does not assume that `A` and `B` form a direct sum, and it does not claim uniqueness of an `A + B` decomposition. Its uniqueness conclusion is only uniqueness of the linear extension after `f`, `g`, and their overlap agreement have been fixed. It does not assert existence or uniqueness of those input functionals.

The Checks module exercises a nontrivial overlap by taking both submodules to be the whole space `Q x Q` and both maps to be first-coordinate projection. A separate witness confirms that the common domain contains a vector with first-coordinate value one, so this fixture is not vacuous. The zero-submodule example covers the trivial-sum branch. These are suitable generic fixtures, but neither is an actual-source or distinct-domain instantiation.

## Manuscript dependency

The manuscript's imported star contract treats leaf labels as linear functions on `L + H_U` satisfying prescribed RHS values on `H_U`, and it later uses joint-span gluing of leaf and center labels. The certified route now has the following shape:

```text
actual good-question equation spans and coordinate spaces
  -> unique RHS functional on each selected equation span                 [closed]
  -> compatible coordinate-space/equation-span functionals on overlap    [closed]
  -> unique linear functional on an abstract submodule sum                [closed here]
  -> instantiate gluing on the exact actual-source sum domains            [open]
  -> define manuscript leaf domains L + H_U and label objects              [open]
  -> prove transport, inverse/descent, and representative independence     [open]
  -> construct the actual star carrier and honest acceptance               [open]
  -> prove clique-resampling stationarity and completeness                 [open]
  -> supply soundness, formula compilation, and randomized reduction       [open]
  -> prove fixed-L hardness and the learning corollary                      [open]
```

The immediate consumer should specialize `A` and `B` to the already certified actual-source domains, feed the certified intersection agreement to `hagree`, and expose an exact theorem whose codomain and restriction equalities match the forthcoming label definition. That specialization should be checked before treating this as manuscript label gluing.

The generic theorem does not replace the imported MZ transport contract. The manuscript additionally requires transverse subspaces `L`, equation spans `H_U`, leaf-equivalence classes, unique side-condition-preserving transport, restriction to a center space `K`, and representative resampling. None of those objects occurs in this module.

## Complexity and claims boundary

1. **No leaf realization.** The theorem glues two supplied maps on arbitrary submodules. It does not construct `L`, identify `H_U`, define `L + H_U`, show that a leaf label exists, count labels, or prove the alphabet size `2^(2h)`.

2. **No transport.** There is no equivalence relation on leaf vertices, map between equivalent presentations, inverse law, functoriality, representative independence, or descent to equivalence classes. A unique map on one submodule sum is not yet unique side-condition-preserving label transport.

3. **No source or label algorithm.** Classical existence and uniqueness do not give a computable representation or polynomial-time construction. The theorem has no finite or encoded input types, no `FP` witness, and no size or running-time bound.

4. **No star acceptance or probability statement.** The module has no center, leaf tuple, star constraint, acceptance predicate, sampler, clique-resampling kernel, stationary marginal, coupling, or source-failure bound.

5. **No hardness consequence.** It proves no soundness, value gap, HN formula compilation, CMMSA promise, randomized many-one reduction, source-hardness map, fixed-`L` asymptotics, NP-hardness, learning lower bound, `P = NP`, or `P != NP`.

The defensible claim is:

> Lean verifies that two linear maps on submodules which agree on their intersection have a unique common linear extension to the submodule sum.

Do not promote this to actual manuscript leaf gluing until the source-specific wrapper is compiled, or to label transport, star acceptance, stationarity, efficient construction, PCP soundness, reduction assembly, hardness, novelty, publication readiness, or a P-versus-NP conclusion.

## Disposition

**GO-WITH-NOTES.** Accept the frozen theorem as the canonical generic submodule-gluing mechanism. It is mathematically correct and directly relevant to the next actual-source bridge. The next risk-first obligation is an exact actual-source specialization that consumes the certified compatible RHS functionals on the intended sum domain. Leaf-space realization, label transport, star construction, acceptance, resampling, soundness, and every complexity conclusion remain open.
