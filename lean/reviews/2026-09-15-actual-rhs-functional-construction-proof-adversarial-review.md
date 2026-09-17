# Actual RHS-functional construction proof-adversarial review

Date: 2026-09-15  
Repository: `C:\Users\Dan\Desktop\Projects\formal-pvnp`  
Reviewed commit: `0ae4103373c1848a8ed6980cbca63784ab3a7025`  
Disposition: **GO-WITH-NOTES**

This is a read-only top-level proof-adversarial review of the frozen `ActualRhsFunctionalConstruction` main-and-Checks increment. It covers equation-vector linear independence, existence and uniqueness of the equation-span RHS functional, the actual-source wrapper, and the finrank corollary. It does not review or certify the later coordinate-space extension, label gluing, star acceptance, randomized reduction, or headline hardness claim.

## Frozen inputs and certification binding

The inspected working tree is at the assigned commit, and the two reviewed sources match the certification pins:

- `ActualRhsFunctionalConstruction.lean`: `A38112D36CED08F6D8AD151D85D08D1140CD8A17D40EFED8DEAB6B25E3100428`.
- `ActualRhsFunctionalConstructionChecks.lean`: `59CD64CCACDE1E2F3BB286A600939187FD5C5DC93024BAB11DBB1F0E1A1DCB9B`.

The closeout record has SHA-256 `50FAE722706AF678BA7AEA26EBAFF38111FF7A83C899831D116C960CE398F5D2`. The canonical 36-row artifact manifest has SHA-256 `6DCE57B5372EEEEA857AC23C93662F5B6B64F7ABF520CCBE40BEC33C93163E3C`. Its archived independent rehash reports all 36 artifacts present with zero malformed, size-mismatched, or hash-mismatched rows, and confirms that the manifest pointer matches. The before/after source inventories are equal.

The isolated target omitted the support, span-intersection, finite-source, RHS-functional main, and Checks objects before rebuilding them sequentially with Lean `4.34.0-rc2` and `LEAN_NUM_THREADS=1`. All five exits are `0`. The resulting direct-project object hashes are:

- `ActualStarQuestionSupport.olean`: `8B4A75485327BA8836F8FDB1AB561ACD15DB816E8C7C16084C58DCEA0B9461FF`.
- `ActualStarSpanIntersection.olean`: `DECC2EAA887AC7C8C1DB4F121FC0B5A9BA03369FA191E1DE6B7CCA3FCE748DBD`.
- `ActualFinite3LinSource.olean`: `72FE7300086DFB3B13844319C75725AC16032C3413699F20810B2282C6235F48`.
- `ActualRhsFunctionalConstruction.olean`: `9A8526B28F205FD8153F9E43FB3A36DF374E6BADB4F7091C9C9721AFDA9D650F`.
- `ActualRhsFunctionalConstructionChecks.olean`: `C46CFA10CD02A6F1E32B5B8F3B0AF359C413577D17633DD2BD1D05CB389636FF`.

This is a target-fresh rebuild of the increment and its direct project dependencies against seeded, hashed transitive dependencies. It is not a from-source rebuild of Mathlib or every project module; the closeout states that boundary correctly.

## Exact statements and assumptions

`equationVectors_linearIndependent` assumes only that rows indexed by `U` have pairwise-disjoint supports and that each such support is nonempty. Its conclusion is linear independence over `ZMod 2` of the actual incidence vectors `equationVector row e` indexed by the subtype `U`.

`existsUnique_rhsFunctional` adds the global assumption that every row has support cardinality three and assumes `GoodQuestion row U`. The cardinality premise supplies nonemptiness for rows in `U`; the first component of `GoodQuestion` supplies pairwise disjointness. The second, no-cross-row component of `GoodQuestion` is not needed for this local construction. The conclusion quantifies a unique linear map on exactly `equationSpan row U`, constrained to take every generator from `U` to its supplied `rhs` value.

`actual_existsUnique_rhsFunctional` is a direct specialization using `I.support_card`; it adds no mathematical premise beyond `GoodQuestion I.support U`. The optional `equationSpan_finrank_eq_card` has the advertised equality and uses the same independence argument.

These signatures match the intended obligation. The generic theorem's `hthree` is stronger in scope than necessary because it quantifies over all `E`, although only rows in `U` need to be nonempty. This is signature conservatism, not a soundness defect, and the actual source supplies it unconditionally.

## Adversarial proof analysis

The coefficient-isolation proof is valid. For a selected row `i`, it chooses a coordinate `x` in `row i`. At `x`, the `i` term evaluates to `g i`; every distinct row term evaluates to zero because pairwise disjointness forbids `x` from belonging to that support. Evaluating the assumed zero linear combination at `x` therefore forces `g i = 0`. Subtype equality is handled correctly when converting inequality of indices in `U` to inequality in `E`.

For the functional construction, the subtype-valued generator family `v : U -> equationSpan row U` is linearly independent because composing it with the span subtype map yields the already-proved incidence-vector family. The proof identifies `Set.range v` with the coercion preimage of the defining generator set and uses `Submodule.span_span_coe_preimage` to show that this family spans the whole subtype. `Module.Basis.mk` is therefore applied to an actual basis, not merely an independent subset.

`b.constr` then assigns `rhs e` to every basis vector. The existence clause follows from `Basis.constr_basis`; the uniqueness clause applies `Basis.ext` and the same generator equations. Consequently the uniqueness is correctly limited to linear functionals on `equationSpan row U`. It does not claim uniqueness of an extension to the ambient function space or to `coordinateSpace`, where uniqueness would generally be false.

The empty-question case is sound: the equation span is zero-dimensional, and there is exactly one linear functional from it. No consistency assumption on `rhs` is required because the good-question equation vectors are independent. There is also no hidden satisfiability or source-assignment assumption.

The finrank proof rewrites the equation span as the span of the range of the same independent family and applies `finrank_span_eq_card`. Its right side is the cardinality of the subtype `U`, which simplifies to `U.card`; no injectivity or cardinality conversion is assumed separately.

## Axioms and forbidden constructs

The frozen-source scan reports no `sorry`, `admit`, `native_decide`, `span_induction`, or explicit axiom declaration. Direct inspection also found no hidden declaration or unsafe shortcut. `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all four reviewed theorems. These are standard Lean/Mathlib axioms for this development; no project-specific axiom or unproved premise was introduced.

## Fixture assessment

The Checks module prints all four signatures and axiom profiles. Its concrete `Instance 1 1` uses a nonempty one-row good question with RHS `1` and consumes the exact actual wrapper, so the principal theorem is exercised outside the empty case. A second example checks the empty-question boundary.

The nonempty fixture is still a type-level consumption check: it does not independently compute the resulting functional or exercise simultaneous isolation of two coefficients. That is weaker coverage than a two-row fixture with two prescribed RHS values. This does not reduce confidence in the universally quantified kernel-checked proof, and adding such a fixture is optional rather than a condition for accepting this increment.

## Findings, manuscript boundary, and disposition

No proof gap, signature drift, instance inconsistency, vacuity in the general statements, false uniqueness scope, hidden assumption, forbidden construct, axiom defect, or certification binding defect was found. The four theorems discharge the stated local manuscript obligation: a good question's disjoint three-coordinate incidence vectors are independent, so arbitrary row RHS data defines a unique functional on their equation span, including for the actual occurrence-allocation source.

The disposition is **GO-WITH-NOTES**. The notes are limited to scope and fixture strength: `hthree` is globally quantified though only needed on `U`, the second conjunct of `GoodQuestion` is unused here, and the one-row fixture does not independently stress a multi-row coefficient-isolation branch. None warrants weakening or revising the frozen theorems.

This increment does not provide a coordinate-space functional, an ambient extension, agreement/gluing, manuscript label transport, actual-star acceptance, stationarity, or any reduction/hardness conclusion. Its immediate consumer should combine `actual_existsUnique_rhsFunctional` with the already-certified side-condition agreement theorem, then construct the permitted coordinate-space map/extension and prove the minimal label-gluing statement. The remaining route is:

```text
constructed equation-span RHS functional
  -> specialize side-condition agreement
  -> coordinate-space extension and gluing
  -> minimal label transport
  -> actual star acceptance and stationarity
  -> reduction assembly and quantitative consumers
```

