# Checks and argument map

## Claims and verification state

| Item | Result | Evidence / limit |
|---|---|---|
| Distinct label coordinates | Actual native carrier | `ExactRefresh.lean` uses `GrassmannCounting.Grass` and `ActualSourceStarLaw.LeafTable`; the latter is one dual functional per distinct d-space. |
| Fresh finite product law | Defined | Uniform law on the actual leaf-table product. |
| Full-X update | Defined and pointwise proved | `refresh_inside` and `refresh_outside`; arbitrary T0 is unchanged outside X. |
| Dual fiber cardinality 2^d | Lean candidate lemma | `dualLabel_card` uses the native Grass Fintype, basis-to-dual equivalence in the reverse direction, and `Module.card_eq_pow_finrank`; source-checked, uncompiled. |
| Full product and constrained assignment counts | Lean candidate lemmas | `fullLabelProduct_card_eq_pow`, `matchingAssignments_card_eq_product`, and `matchingAssignments_mass_product`; uncompiled. |
| Match probability p^|S| | Lean candidate lemma | `matchingAssignments_mass_eq` cancels the actual product fibers coordinatewise using `Finset.prod_div_distrib` and a product-subset identity; uncompiled. |
| Match-count powerset identity | Lean candidate lemmas | `pow_matchCount_eq_powerset_card` and `matchCount_power_eq_subset_sum`; source APIs inspected, uncompiled. |
| Exact finite moment (1+p)^M | Lean candidate theorem | `refreshMoment_eq` expands powerset indicators, swaps finite sums, uses exact match mass, and sums over subsets; uncompiled. |
| Tail exp(-pM/3) | Mathematical derivation only | Markov and pinned exponential inequalities are derived in ARGUMENT.md; no Lean tail theorem yet. No assumed concentration bound. |
| Bounded history | Carrier, uniform law, and cardinal candidate | `boundedRefreshHistory_card` gives history size `|Omega|^B`; conditional recursion and absorbing-state probability argument remain to translate. |
| Adaptive preservation and many-Q force | Mathematical argument only | One-step candidate union, padded finite history, potential growth/termination, acceptance change, and distinct-Q averaging/count are explicit. Fixed-coordinate inverse and initial-density transport are input interfaces. No Lean theorem or final decoder claimed. |
| Compilation / kernel acceptance | Not run | Explicitly excluded from this task. |
| Provider failure | Recorded | Provider request `f7f98873-a43f-4b5c-a8d3-4685ffef6078` failed; this is not evidence for or against any mathematical claim. |

## Exact source pins

- Frozen native source archive: `C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02/input-archive.tar.gz`, SHA-256 `70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`.
- `ActualSourceStarLaw.lean` defines the native ordinary table exactly as `LeafTable (d) = (L : Grass V d) → L.val →ₗ[ZMod 2] ZMod 2`. `GrassmannCounting.lean` defines `Grass V d` as actual submodules of dimension d and supplies its finite instances. The new source imports both instead of duplicating these types.
- Frozen Full114 manifest pins Mathlib to revision `e06eff5f95374108acfaf19f1ff7473aa7771df2`.
- Canonical manuscript SHA-256 `16E77E937685F55BA96CD276BBDE4E65EF36F25C25B790E946F5E3EC9CFAA449`; robust enlarged-ambient statement begins at line 754. Prior captured refresh argument SHA-256 `6C05AEBB2FCFE008EA6C7458367CDE24CA08C032A121A63AA7958589850B5DC7`; this offer does not modify it.
- Existing fixed-coordinate inverse candidate SHA-256 `BC0B039F43B5D62509118B698A8049A9AE5633A8DD2425C64F67293F206A3E3B`, uncompiled. It remains an input interface, not a theorem accepted by Lean.
- Existing side-extension capture index SHA-256 `0E840CD62649F151716F3F760923EAF85D6EBABCC07FCA5040F595485CB226D7`; this is the separate final source-witness extension interface, not a refresh premise.

## Pinned Mathlib APIs inspected

All links below are primary source at exactly revision `e06eff5f95374108acfaf19f1ff7473aa7771df2`.

- [`Mathlib/Data/Fintype/BigOperators.lean`](https://github.com/leanprover-community/mathlib4/blob/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/Data/Fintype/BigOperators.lean#L102-L121): `Finset.card_pi`, `Fintype.card_piFinset`, and `Fintype.card_pi`. Lines 147-173 also give fixed-coordinate constraint counts.
- [`Mathlib/FieldTheory/Finite/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/FieldTheory/Finite/Basic.lean#L347-L363): `Module.card_eq_pow_finrank`, the current theorem spelling.
- [`Mathlib/LinearAlgebra/Dual/Basis.lean`](https://github.com/leanprover-community/mathlib4/blob/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/LinearAlgebra/Dual/Basis.lean#L108-L123): `Module.Basis.toDualEquiv`, used to identify a finite-dimensional vector space with its dual.
- [`Mathlib/Data/Finset/Powerset.lean`](https://github.com/leanprover-community/mathlib4/blob/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/Data/Finset/Powerset.lean#L92-L95): `Finset.card_powerset`, used for the exact match-count identity.
- [`Mathlib/Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/Analysis/Complex/Exponential.lean#L584-L635): `Real.add_one_le_exp`, `Real.prod_one_add_le_exp_sum`.
- [`Mathlib/Analysis/Complex/ExponentialBounds.lean`](https://github.com/leanprover-community/mathlib4/blob/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/Analysis/Complex/ExponentialBounds.lean#L63-L78): `Real.log_two_near_10` and `Real.log_two_gt_d9`; rational arithmetic gives log 2 > 2/3. No concentration library is needed.

The candidate exact-moment theorem is `refreshMoment_eq`; it is uncompiled and must not be represented as accepted Lean evidence. The next formal boundary is the Real Markov inequality on the finite law, then strict-event and M=0 handling, then per-state candidate union/history recursion. The cited Mathlib sources provide product/powerset and exponential APIs, not the application-specific tail theorem.

## Translation map and remaining obligations

1. Instantiate V with the selected fixed coordinate ambient and d=2h. Use the actual `Grass` and `LeafTable` carriers already imported in `ExactRefresh.lean`.
2. Check the uncompiled proof candidates for `matchingAssignments_mass_eq` and `refreshMoment_eq` against Lean, when compilation becomes authorized.
3. In a successor module, define the Real finite moment and bad event; prove Markov directly from finite sums, cast exact rational mass/moment to Real, handle M=0 and the strict threshold, and derive `exp(-pM/3)` from `Real.log_two_gt_d9`.
4. Prove for every fixed pre-refresh `(T0,X)` and fixed candidate the one-step bound, then union over the full candidate universe before any adaptive inverse selection.
5. Give the finite history recursion an explicit prefix-product law or a constructive positive-good-mass path; formalize stage dependence and absorbing states. Then integrate the captured fixed-coordinate inverse and initial-density interfaces, potential termination, uniform leaf incidence marginal, and distinct-Q count.
6. Keep leaf-table agreement separate from fixed center-table agreement. No premise may assume a final decoder, source-NO, or the desired many-Q conclusion.

No premise may assume a final decoder, source-NO, or a many-Q lower bound.
