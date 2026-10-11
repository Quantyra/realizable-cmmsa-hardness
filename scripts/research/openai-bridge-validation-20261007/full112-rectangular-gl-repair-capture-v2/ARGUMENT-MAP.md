# Full112 rectangular GL repair candidate

## Status and scope

This is a source-only repair candidate for the exact `RectangularGLRowCompletion.lean` member supplied to Full111. No Lean compiler was run here. The Full111 terminal snapshot contains deterministic errors, so this offer does not claim compilation, certification, or acceptance. The public theorem statements, imports, and `RectangularGLRowCompletionChecks.lean` bytes are preserved.

## Argument-to-source map

| Declarations | Mathematical/API obligation | Source route |
| --- | --- | --- |
| `prefix_fiber_equiv_nonempty` | Transport an invertible pair in the fibre over `X` to the fibre over `Y` by right multiplication by `T`, and invert by `S`. | The two inverse laws are now reassociated at the inner products: `T * (S * V) = (T * S) * V = V` uses `hTS`; `S * (T * V) = (S * T) * V = V` uses `hST`. The first-coordinate inverse laws use the matching `T*S` and `S*T` equations. The separate paired-matrix carrier laws and prefix equations are retained. |
| `row_prefix_uniform_mean` | Equal nonempty fibres plus surjectivity give the normalized uniform-image mean. | Existing `rowPrefixMap_surjective`, `prefix_fiber_equiv`, `rowPrefixFiberEquiv`, and `RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers` remain the proof route. Redundant local `Fintype`/`Nonempty` instance declarations were removed; the file's local `Fintype.ofFinite` instance supplies the finite carriers, avoiding proof-irrelevant instance shadowing. A 400,000-heartbeat limit is scoped to this theorem because the unchanged Full111 run stopped deterministically at `whnf` at 200,000 while elaborating this declaration. |
| `transpose_of_surjective_is_injective` | Convert injectivity of the transposed matrix map into the matrix-vector form expected by `Matrix.mulVec_injective_iff`. | The hypothesis is an equality of `Matrix.toLin' M.transpose` applications. Pinned `Matrix.toLin'_apply'` is proved by `rfl`, so `change` exposes `mulVecLin`; pinned `Matrix.mulVecLin_apply` is also `rfl`, so a second `change` gives exactly `(M.transpose).mulVec x = (M.transpose).mulVec y`, the goal from applying `hmul`. This uses no simp set and no transpose/row-vector identity. |
| `column_prefix_uniform_mean` | Transfer the row-prefix marginal through the transpose equivalences on frames and inverse pairs. | Redundant local `Fintype.ofFinite` declarations were removed so `hinput`, `houtput`, the cardinality equivalence, and `row_prefix_uniform_mean` share the same synthesized finite instances. The sum and cardinality reindexings remain explicit. |

## Pinned source/API dependencies

The parent input archive is `full111-exact-real-complex-operators-repair-resource02/input-archive.tar.gz`, SHA-256 `3d04e683ff88b4a5ca389f07aa64583436eac27b31fdfc9406453021021939ef`. Exact imported project members from that archive:

| Member | SHA-256 |
| --- | --- |
| `BinaryMatrixRightOrbit.lean` | `409fd652e1f051e92688466eac57bd6b85af93866d5f5d4c9aa0152ab25286b0` |
| `RectangularFrameFiberAverage.lean` | `f1dbdbf44468d72573f2b15facffd3435a700b5aab98362e2b70f217777c9b8f` |
| `ActualFiniteBinarySurjectionCounting.lean` | `ba136fc5ca364b14f76447954f47ede670930b042f1ea8276a11675b50c76c2f` |

The Mathlib source APIs used by the transpose repair were inspected in the pinned local source snapshot. `Matrix.toLin'_apply'`, `Matrix.mulVecLin_apply`, and `Matrix.mulVec_injective_iff` are in `LinearAlgebra/Matrix/ToLin.lean`; `Matrix.row_transpose` is in `LinearAlgebra/Matrix/Defs.lean`. The manifest also pins the reviewed transpose identities and unchanged `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card` import. SHA-256 values are recorded in `OFFER-MANIFEST.json`.

## Diagnostics addressed

The exact observed Full111 `stage-4.stdout` reports the two unsolved inverse-action goals at original lines 171 and 175, an unused-simp-argument warning for the opposite inverse equation at each goal, a deterministic `whnf` timeout at original line 207 with a 200,000 heartbeat cap, the `vecMul` versus transposed `mulVec` mismatch at line 289, one failed `hinput` rewrite at line 362, and six `letI`-on-proposition style warnings at lines 218, 219, 227, 342, 343, and 344. The repaired source addresses these sites without changing theorem hypotheses, suppressing warnings, or introducing proof holes or axioms. The local heartbeat increase is bounded to the single timed-out theorem and is recorded above.

The captured diagnostics and the original input archive remain immutable. Root owns compilation and will determine whether any additional repair is needed from the next native result.
