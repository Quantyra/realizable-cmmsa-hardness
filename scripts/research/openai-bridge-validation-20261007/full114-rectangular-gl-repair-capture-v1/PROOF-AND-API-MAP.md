# Rectangular GL row-prefix repair v2

Status: uncompiled source offer for the exact failed Full113 input. This is a bounded elaboration repair; it claims no Lean acceptance or certification.

## Repair

The Full113 source timed out while elaborating the single `row_prefix_uniform_mean` proof at 800,000 heartbeats. I factored the expensive equal-fibre argument into two private declarations. `rowPrefix_fiber_equiv` composes the explicit row-prefix fiber identification, the same-range paired-inverse transporter, and the inverse row-prefix fiber identification. `rowPrefix_fiber_card_eq` then applies `Fintype.card_congr` to that named equivalence. The main theorem now uses the card lemma, with explicit type for the row-prefix map, rather than elaborating the nested subtype equivalences and their cardinal transport inside its local proof. This creates separate elaboration boundaries instead of raising the monolithic heartbeat cap.

The only heartbeat setting is a local, finite 400,000 cap on `row_prefix_uniform_mean`. Full113 used a local 800,000 cap and still timed out. The source keeps the canonical-frame nonemptiness witness as an ordinary local `let` and supplies it as the explicit argument to the generic pushforward theorem. This removes the `letI` style warning without changing the finite-carrier argument. The original public declaration headers and imports are unchanged. The Checks file is byte-identical to the Full113 input.

## Proof and API route

`canonicalPrefixMap_surjective` proves the first-coordinate projection onto the c-row prefix is onto. `exists_square_completion` applies `same_range_matrix_right_orbit` to the matrix and canonical prefix matrix; the resulting square matrix and two-sided inverse stay explicit. `rowPrefixMap_surjective` therefore covers zero row-width and zero complement-width cases.

For any two full-row frames X and Y, `prefix_fiber_equiv` transports the inverse-pair prefix fibers using the explicit two-sided matrix transporter. `rowPrefixFiberEquiv` identifies each actual map fiber with its corresponding prefix fiber. The new private `rowPrefix_fiber_equiv` composes these equivalences, and `rowPrefix_fiber_card_eq` derives equality of the finite fiber cardinalities. The canonical prefix frame X₀ proves the codomain nonempty; surjectivity supplies a nonempty fiber, hence its cardinal k is positive. The existing `RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers` then yields exact equality of normalized finite means. Its finite-carrier and nonempty arguments are passed explicitly at the call site.

The full-column identity remains the transpose of the row identity through `rowColumnFrameEquiv` and `inversePairTranspose`. `gl_column_prefix_uniform_mean` transports the explicit inverse-pair result to Mathlib's finite GL carrier through `inversePairEquivGL`. This leaves every prior mathematical statement and zero-dimension case intact.

## Exact input and dependency pins

The failed Full113 native custody archive has SHA-256 `60ED6FF40DAE28268D1C52EF5ECD78B354BA3E8FE347E5AFF14986C53BE36213`; it contains two independently matching native copies. The exact source and Checks inputs are copied from `full113-native-diagnostic-packet-v1`, index SHA-256 `DA68B27E6FC25D36F261862AFAE2057D9FDEB4C4BCFD725706D3CF21EFD26CF4`. Input source `RectangularGLRowCompletion.lean` SHA-256 `FD0E815F4A816C82EFA77CD0334E40BDC7AF28A7C1E23937CF6CCDA90A8BA1FD` (17,838 bytes); unchanged Checks SHA-256 `D17BF262EB0E9ABA0110C7E6C6CD51EAFFECE4AC03D68E033C3320383E6984FB` (1,822 bytes). Exact diagnostic packet: timeout at original line 224, maxHeartbeats 800000; dependent unknown declaration at line 365; one style warning at original line 250 recommending an ordinary `let` over `letI`.

The Full113 input archive is `ROOT113`'s exact `input-archive.tar.gz`, SHA-256 `BE67B48A7D6AA2745A1D28B99953E29B5764686EECFE4EDCFA01908872DE7EC2`. Imported project members:

- `BinaryMatrixRightOrbit.lean`, 2,521 bytes, SHA-256 `409FD652E1F051E92688466EAC57BD6B85AF93866D5F5D4C9AA0152AB25286B0`.
- `RectangularFrameFiberAverage.lean`, 4,413 bytes, SHA-256 `F1DBDBF44468D72573F2B15FACFFD3435A700B5AAB98362E2B70F217777C9B8F`.
- `ActualFiniteBinarySurjectionCounting.lean`, 8,251 bytes, SHA-256 `BA136FC5CA364B14F76447954F47EDE670930B042F1EA8276A11675B50C76C2F`.

The external imported declaration `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card` was inspected from the pinned Full112 package-source capture referenced by the prior GL source map: package-source archive SHA-256 `2DFA036C84860818068E8F5B64C203AE9F86A51DDB966B745B0743A988E50414`; member source 4,219 bytes, SHA-256 `AC31F64E47BA76F80C1C9BAB4E58645175A13C23C9175449C41ACD22B1E44F1F`. Full113's input manifest names the same import. This records the exact inspected API body; the parent must still confirm that its selected Full113 package environment matches the pin.

## Validation boundary

The source and Checks must pass UTF-8/no-BOM and glyph-integrity lexical checks. No Lean/Lake, GCP, or Git operation was performed here. The candidate source has not been parsed or compiled. Root owns native compilation and immutable capture; the Full113 failure remains preserved.
## v2 static correction

The v1 static review identified that owPrefix_fiber_equiv returns an Equiv in Type; it is therefore a private noncomputable definition, not a theorem. V2 changes only that declaration kind. The v1 four-file offer is preserved unchanged in the captured static-rejection record (index 933D8CD90B09EE955C3C424FD6E6BDC1B1B517D69A1C1576B3F8B12D41B5779C). The codomain nonemptiness witness is an ordinary local let, passed explicitly to the generic averaging theorem, matching the source-owned linter recommendation; no haveI instance is introduced.
