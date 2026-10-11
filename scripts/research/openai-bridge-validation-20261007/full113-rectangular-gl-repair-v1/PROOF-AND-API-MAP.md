# Rectangular GL row-prefix completion repair v1

Status: uncompiled source repair offer for the exact Full112 failed input. This does not claim Lean acceptance, proof certification, or mathematical milestone acceptance.

## Proof route

`canonicalPrefixMap_surjective` establishes surjectivity of the first-coordinate projection. `exists_square_completion` applies the pinned same-range right-orbit theorem to any surjective rectangular matrix and the canonical prefix map, retaining explicit left and right inverse matrix equalities. Thus `rowPrefixMap_surjective` covers all finite dimensions, including zero row and zero complement widths.

For the normalized row-prefix mean, every full-row-frame point `X` is related to one fixed full-row-frame point by `prefix_fiber_equiv`, whose proof transports paired inverses using an explicit two-sided transporter. `rowPrefixFiberEquiv` identifies each actual row-prefix fiber with that paired-inverse prefix fiber. The repaired proof gives explicit types to both fiber equivalences and their composite, then applies `Fintype.card_congr` to obtain the common fiber cardinality. A local `Nonempty` instance for the full-row-frame codomain is supplied by the already constructed canonical frame. The finite-fiber pushforward theorem then yields the exact normalized mean identity.

The source retains the original public theorem statements and imports. The Checks file is copied byte-for-byte from the Full112 input. The only resource change is a bounded `maxHeartbeats 800000` scoped to `row_prefix_uniform_mean`: the captured 400000-heartbeat setting timed out, and the proof now avoids repeated implicit equivalence/cardinality elaboration through typed intermediates and a typed mean result. No global option, assumption, axiom, or warning suppression is added.

## Full112 repair map

The original docstring directly preceded `set_option ... in`, which caused Lean to parse the option command where the declaration was expected. The scoped option now precedes the docstring and nested theorem. The `row_prefix_uniform_mean` proof has typed intermediates for the selected fiber equivalence, its cardinality transport, and the final mean identity; `exact hmap` reuses the single typed helper result. This addresses the captured whnf timeout through explicit elaboration boundaries as well as a finite, theorem-local heartbeat allowance. The missing downstream declaration error for `row_prefix_uniform_mean` was a consequence of its failed declaration and has no separate mathematical repair.

## Exact source and dependency pins

The input source and unchanged Checks are from `full112-native-diagnostic-packet-v1`, whose index SHA-256 is `A0CC0804ED5ABA8F393BEAFC5F65EFE2251324CDCBE24AC80462B7CBAAE9D249`. The captured source SHA-256 is `1E117431C3D55B88A2F1BE2E18C9FAA17ABAE94BC504A0490D4DDB0D80720993`; the Checks SHA-256 is `D17BF262EB0E9ABA0110C7E6C6CD51EAFFECE4AC03D68E033C3320383E6984FB`. The captured rectangular diagnostic file SHA-256 is `40A9DFA408D6405D36AE8F31E2A1FCD8272D5C978E8C6C01F972A1F1E835EC71`.

Full112's exact input archive is SHA-256 `1686A96C43231E3E02D88468C6EE5B176D131FF96B2A1F44C3C85C3E5CE531AA`. The imported project source members from that archive are:

- `BinaryMatrixRightOrbit.lean`: 2,521 bytes, SHA-256 `409FD652E1F051E92688466EAC57BD6B85AF93866D5F5D4C9AA0152AB25286B0`.
- `RectangularFrameFiberAverage.lean`: 4,413 bytes, SHA-256 `F1DBDBF44468D72573F2B15FACFFD3435A700B5AAB98362E2B70F217777C9B8F`.
- `ActualFiniteBinarySurjectionCounting.lean`: 8,251 bytes, SHA-256 `BA136FC5CA364B14F76447954F47EDE670930B042F1EA8276A11675B50C76C2F`.

The external import `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card` was read from the Full112 captured package-source archive. The enclosing evidence archive SHA-256 is `0392E798A4234ADC4386703FDB1817217D99DFBEA7FF48D4184E614AA42FD6B2`; its `package-sources.tar.gz` member is SHA-256 `2DFA036C84860818068E8F5B64C203AE9F86A51DDB966B745B0743A988E50414`; the Mathlib source member is 4,219 bytes, SHA-256 `AC31F64E47BA76F80C1C9BAB4E58645175A13C23C9175449C41ACD22B1E44F1F`.

## Validation boundary

The source and Checks must pass UTF-8/no-BOM and glyph-integrity lexical checks. Those checks do not parse or compile Lean. No local Lean/Lake, GCP, or Git was invoked by this author. Root owns native compilation and immutable capture. The result remains an uncompiled translation offer until root diagnostics are available.
