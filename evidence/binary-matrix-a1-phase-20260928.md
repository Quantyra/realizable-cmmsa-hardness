# Canonical affine character phase for A1

`BinaryMatrixA1Phase.traceCharacter_carrier_base` proves the manuscript's character phase identity on the actual quotient/inclusion carrier, for every finite binary `V,W`, every subspace pair `A≤V`, `B≤W`, every frequency `Y:W→V`, every ambient affine base `T:V→W`, and every `N:V/A→B`:

`χ_Y(T+j_B N q_A) = χ_Y(T) χ_(q_A Y|B)(N)`.

The underlying trace equality is `tracePair_carrier`, proved by cyclic trace. It uses canonical quotient and subtype maps and includes zero-dimensional cases. The sign multiplication uses the finite binary sign-add law.

This is an exact force-bearing component of manuscript A1, together with `BinaryMatrixNestedSelectorA1.selected_nested_iff` at commit `b446147`. The full function-level composition still needs finite Fourier orthogonality/inversion on `Hom(V/A,B)` so the later filter can act after frequencies coalesce; it also needs double-quotient carrier identification. No numerical NO-soundness gap is reduced by this phase theorem alone.
