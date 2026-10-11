# Full113 exact complex append repair: argument and API map

This offer is a static successor to the exact Full112 `ExactComplexAppendContinuation.lean` input. It preserves imports, public declaration statements, assumptions, and the complete Checks file. It repairs only the six source diagnostics from the Full112 stage-4 packet: two mean-reduction goals, the norm-square rewrite target, the implicit rank index, and three unused simp arguments in two simp lists.

## Proof changes

- `complexAppendAverage_re` and `complexAppendAverage_im`: after `complexFiniteMean_re` / `_im`, unfold the remaining `uniformMean` on the real append-average side and close by reflexivity. The exact project definition is `uniformMean f = (sum M, f M) / (Fintype.card ... : Real)` in `BinaryMatrixFourier.lean`; `appendAverage` is exactly this mean over appended B matrices in `ActualFixedFunctionalAppendOperator.lean`. Thus both sides have the same finite sum and denominator, including a zero-cardinality denominator case.
- `uniformMean_normSq_components`: make the beta-reduced goal explicit with `change Complex.normSq (F M) = ...` before using `Complex.normSq_apply`. This aligns the subterm with the pinned Mathlib theorem.
- `complexAppend_rankProjection_energy_eq_product`: specify `(i := i)` when instantiating `complexRankProjection_energy_components`; the function F does not determine the projection rank parameter.
- `complexPhi_rankProjection_eigen`: remove `mul_zero` from the real component simp set and `mul_zero` plus `zero_add` from the imaginary component simp set, exactly the entries reported unused. No linter option or warning suppression was introduced.

## Pinned source identities

The exact Full112 input archive is `C:/Users/dfred/.quantyra/builder02/full112-exact-real-complex-operators-repair2-resource02/input-archive.tar.gz`, SHA-256 `1686A96C43231E3E02D88468C6EE5B176D131FF96B2A1F44C3C85C3E5CE531AA`. Its project members are pinned in `OFFER-MANIFEST.json`.

The Full112 native evidence archive is `C:/Users/dfred/.quantyra/builder02/full112-exact-real-complex-operators-repair2-resource02/checks/20261011T051347974720Z/cmmsa_a8_output_20261011T051406Z_3ef6ddc2_evidence.tar.gz`, SHA-256 `0392E798A4234ADC4386703FDB1817217D99DFBEA7FF48D4184E614AA42FD6B2`; its embedded `package-sources.tar.gz` member is 28,053,685 bytes, SHA-256 `2DFA036C84860818068E8F5B64C203AE9F86A51DDB966B745B0743A988E50414`. The pinned `Mathlib/Basic/Complex/Basic.lean` member is SHA-256 `744EB1D57D32044612AB388AA45E69FAE15C87F84BB966C909D2C5CF55D03115`, where `Complex.normSq_apply` states `normSq z = z.re * z.re + z.im * z.im`.

## Scope and status

The unchanged Checks file retains all original `#check` and `#print axioms` requests. No Lean/Lake command was run for this offer. The edits are a translation repair candidate, not native verification or acceptance. No other Full112 source, prior offer, or captured input was edited.