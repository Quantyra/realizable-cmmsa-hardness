# Actual numeric-NO proof slice: source map and limits

This candidate translates two concrete parts of the actual material-RHS argument. It does not certify a numeric NO theorem or provide the selector/sampler, actual-star lower signal, or complete RHS comparison.

## Exact agreement maximum

`ZoomIndex` ranges over every q?r, every `Q : Grass V q`, and every `DecodedPair Q d`, including all decoded functionals `P.g`, subject only to the exact budget equation and nonempty Zoom condition. `submoduleCode` embeds the finite set of submodules into `V ? Bool`. Every submodule carrier and every dual map is finite; `decodedPair_finite` embeds the structure into a dependent sum of its subspace and functional, while the proof field is proof-irrelevant. `actualAgreementMaximum` is a recursive max over the finite univ list, starting at zero, so the empty family has value zero. `indexed_agreement_le_max` proves every indexed value is below it. `actualAgreementMaximum_gives_hfail` handles the source's unbounded q binder by deriving q?r from q+codim=r. `actualAgreementMaximum_cast_le_of_failure` uses only the exact real failure bound, positive/equal-to-zero fallback, and cast preservation of max; it preserves the manuscript's real e0 without rounding.

Source identity: Full110 archive `input-archive.tar.gz`, SHA-256 `C1702903ECC5F939B9504371D63F0D4313E192446971EF0DD7627F6E770F3C61`.

- `ActualMaximalPairLadder.lean`, SHA-256 `D61DF4001A90D5F5CF56B756151212F2EC1DDC8E10A64D919F0E046993E3FA81`: `DecodedPair`, `Zoom`, `agreement : ... ? ?`, and exact empty/nonempty definitions.
- The source file has no Fintype instance for all decoded pairs. This candidate constructs finiteness; no imported Fintype or arbitrary selected witness is presumed.

## Total Boolean rank energy and actual weighted tail

`booleanRankEnergy_total` applies the pinned `rankProjection_finite_energy_sum` through q=d and `rankProjection_finite_reconstruction`. The equality includes all ranks 0..d and all zero-width cases. `booleanRankEnergy_total_le_one` uses the actual real Boolean indicator and its pointwise square identity.

`actualWeightedHighEnergy_le` bounds the exact two-term coefficient sum used in the material RHS over `selectedHighFinIndexSet`. Its assumptions are only `1?bdim` and the integer form `nAmbient ? d+r*bdim+3` of the manuscript's `n?d+rb+log?6`; it proves the actual B tail ?`2^(-r*bdim)` by coefficient monotonicity, nonnegative rank energies, and the total-energy identity. It does not assume a bound on B or on a weighted sum.

Source identities:

- `ActualBinaryMatrixHC46FourierA16.lean`, SHA-256 `21E062E1FE12023D981810AF3C06A9D463F25FB568B6ECF10F8B3396CD16A045`: `rankProjection_finite_energy_sum`.
- `ActualSelectedComplementSourceSizeAnalyticMoment.lean`, SHA-256 `03FB0A5DE3FD2E7E150645825165D2E30CFCE60BD34765BF7D6623E3A6D2D3D1`: `rankProjection_finite_reconstruction`, `selectedHighFinIndexSet`, and the exact material RHS coefficient definition.

The theorem is generic in the actual selected Boolean leaf and its ambient matrix dimensions; substituting `selectedF Tc fc` and `n=2J,d=c+s` is definitional. It does not prove that the selected parameter witness satisfies the ambient inequality. That same-instance selector/sampler obligation remains with the numeric scalar comparison.

## Evidence boundary

The sources in the Full110 archive are pinned input bytes. No Lean/Lake invocation was run for this candidate. The `#print axioms` Checks are requests only; the target declarations are candidate translations, not compiled or accepted theorems. Parent controls own compilation and capture.
