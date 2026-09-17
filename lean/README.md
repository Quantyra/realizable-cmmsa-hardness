# Paper-specific Lean sources (certified subset)

This directory is the Lake `srcDir` for the realizable-CMMSA manuscript companion. Sources were copied from `formal-pvnp` commit `e8eb955ebfd22c58397c52cc7e203e8ecbc362f1` (`certifications/realizable-hardness/`), which is the last packing stop-loss that includes every GO / GO-WITH-NOTES increment through `readTableTag_mem_FP` and `listLenBits_mem_FP`.

This is **not** a complete formalization of manuscript Theorem 1 or Corollary 2. Unconditional NP-hardness, inhabited `hSrcCmmsa`, `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, and P versus NP are not claimed.

## Build

Toolchain: Lean 4.34.0-rc2 (`lean-toolchain` at the repository root). Dependencies are pinned in `lakefile.toml` / `lake-manifest.json` (complexitylib `6c248df`, mathlib `e06eff5`, cslib `d9be641`).

```
lake update
lake build PvNP
```

Do not treat a component GO as the paper theorem.

## Provenance

See `PROVENANCE.md`. Reviews with GO or GO-WITH-NOTES are under `reviews/`. Increment closeouts are under `evidence/`.

## Remaining Lean work (continue here)

1. `readTableTag_of_rows` / ValidRows tree agreement
2. `decodeInputTag_mem_FP`
3. `paddedRun` / `selectedPairedRun_mem_FP` / `selectedSeededMap`
4. 3SAT → `encodeInput` compiler inhabiting `hSrcCmmsa`
5. Unconditional Theorem 1, then Corollary 2

Further Lean edits for this paper belong in this repository, not in the mixed `formal-pvnp` research history.
