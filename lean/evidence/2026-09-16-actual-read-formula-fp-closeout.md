# Closeout: packed readFormula in FP (`readFormulaTag_mem_FP`)

Date: 2026-09-16
Source commit: `41c6e1ca1d4fc3d264d319fdd20cb65170b1851c`
Freeze: Quantyra-Planning `docs/research/pvnp/read-formula-tag-fp-freeze-2026-09-16.md`

## Statement

`readFormulaTag ∈ Complexity.FP` via `formStep_encode`, `formReach_step` with `formula_encode_le` on the parent, `formReach_iterate`, `Cobham.iterate_mem_FP`. Not `readFormulaTag_of_pair`. Not `decodeInputTag_mem_FP`.

## Certification

GCP reauth failed. Local target-fresh of frozen `41c6e1c` blobs (not dirty Luna worktree): main+Checks twice, matching hashes, exit 0.

| Item | Value |
|---|---|
| Main SHA-256 | `ACD77A39B055A6F0630661D86D785BF256AE03B2FBDA15B682706373C9B09821` |
| Checks SHA-256 | `9200399532E217768D248356E9FDDC2E4346D4C3C5DB9A72BC1E5BB2C3025A60` |
| `ActualDecodeInputFP.olean` | `C118C1F7DDCD60180FB143CD571AD763F7318AC0E7B5AB9A9549AC7D6AABFA6E` |
| `ActualDecodeInputFPChecks.olean` | `12273BFE4B9EA38F8116DB27AB611B6079DFF87D8CB3DEF2EFD86EFC6480D048` |
| `#print axioms readFormulaTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` (from Checks compile) |

Checks inhabit `example : readFormulaTag ∈ Complexity.FP`.

## Next consumer

`readFormulaTag_of_pair`, then `readInputTag_mem_FP` / `decodeInputTag_mem_FP`.
