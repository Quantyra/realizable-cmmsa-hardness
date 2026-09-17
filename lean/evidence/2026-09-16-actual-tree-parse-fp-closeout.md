# Closeout: packed Tree.parse in FP (`treeParseTag_mem_FP`)

Date: 2026-09-16
Source commit: `52b57f29cd7d317bfa77a6d046f58ce3d44633a7`
Freeze: Quantyra-Planning `docs/research/pvnp/tree-parse-fp-freeze-2026-09-16.md`

## Statement

`treeParseTag` packs `CMMSACodec.Tree.parse (|z|+1) z` as a total `List Bool → List Bool` function. Empty tape is `none` (malformed or truncated). Nonempty is `true :: pair (encode t) rest`. `treeParseTag_mem_FP : treeParseTag ∈ Complexity.FP`.

Not claimed: `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, unconditional Theorem 1, Corollary 2, P vs NP.

## Certification

Target-fresh isolated compile on `quantyra-lean-builder-01` (Lean 4.34.0-rc2). Gate named `52b57f2` not `bba6dbb`.

| Item | Value |
|---|---|
| Main SHA-256 | `563831C5485F44DE298A0E896BD6A9843F5B338F8CDA428F15DFBFB9EB057074` |
| Checks SHA-256 | `B9DA8EB5A89BDDA4F81FFA25D2B9D869E20B65978AD3A7ED8C344A131EDDBCA3` |
| Bundle SHA-256 | `F164DAC94862776ADEEBC2E49296E7A78211F6DA6460D00B1C4D16F36109F0CF` |
| `ActualTreeParseFP.olean` | `BEF82D9A5F18A1AB150C4945F370369654706539200555D47FD5437FE7D3F34F` |
| `ActualTreeParseFPChecks.olean` | `3E17CACAAE1A4DF4AB37EF6FA62B53E167605BF8F0FA5F84E1ED5F5B26473D21` |
| Artifact manifest | `41F5DD9E34149C3EEFB3F25E8B8664A27385F8CBFECFB8FB6F06CE0DE60A0E0F` |
| Archive | `21F68150B68274692AF943DEF003CA70A837E49D9888B04668D0F1AF21664E3F` |
| Independent rehash | PASS, 61 rows, 0 mismatches |
| Stages | exception-repair, formula, cmmsa-codec, main×2, checks×2; all exit 0 |
| Forbidden scan | clean |
| `#print axioms treeParseTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |

Evidence: `research/evidence/2026-09-16-actual-tree-parse-fp-fresh-run/`

Independent local `git cat-file` SHA-256 of both Lean blobs at `52b57f2` match the gate.

## Next consumer

`decodeInputTag_mem_FP` (readInput packing after trailing-empty test on `treeParseTag`), then `selectedPairedRun_mem_FP`.
