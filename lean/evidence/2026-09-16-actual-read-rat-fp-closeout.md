# Closeout: packed readRat in FP (`readRatTag_mem_FP`)

Date: 2026-09-16
Source commit: `dbdca8728e164f41d9fbe005ab699f48450c67f4`
Freeze: Quantyra-Planning `docs/research/pvnp/read-rat-tag-fp-freeze-2026-09-16.md`

## Statement

`readRatTag ∈ Complexity.FP`. Packed GCD/`dropTwos`/`packReduced` compose on digit tapes. This is **not** semantic agreement with `readRat`/`ratTree` (`readRatTag_of_tree` open) and **not** `decodeInputTag_mem_FP`.

Not claimed: `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, Theorem 1, Corollary 2, P vs NP.

## Certification

Target-fresh isolated compile on `quantyra-lean-builder-01`. Gate named `dbdca87`.

| Item | Value |
|---|---|
| Main SHA-256 | `2508B3F45C37D04889D3B6448F0DAF44E8842F625B8D778D743E3A920D487763` |
| Checks SHA-256 | `9380B508A6BF71A74311AA8B6884921982D9B8CB3CB0DDC4D43FE80DC65E0B7A` |
| Bundle SHA-256 | `F06511A2A11C1BF42C43B7850143835005DC60624435358184501BDF1DAA863F` |
| `ActualDecodeInputFP.olean` | `0F4729C564C61B7DF5B47091C59D826D3B13A7874553BEB0CDFD032D6EAC83DB` |
| `ActualDecodeInputFPChecks.olean` | `D22359AA6A705B5FB352C0A8573A5B1B113EEF59AC896DE0AC7369C3AB7A36C9` |
| Artifact manifest | `5CFAD7D15BCE0AF984309093A24971DC90DCF399B668BFD7642EEC026559BF5A` |
| Independent rehash | PASS, 175 rows, 0 mismatches |
| Forbidden scan | clean |
| `#print axioms readRatTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |

Checks inhabit `readRatTag ∈ Complexity.FP`.

## Next consumer

`readRatTag_of_tree`, then `decodeInputTag_mem_FP`.
