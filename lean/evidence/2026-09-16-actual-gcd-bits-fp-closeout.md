# Closeout: packed binary GCD in FP (`gcdBits_mem_FP`)

Date: 2026-09-16
Source commit: `7105c9504c55226b4143624a4f0143379e11c1ba`
Freeze: Quantyra-Planning `docs/research/pvnp/gcd-bits-fp-freeze-2026-09-16.md`

## Statement

`gcdBits` packs binary GCD of digit tapes as a total `List Bool → List Bool` function. `gcdBits_mem_FP : gcdBits ∈ Complexity.FP`. `subCanon_bitValue` gives canonical subtractive length. This is a stop-loss: `readRatTag_mem_FP` and `decodeInputTag_mem_FP` are not proved.

Not claimed: `readRatTag_mem_FP`, `decodeInputTag_mem_FP`, `selectedPairedRun_mem_FP`, `selectedSeededMap`, `hSrcCmmsa`, Theorem 1, Corollary 2, P vs NP.

## Certification

Target-fresh isolated compile on `quantyra-lean-builder-01` (Lean 4.34.0-rc2). Gate named `7105c95`.

| Item | Value |
|---|---|
| Main SHA-256 | `8C9B46562B478EB93870249071E8636FFEC80A6F8A068E681D2467E0963FBD8A` |
| Checks SHA-256 | `3FF960978E4C1567E74B764704612B72044A76639DA2D18EFAC0EF92921422E6` |
| Bundle SHA-256 | `D706ABC78AC3B786CF47FE1DF4FBB4DEDE73B9796F20BC39B5B377C47D9AD756` |
| `ActualDecodeInputFP.olean` | `68D4E315CDC58A7410C0A5BB1C07ED5675F268040A26121BC735F24C52B749AD` |
| `ActualDecodeInputFPChecks.olean` | `4B90D9D4541098CE91846ECD6BA6945FB57A3122F28CF9F106593D01473315C8` |
| Artifact manifest | `6443BE05228C45699589EC8E02667535E321447915823CC9197636EE37FA3786` |
| Archive | `790B7DB0583489A047CA241A81AAE2F8404CC71E83544FCDA5442D1EDE3ACCF0` |
| Independent rehash | PASS, 175 rows, 0 mismatches |
| Forbidden scan | clean |
| `#print axioms gcdBits_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |

Evidence: `research/evidence/2026-09-16-actual-gcd-bits-fp-fresh-run/`

## Next consumer

`readRatTag_mem_FP` (semantic GCD of the iterate, then reduced `ratTree`), then `decodeInputTag_mem_FP`.
