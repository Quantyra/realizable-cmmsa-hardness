# Closeout: decodeInputTag_mem_FP (packed decodeInput in Cobham FP)

Date: 2026-09-16
Repo: realizable-cmmsa-hardness
Source commit: `f7f338bdd28101ff66fa482716a435ca783cd191`
Freeze: Quantyra-Planning `docs/research/pvnp/decode-input-compose-fp-freeze-2026-09-16.md`

## Statement

`readInputTag_mem_FP` and `readInputTag_of_tree` pack `readInput` (weights, packed rows/`ValidRows`, parameters, precision, trials). `decodeInputTag_mem_FP` then places `decodeInputTag` in `Complexity.FP` via existing `decodeInputTag_mem_FP_of_read`. Not `selectedPairedRun_mem_FP`. Not `selectedSeededMap`. Not Theorem 1.

## Certification

GCP reauth failed. Local target-fresh of frozen `f7f338b` blobs: main+Checks twice, matching hashes, exit 0.

| Item | Value |
|---|---|
| Main SHA-256 | `D2405DC2CE759190671801AEF669297C1F8DD9F56BAC1079F7E95D9EB87DDD87` |
| Checks SHA-256 | `BAD35DD0BFFD06A007E5C552C494AAA823AF1B266CB2F74498EF01E0B614DC9D` |
| git blob Main | `aba9e488124928fba7d18fbb22f6d056b20c8eff` (402609 bytes, LF) |
| git blob Checks | `aef903bfaf40998fb168184274973214f62bcee4` (6581 bytes, LF) |
| `ActualDecodeInputFP.olean` | `773E14769F846688877E9E0857873E8AB3286E4CBA43D3D3161D6A717ECBB8E8` |
| `ActualDecodeInputFPChecks.olean` | `BB977DD6D036454A4C9B5978347A5D345D62F3CA0B816030172A55B57DDF3BC2` |
| `#print axioms decodeInputTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |
| `#print axioms readInputTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |
| `#print axioms readInputTag_of_tree` | `propext`, `Classical.choice`, `Quot.sound` |

## Next consumer

`selectedPairedRun_mem_FP` then `selectedSeededMap`. Do not inhabit `hSrcCmmsa` with identity. Do not claim Theorem 1.
