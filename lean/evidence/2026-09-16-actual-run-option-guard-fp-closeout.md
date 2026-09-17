# Closeout: runOptionGuardTag_mem_FP (decode + trials*precision length guard)

Date: 2026-09-16
Repo: realizable-cmmsa-hardness
Source commit: `c78bf1a5b4c8c31fe82535f3f293c57c2b348da2`
Freeze: Quantyra-Planning `docs/research/pvnp/run-option-fp-freeze-2026-09-16.md` (stop-loss)

## Statement

`runOptionGuardTag_mem_FP`: packed decode + unary `trials*precision` length guard of `runOption`. Success payload is `true :: pair instanceBits coins`; malformed decode is `[]`. Not `runOptionTag_mem_FP`. Not `selectedPairedRun_mem_FP`. Not Theorem 1.

## Certification

GCP builder TERMINATED (idle-stopped after previous increment). Local target-fresh of frozen `c78bf1a` blobs: main+Checks twice, matching hashes, exit 0.

| Item | Value |
|---|---|
| Main SHA-256 | `99B5245219A98031C9BA4537E19E2968FF29AD0327F41153CBF8B3275D5EB152` |
| Checks SHA-256 | `FAF432B65CAC722C809646E2979EB8F2CEB43037D7018944C35DD64A055F38D8` |
| git blob Main | `7fe2f4c6bf7faffee4ea20d70b0cb108f57941a6` (35975 bytes, LF) |
| git blob Checks | `373bbdbd75f65f21c7b48867d973c600ea0dc224` (2183 bytes, LF) |
| `ActualSelectedCmmsaSeededMap.olean` | `960B9AB41DA7C6BF5621A2BB285FA926A1D43F34AEE63E2E5AF7352F7BFB1651` |
| `ActualSelectedCmmsaSeededMapChecks.olean` | `6C841EBD06E28B9E470E600F26517364C4A270E49083B5A1F8B630BCC8CD4B9B` |
| `#print axioms runOptionGuardTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |

## Next consumer

`runOptionGuardTag_eq` then packed `checkedBits`/`accepted`/`tree`/`bits`, then `runOptionTag_mem_FP` and `selectedPairedRun_mem_FP`.
