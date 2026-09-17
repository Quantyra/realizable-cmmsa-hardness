# Closeout: paddedRunGuardTag_mem_FP (decode + coinRuler guard)

Date: 2026-09-16
Repo: realizable-cmmsa-hardness
Source commit: `b8ba7b55b542759d151410667ed56e50f6dcad3e`
Freeze: Quantyra-Planning `docs/research/pvnp/selected-paired-run-fp-freeze-2026-09-16.md` (stop-loss)

## Statement

`paddedRunGuardTag_mem_FP`: packed decode + `coinRuler` length guard of `paddedRunOption`. Success payload is `true :: pair instanceBits coins`; malformed or length-mismatch is `[]`. Semantic agreement `paddedRunGuardTag_eq`. Not `selectedPairedRun_mem_FP`. Not Theorem 1.

## Certification

GCP builder started then idle-stopped; manuscript-repo content-addressed cloud gate is not ported. Local target-fresh of frozen `b8ba7b5` blobs: main+Checks twice, matching hashes, exit 0.

| Item | Value |
|---|---|
| Main SHA-256 | `1B3BCB0452CD11DCB9C7B61E97F35FF8807297C0526F92534BF9DD2F3D7E69C9` |
| Checks SHA-256 | `94D888D4645D8BD0EB4231F2766F8878030CDC3C585AC06B4F3A0B055E3344A8` |
| git blob Main | `de09577c74a2910aa2b81a360a5b4c3b5272878f` (14990 bytes, LF) |
| git blob Checks | `3f0fdc959eb9b333b79c142f4adc3a5cd3abd8c5` (1759 bytes, LF) |
| `ActualSelectedCmmsaSeededMap.olean` | `85487B040ABB6C47267693905D152392E9F461705078D09FB665F903FCC58F5B` |
| `ActualSelectedCmmsaSeededMapChecks.olean` | `FC2513F4FBD85CC8AEDBD10BA4CB5E53B51034A6C387A912D7DEDEDD0573D5D3` |
| `#print axioms paddedRunGuardTag_mem_FP` | `propext`, `Classical.choice`, `Quot.sound` |

## Next consumer

Pack `runOption` / `checkedBits` then `selectedPairedRun_mem_FP`. Do not inhabit `hSrcCmmsa`. Do not claim Theorem 1.
