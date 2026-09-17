# Closeout: readTableTag_of_rows (ValidRows tree agreement)

Date: 2026-09-16
Repo: realizable-cmmsa-hardness
Source commit: `a59171452a27edff5eaf99365fbcf64e402a307f`
Freeze: Quantyra-Planning `docs/research/pvnp/read-table-of-rows-fp-freeze-2026-09-16.md`

## Statement

`readTableTag_of_rows`: packed `readTableTag` on `true :: encode (listTree (rows.map rowTree))` agrees with `FiniteSourceSampler.ValidRows`. Not `decodeInputTag_mem_FP`. Not Theorem 1.

## Certification

GCP reauth failed. Local target-fresh of frozen `a591714` blobs (not dirty Luna worktree): main+Checks twice, matching hashes, exit 0.

| Item | Value |
|---|---|
| Main SHA-256 | `7F1866ED2F508B2909E9D90C323BA5C4259969829ED0214E7967C0B3536367DE` |
| Checks SHA-256 | `278CD6A23C62792B75B62E670E1B44F256FCA45276FF6522CE005E94F465B621` |
| `ActualDecodeInputFP.olean` | `05288D3D0DDA3EFD6300642D10CE2774D4B77551DAFD010014D23880F97BEFE5` |
| `ActualDecodeInputFPChecks.olean` | `E615ED35D700F69C6C417E08391140702D4B6F0EDAD5B7B5B055A093D29F14E0` |
| `#print axioms readTableTag_of_rows` | `propext`, `Classical.choice`, `Quot.sound` |

## Next consumer

`readInputTag_mem_FP` then `decodeInputTag_mem_FP`.
