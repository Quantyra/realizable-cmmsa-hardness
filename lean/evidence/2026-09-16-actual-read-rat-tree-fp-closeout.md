# Closeout: readRatTag_of_tree (local target-fresh after GCP auth failure)

Date: 2026-09-16
Source commit: `93d35131ed5317209ab456651387d4d9a2558fc2`
Freeze: Quantyra-Planning `docs/research/pvnp/read-rat-tree-bridge-fp-freeze-2026-09-16.md`

## Statement

`readRatTag_of_tree`: packed `readRatTag` on `encode t` agrees with semantic `readRat` / `ratTree`. Also `gcdBits_odd_pair`. Not `decodeInputTag_mem_FP`.

## Certification

GCP `quantyra-lean-builder-01` could not start: `Reauthentication failed. cannot prompt during non-interactive execution.` Captured `{SCRATCH}/gcp-of-tree-unavailable.log`. Local target-fresh of frozen `93d3513` blobs (not the dirty Luna worktree): main+Checks twice, matching hashes, exit 0.

| Item | Value |
|---|---|
| Main SHA-256 | `6356E80AF6A35BF9725434C911961B130A2BAD86F46B42951A7E2D85FB2907D4` |
| Checks SHA-256 | `0EA0879E4232070A818E453FB0885A1934BFC29709391DA022817038088593E1` |
| Bundle SHA-256 | `3BE4A9BE96181EA7536E5C6E2580D0BD8AED32FE999642C589418C3F0B36A664` |
| `ActualDecodeInputFP.olean` | `825FD451B5E459A111AAEC37238062F373E9FEE1869DA4A373341E91F6DA1BFB` |
| `ActualDecodeInputFPChecks.olean` | `F6DFD04AD74F078DA70BE8F9FDECE26F07F9B4711882585EB1522F09A6AEC209` |
| `#print axioms readRatTag_of_tree` | `propext`, `Classical.choice`, `Quot.sound` |

Log: `{SCRATCH}/of-tree-local-cert.log` copied into this evidence dir.

## Next consumer

`decodeInputTag_mem_FP` via `readInputTag ∈ FP`.
