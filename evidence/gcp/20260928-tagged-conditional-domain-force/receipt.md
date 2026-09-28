# Fixed-question tagged conditional domain force

- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`.
- Exact source: current `6b4515f` archive plus the four Lean modules below, copied into isolated `/tmp/tagged-domain-r1`. Complete pinned package cache symlink: `/home/dfredriksen_quantyra_org/cmmsa-phasea-build-185df9d/.lake/packages`.
- Terminal check: detached PID `6237`, exit `0`; `lake build PvNP.RealizableHardness.ActualTaggedConditionalDomainDrawChecks` completed successfully, `3250` jobs. Full output: `checks.log.gz` (raw UTF-8 log, gzip compressed).
- The listed theorems' `#print axioms` returned only `propext`, `Classical.choice`, and `Quot.sound`.

| Module | SHA256 |
| --- | --- |
| `ActualTaggedConditionalGraphCount.lean` | `079561f0b9f7714f75bd89564762e448302bebd7bc8aa638eff0f4b18a322457` |
| `ActualTaggedConditionalDomainCollision.lean` | `14da432c993ed3d0f88fb10a66a67a3ab1850d78e77892e2365d77ea54060783` |
| `ActualTaggedConditionalDomainDraw.lean` | `23a4ca9158310e4b9d19481a3d8f82d09644891ed06999c2993c12a83e084a36` |
| `ActualTaggedConditionalDomainDrawChecks.lean` | `b73ae6884e659bc120dc81de0a061038407385889fa5f8ee5a7fd4cedd490265` |

For every fixed eligible tagged question `q=(U,K)` with `t≤2h` and `h≤J`, the complete eligible full-domain draw has exact cardinal `gaussian (2*J-t) (2*h-t)`. Every such domain has a transverse leaf presentation containing the same ambient `q.K`; each domain has exactly `2^(J*(2*h-t))` eligible presentations. The uniform conditional presentation law therefore pushes forward to the uniform full-domain law. These statements apply before fixing or evaluating arbitrary center and raw vertex tables.

Open: the explicit `taggedClassCollisionMass` of the ordered law has no numeric bound here. The initial-vertex/clique-resampled-row manuscript marginal, MZ local decoder, and numeric NO-soundness remain open. This receipt makes the conditional domain denominator exact but does not by itself reduce the numeric NO gap.
