# Accepted-good-mass three-lens

Date: 2026-09-26. The statement is
`selected_transverseStar_starAcceptsCenter_rankGood`.
It is not route-final. Theorem 1 and Corollary 2 are not claimed.
Full CMMSA stays partial.

`transverseStarAcceptsCenter` calls `starAcceptsCenter` on the presented
forms of both extensions of one `starLaw` draw. Acceptance implies the
extensions are equal. The intersection with rank-good `jointlyDirect` is
empty, so `r` is the acceptance mass, which is at most
`1 / gaussian(2J − leafT, leafK) < S/2`.

Local `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

GCP replay debt: `gcp-replay-starAcceptsCenter-rankGood-2026-09-26`.
`gcloud` auth for `dfredriksen@quantyra.org` succeeds. The replay was not
sealed in this increment.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Checks target exits 0. Axioms are `propext`, `Classical.choice`, `Quot.sound`. No `sorry`. |
| Proof-adversarial | NO-GO | A review of the earlier self-copy form, where both query slots were the first leaf and `Rel.refl`, is NO-GO. The shipped predicate passes both extensions into `starAcceptsCenter`. That revision was not given a separate review, so the shipped wording is not cleared. |
| Complexity | GO-WITH-NOTES | The probability is one `starLaw`: `centerLaw` then two independent extensions. Acceptance sits inside the equal-extension event, whose mass is below `S/2`, and the rank-good intersection is empty. This is not an `FP` map, Theorem 1, or Corollary 2. |
| Non-claims | GO-WITH-NOTES | The stop note does not claim Theorem 1, Corollary 2, route-final, or full CMMSA. README.md and MANUSCRIPT.md are unchanged. `r` is the acceptance mass of an event contained in equal extensions, not a positive good-mass gap. |
