# Accepted-good-mass three-lens

Date: 2026-09-26. Proof commit `523fbc1`.
Scope: `selected_joint_accepted_rankGood`. `jointLaw` is `starLaw`.
`jointLaw_draws_center` is `centerLaw` times the leaf law of that same
drawn center. Acceptance is `accepts` and rank-good is `jointlyDirect`
on that tuple. `leafT ≤ 2h` and `h ≤ blocks` are lemmas. The
`coordinateCenterGrass` fiber is `DomainDraw` by
`physical_domainDraw_eq_center_extension_law`. This increment is not
route-final. Theorem 1 and Corollary 2 are not claimed.

The supplied-center `uniformDomainTupleLaw` claim and its `GO` table are
withdrawn. Proof-adversarial and complexity did not accept that claim,
so those verdicts are `INCOMPLETE` rather than `GO`.

## Three-lens

| Lens | Verdict | Note |
|------|---------|------|
| Build/audit | GO | Local and VM `lake build --old` of the checks module. Axioms are `propext`, `Classical.choice`, and `Quot.sound`. |
| Proof-adversarial | INCOMPLETE | Not run on the joint-law statement. The earlier `GO` excused a supplied center and is withdrawn. |
| Complexity | INCOMPLETE | Not run on the joint-law statement. A nonempty leaf witness is not a center draw. |
| Non-claims | INCOMPLETE | Not run as a separate lens. The module text does not claim Theorem 1, Corollary 2, or route-final. README and MANUSCRIPT are unchanged. |

Full CMMSA remains partial.
