# Checks and claim boundary

| Item | Status | Limit |
|---|---|---|
| Actual finite `(a,Q,P)` candidates | Defined with `a : Fin (r+1)`, every actual decoded functional, and `a+codim(W)≤r` | Fintype instance is a source candidate, uncompiled |
| Actual `X∩Zoom` coordinates | Defined by the two subspace inclusions on distinct `Grass V d` indices | No Gaussian zoom-card theorem in this module |
| Candidate target | Uses the actual decoded linear functional via `targetFromMap` | Functional-agreement equivalence still requires an explicit extensional lemma |
| Per-candidate strict tail | Reuses captured `actual_match_tail_bound` | Uncompiled |
| Full candidate union | Omits candidates with fewer than `p` times the zoom size in `X`; bounds the remaining actual union mass by all candidate tails before adaptation | No uniform lower bound or `F_n` count yet |
| Preserving fresh table | Positive-mass extraction when full union mass `<1` | The required cutoff has not been connected |
| Bounded stopped history | Mathematical derivation recorded in `ARGUMENT.md` | Not yet encoded; no event-level `B_nF_n` theorem |
| Potential and many-Q | Argument recorded, source proof open | No many-Q theorem or final decoder |
| Compilation / GCP / Git | Not run by this author | Sol remains compiler and Git custodian |

Dependencies are the immutable actual tail capture `numeric-refresh-tail-capture-v2` (index `F738579E7F6A481DB58CE4972C8E1E37580A78418977AAC97E69C5C6B10B2560`, source `7B54EE1E137076B252C54C9268083412FE54C2FADC9705170FE4911400D4F538`) and its captured actual-product predecessor (`B04D33E2E0D4DEB2F384C7DDA081497CBDD5ED41035BC43CEAA60A24E4B43678`, source `B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3`). All original Full114 and Mathlib pins are inherited from those captures.

No `sorry`, `admit`, or new axiom was added. No local Lean/lake command, GCP command, or Git action was run. This is source-level translation progress only.
