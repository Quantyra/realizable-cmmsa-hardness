# Proof-adversarial review of the selected analytic moment

Date: 2026-09-30. Owning planning work: full Lean certification (S3126), outer game and star PCP (S3132), research portfolio (E004).

**Verdict: GO-WITH-NOTES for the frozen conditional analytic increment only.** No blocking proof, hypothesis, substitution, rank-conditioning, or center-marginal error was found in the reviewed increment. This verdict does not establish inhabited classical contracts, the original-source failed-zoom premise, an inverse theorem, robust 8S, numeric NO soundness, runtime, Theorem 1, Corollary 2, or manuscript completion.

## Scope and independence

The reviewer was launched by the orchestrator as a separate top-level proof-adversarial agent. The source author was reported as Luna; prior root/Sol proof-routing assistance and model/persona overlap were disclosed. This review independently inspected source bytes, theorem statements, proof bodies, imported interfaces at the application boundaries, and the actual durable native receipts. It did not rely on the orchestrator's summary as proof evidence. This is AI review, not human peer review or an independent proof-kernel implementation.

Read-only review was performed in `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness`. No compiler, GCP, source edit, or git operation was performed. This review file is the only artifact written. The Task launch mechanism was unavailable; collaboration fallback routing was disclosed and remains a protocol-routing note for orchestrator closeout.

Planning sources read: `README.md`, `AGENTS.md`, `docs/protocol.md`, `docs/entity-protocols.md`, `docs/formal-three-lens-closeout-protocol.md`, `docs/research-portfolio-boundary-map.md`, `docs/local-codex-workflow-protocol.md`, the owning stories, the inherited IGH baseline, and the IGH-to-Quantyra inbox, with a final inbox recheck. The satellite contains no `AGENTS.md` at its root or the reviewed Lean directory ancestry; the checked filesystem parent paths contained none. Satellite `README.md` and the existing classical-condition/provenance notes were read.

The accepted frozen sources are:

| File under `lean/PvNP/RealizableHardness/` | SHA-256 |
| --- | --- |
| `ActualSelectedComplementAnalyticMoment.lean` | `BFAE5D2ECAA63D258742FC776B3A21720744F0238A6624D4800304072FFE92F9` |
| `ActualSelectedComplementAnalyticMomentChecks.lean` | `8D2F2596FEA7917F306F1F26907563DD78181D5973305F644F597BC704383979` |
| `ActualFiniteMomentLpBounds.lean` | `BF9C27E32D08A6D4FCE7853D6D45F5BF2BA229635BE0C2AC7229A02979B5532B` |
| `ActualSelectedSpectralParameters.lean` | `78FB8DF0B635E950ED087C3598530B328AD25EC5AC4B2DBF556CBE433A46E582` |

`ActualCoordinateZoomFailureTransport.lean` is excluded. Its inclusion as source bytes in the native input archive is not compilation or acceptance evidence. Neither the main module nor Checks imports it, and the inspected native script names only the parameter, main, and Checks build targets.

## Native evidence checked

Evidence directory: `docs/native-receipts/ActualSelectedComplementAnalyticMoment/durable-runs/cmmsa_analytic_20260930T072903Z/`.

- The 32,899-byte evidence archive has SHA-256 `A0A764BF164D620DCAA83D0856ACA7BADED8EBEC465E59DD6B6E6A9457E46153`.
- All 34 entries in `byte-exact-manifest.json` were rehashed and matched. The native evidence archive's regular files equal the corresponding `raw-evidence` copies byte for byte.
- The four reviewed files in the frozen input archive equal the live reviewed bytes. `source-before.sha256` and `pins.sha256` retain the same four hashes.
- The actual native exit files record parameter prebuild `0`, main prebuild `0`, and terminal native exit `0`. The corresponding logs end with successful builds at 3,229, 3,358, and 3,359 jobs respectively.
- The eight scoped profiles printed by Checks lines 13-20 each contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Additional dependency profiles occur earlier in the log; they are not confused with the eight requested profiles.
- `wrapper-terminal.json` records wrapper exit `0` and expressly distinguishes wrapper outcome from native proof status. The recorded final describe output is `TERMINATED`. These are historical receipts, not a fresh cloud-state query.
- The script verifies the frozen input archive, checks reused dependency source bytes against that archive, checks source hashes, removes parameter/main/Checks objects before the named builds, and retains native exit evidence. It does not build the excluded coordinate transport. The helper is accepted through the main import and successful dependency build; it is not separately claimed as a freshly deleted helper object.

The forbidden-token scan found no `sorry`, `admit`, new `axiom`, `native_decide`, or `unsafe` in the three proof source files. The native logs showed linter notes rather than proof failures.

## Concrete proof findings

Line references below are to `ActualSelectedComplementAnalyticMoment.lean` unless another file is named.

| Check | Finding |
| --- | --- |
| Normalized Lp and append averaging | `ActualFiniteMomentLpBounds.lean:22`, `:52`, `:85`, `:101`, and `:136` use genuine finite Jensen, the append/product equivalence, and normalized Minkowski. Both matrix carriers have positive cardinality, including zero dimensions. The same unconditional all-matrix measure survives the contraction. Lines 292-329 apply finite Minkowski and the per-level HC premise to that carrier. |
| Same Boolean and functional | Lines 60-80 define the actual leaf/center rank-image Booleans and establish all-matrix right-basis invariance. The imported proof handles injective and deficient inputs separately (`ActualRankImageRightBasisInvariance.lean:78`); no full-rank input premise is smuggled into the spectral call. Lines 98-110 and 1274-1276 obtain exact-budget PR for the identical selected leaf and functional. |
| Fourier reconstruction | Lines 150-171 reconstruct all rank levels using Fourier inversion and rank at most column width. Lines 174-210 split each frequency once into low or high. The final estimate consumes this proved decomposition at lines 718-747; its reconstruction is not an assumed final-moment field. |
| Threshold and Holder | Lines 385-453 prove a good/bad threshold inequality from the Boolean append average in `[0,1]`, `a>0`, and the decomposition. Lines 548-559 apply weighted Holder. Lines 998-1059 drop only the center indicator weight, convert the literal mth power to the kth power, and take the appropriate nonnegative root. No positive beta premise or division by beta is introduced. |
| Correct center distinction | Lines 566-619 obtain matrix center mean as the full-rank factor `alpha n c 0 0` times Grassmann beta, then use `alpha<=1`. They conclude **at most beta**, not equality. Deficient matrices are zero. This is the correct quantity for the threshold and Holder estimates. |
| Exact rational center marginal | Lines 1095-1152 prove matching center mass equals Grassmann beta for each fixed `f`. The auxiliary table `T0(W)=f|W` is used solely to make all leaf tests true when extracting this center-only marginal. The original leaf `T` remains in the analytic/star estimate at lines 1278-1301. There is no T0 substitution into the target leaf moment. |
| Post-append high energy | Lines 766-799 expand the finite square and erase off-diagonal terms using the actual post-append orthogonality theorem. Lines 804-873 apply the squared spectral bound per level. This does not infer post-operator orthogonality merely from the per-level spectral estimate, nor assume an unrestricted adjoint. |
| Dyadic window | Lines 888-913 use the least dyadic integer at least `4*m`, proving `4*m<=k<8*m` under `m>0`. The selected caller derives `m>=256`, so neither zero-moment division nor an unbounded dyadic surrogate is used. |
| Integral split and source cutoff | `ActualSelectedSpectralParameters.lean:46` derives `m>=256`, `h>=m+2`, divisibility, positive append width, `c+s=2h`, and the precise real split at `rho=1/bOf m`. Its floor preserves both `base m` and `sourceHeightCutoff rho`. The caller at lines 1208-1210 assumes selection against this augmented floor explicitly. It does not silently transfer the result to an older selector. |
| Ambient dimension and rank loss | Lines 1154-1190 derive source dimension from the selected floor and `samplerA>=1`. Lines 1263-1273 establish `c+s<=n` with `n=2J`. The inherited selected append bound supplies the factor two after deriving its rank-loss guard (`ActualSelectedComplementAppendMoment.lean:155`). The result is not a new rank-conditioned experiment. |
| Material caller | Lines 1197-1256 retain original `I,copies,U,A,C,T,f`, form the corresponding coordinate tables and functional, and conclude original matching star mass `<=2*selected_actual_analytic_rhs` together with exact original matching center mass `=beta`. Lines 1282-1320 compose the original coordinate mass transport, conditional same-function moment estimate, and center identity. |

## Notes and required debt

**MEDIUM — conditional classical interface, not an inhabitance result.** `HC46ExactContract` at lines 35-40 and `Spectral47ExactContract` at lines 45-58 are propositions supplied by the caller. They are not local axioms, and the standard axiom reports do not discharge them. Their displayed shapes align with the dyadic Boolean estimate and squared basis-invariant estimate in [Minzer–Zheng v1, section 4.2](https://arxiv.org/html/2510.23991v1#S4.SS2). The explicit cutoff is retained; no extra eta-upper-bound or Boolean-PR basis-invariance premise was added to HC. Exact contract inhabitants and any reconciliation of source standing assumptions remain outstanding. No fully instantiated unconditional application is certified here.

**MEDIUM — the failed-zoom family is still a coordinate premise.** Lines 1217-1228 require every coordinate `q,Q,P` with exact budget `r` and nonzero zoom cardinality to satisfy agreement `<=e` for `selectedCoordinateLeafTable I copies U A T`. This is the complete required family, not a single failed zoom or a witness chosen after `f`. The accepted theorem does not prove that an original-source ladder failure supplies this family. Clearing that transport debt requires separate compilation, review, and exact statement comparison of the excluded transport increment.

**Non-vacuity limit.** No accidental empty carrier or contradictory added positivity guard was found in the finite inequality pipeline. The selected dimensions make the Grassmann and above-center carriers nonempty; the material theorem derives positive m and append width. Zero beta is allowed and creates no beta denominator. Nevertheless, this increment supplies neither joint inhabitants of its two classical contracts nor a selected original-source witness satisfying all hypotheses. Its conditional status must remain visible. Acceptance does not establish non-vacuity of a completed hardness theorem.

**LOW — intermediate comment.** Lines 621-624 call the decomposition an outstanding obligation for an intermediate consumer that takes `hdecomp`; the final reconstructed consumer at lines 718-747 discharges it. Closeout language should describe the final exports rather than repeat that intermediate comment as current debt.

Remaining work belongs to the owning orchestration stories (S3126/S3132): accepted original-source failed-zoom transport; exact classical contract inhabitants; inverse/decoder derivation; numerical comparison at the manuscript parameters including robust 8S; outer NO contradiction; source YES; encoded polynomial producer and same-function reduction/runtime; full theorem/corollary assembly; paper reconciliation and subsequent claim/publication gates. The orchestrator must preserve these as open work and record the complete three-lens table. This single GO-WITH-NOTES verdict does not close the full core or either owning story.

Remaining to-do list for this reviewer: none. Remaining route debt: as listed above.
