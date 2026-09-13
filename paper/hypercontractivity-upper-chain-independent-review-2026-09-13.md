# Upper-chain binary hypercontractivity manuscript review

2026-09-13. S3137. Reviewer: compact_source_encoding_audit. Verdict: **GO for this bounded source integration**. No mathematical defect or required correction was found in the reviewed upper chain. This is an informal mathematical and transcription review, not human peer review, Lean/kernel acceptance, PDF/layout acceptance, or certification of the entire manuscript.

## Exact candidate and role

Reviewed in `C:/Users/Dan/Desktop/Projects/realizable-cmmsa-hardness`:

- `paper/submission-manuscript.md`: SHA256 `d8b03b5fa1524391bc8f492086de8859ba25b361deb2bb86815a1dfbff33f981`, 104745 bytes.
- `paper/body.tex`: `766ebbd2545545063ac0290c68264436b4ef09545289c6986ff5feeb93b80dc7`, 113222 bytes.
- `paper/correspondence.json`: `4dcedadece4b46ef03246c452a0dc6be9544e755df69677f1a56bae94f3dcc88`, 22383 bytes.
- Unchanged renderer: `85eb3770b711843212764ee9785427c3c3ec2454da8a7c0d33b3a2662ae5e8d4`.

All four files above are raw LF files, with no CRLF-to-LF distinction in these hashes. I reviewed the canonical appendix from the globalness definition and (A13) through the conclusion, its theorem/interface statement, and the inverse-lemma invocation. I read the complete changed-source diff for claim drift. Incidence's separate review owns the newly transcribed lower chain through (A12); this note does not present that division of review as a second independent reconstruction of every lower lemma.

I did not author this manuscript integration or the four upper-chain derivations. I previously reviewed those derivations and authored their joined Boolean inequality review. I also contributed to lower-chain challenges and the original weighted-fourth-power counterexample. Consequently this is an independent integration check with disclosed mathematical contributions, not a claim that I am a noncontributing independent certifier of the entire foundation. No source repair, compiler, renderer execution, PDF build, Git operation or public action was performed. Only this requested review note was written.

## Actual source correspondence

I re-read the following accepted finite derivations in `C:/Users/Dan/Desktop/Projects/formal-pvnp/research/p-equals-np/`, with the common filename prefix `2026-09-13-realizable-hardness-`:

- `globalness-to-level-influence-derivation.md`: `c905e6ae82fcc0369161f20b007a02339ecb01a4e4e94bfeea32d4d2ba98f111`.
- `influence-to-globalness-derivation.md`: `563187200f9761458f9d9b106042fafb381238d7a4ea2a7e88275ac2a4c1112b`.
- `square-globalness-dyadic-derivation.md`: `3c75f32e997b35156178ebbc9165717de55485565eb379d64eacc4eaefd0a98c`.
- `lp-globalness-level-influence-derivation.md`: `7b0e90c2e3ba37b513624b935bbc55dc6044bdf64c90f2acaf2f3b5f66f187c6`.

The final join matches `minimal-boolean-hypercontractivity-joint-review.md`, `45773a367aabdd4d7555c88e4adc508869df11ce3c9a3ca21c6982925215cdea`. These identities were freshly rehashed. The manuscript supplies the actual proofs, rather than replacing these notes with theorem-name citations or an assumed analytic certificate.

Read-only verification also checked every one of the 130 correspondence span hashes against the exact canonical lines and checked the manifest's source hash. All four complete raw-LaTeX blocks occur in the generated body after precisely the existing renderer's Gaussian-binomial `genfrac` substitution. The appendix is one such complete block. There was no need to regenerate or mutate either artifact. The 30 display count is the existing renderer's legacy display count, not a claim that the newly appended tagged equations are absent.

## Forward conversion: definitions, phases and small spaces

The manuscript defines up-to-order globalness using every actual affine base and squared normalized L2 norms, including order zero. This avoids the vacuous exact-order premise on a small quotient. The two translation distributions have the correct direct binary eigenvalue counts: zero on the relevant order-one hybrid selector and 2^(-rank Y) otherwise. The hyperplane case uses uniform w outside the hyperplane and all functionals; it is not an unexplained symmetry assumption.

For (A14), raw line quotient or hyperplane restriction changes rank by zero or one, with loss one exactly on the selected frequencies. Thus only input levels j and j-1 can reach output level j-1. The polynomial P_j agrees with the selector on both levels; selected rank j-1 drops below the target, and selected rank zero is absent when j=1. This establishes the stated actual witness at each requested base, without commuting an arbitrary raw restriction with a Fourier projection or discarding within-level collisions.

The coefficient sum bound gives squared loss 4*2^(4j). Composing the actual restrictions adds orders and canonically embeds bases with the same normalized measure. Peeling precisely k positive orders, then using the final projection's Parseval bound, gives exponent 4kd-2k^2+4k. The order-zero and d=0 cases are stated separately. For a full bounded-degree function, the residual ranks i-k are distinct across surviving levels; summing orthogonal squared norms gives 11d^2. This does not reuse the false fixed-base rank-poset contraction.

## Reverse conversion: conditional measure and induction range

The restriction-averaging proof keeps the exact affine law. Conditional on A'=ker(phi restricted to A) and B'=B+span(w), the unexpanded branch is uniform on Hom(V/A',B). In the expanded branch, the first column is uniform outside B, while the remaining columns are uniform in B'; this is conditioning an otherwise uniform map on an event of probability 1/2. Thus the squared norm costs at most two. When s=0 the expanded branch is impossible, so no negative-order premise occurs. Transpose exchanges actual restrictions with their annihilator restrictions, preserving order and probability law.

The homogeneous identity and squared triangle inequality therefore give (A17), including both factors two. The manuscript explicitly proves the all-r statement using outer induction on d simultaneously for all spaces and all r, followed by inner induction on r. Levels inherit influences by projection on distinct reduced ranks, and first derivatives inherit them by actual composition. Relative to K=2^(10dr)*epsilon, the top contribution is at most 9/512, smaller-order top bounds at most K/4, and lower levels at most K/961. Their final combination is strictly below K. Neither this argument nor the forward conversion imports a fourth-moment or dyadic assertion. Missing exact-order families and unavailable levels are treated without selecting nonexistent subspaces; epsilon zero follows from order-zero norm.

## Square-globalness and dyadic moments

The manuscript retains every conversion factor: 11+103=114, reverse enlargement to order 3d gives 41, and both restricted factors B=2^(41d^2)*epsilon yield 114+2*41=196. Every raw restriction of order at most 2d is on its actual quotient/subspace and is global through another d orders by composition. Its degree remains at most d because each character restricts to frequency q_A Y restricted to B, whose rank cannot increase. The product degree bound follows from character multiplication and rank subadditivity; complex squaring is legitimate because |f^2|=|f|^2. Hence (A20) bounds the actual square, rather than an auxiliary square with assumed globalness.

The induction at p/2 uses the actual doubled degree 2d, retaining the factor 4 before A_(p/2). Its recurrence is A_p=4A_(p/2)+49p-82, A_4=114. The invariant A_p<=200p^2-100p propagates as written. The p=2 case, epsilon zero and constant degree-zero cases are explicit; p=1 is not asserted. This supplies (A21) on all finite dimensions and does not depend on the later Lp-prime bridge.

## Lp-prime bridge and final Boolean inequality

The premise in (A22) is an Lp-prime norm bound epsilon, not a density or squared norm. For h=f^(=j) with energy E>0 and established influences <=beta*E, reverse globalness and the pth root of (A21) give the displayed 210 exponent. The actual orthogonal pairing with f and Holder yield 420 after squaring. Division is confined to positive energy.

The explicit witness polynomial has coefficient norm at most 2^(3j). Lower-level induction consequently supplies every positive-order influence bound B=2^(500(j-1)^2*p+6j)*epsilon^2, through actual factorization of each derivative. The case split is essential and is present: E<=B closes directly; E>B establishes all influences <=E before applying duality with beta=1. Thus there is no circular desired-influence premise. The p=2 endpoint uses the forward conversion with squared parameter epsilon^2.

For the final matrix theorem, fixing a basis of the domain constraint and quotient rows for the codomain constraint represents the whole actual affine coset. Zero equations pad any order <=i to the nominal budget r without changing the conditional law. This works in rectangular and zero-dimensional spaces and gives the order-zero density bound as well. Booleanity then gives Lp-prime parameter delta^(1-1/p), influences 2^(500i^2*p)*delta^(2-2/p), and squared globalness 2^((10+500p)*i^2)*delta^(2-2/p).

The final moment exponent 450p^2-495p-10 and density exponent p-2+2/p agree with the exact algebra. Weakening uses 0<delta<=1 in the correct direction, followed by the pth root. Delta zero, i zero and unavailable ranks are explicitly handled. The separate exact-order convention is justified by affine coset partition only when its family exists; no full-function conclusion is drawn from a vacuous premise.

## Inverse application and claim boundary

The inverse lemma invokes exactly the proved binary specialization with delta=2e, requires e<=1/2, and chooses the dyadic P at least mT. Monotonicity of normalized probability norms allows the smaller exponent mT; no nondyadic theorem is asserted. The resulting bound (r+1)^m*2^(500mr^2 P+m)*e^(m-2/T) follows from P>=mT and e<=1/2. The matrix-lift input has the actual nominal restriction interface used in the appendix; basis invariance remains needed for the separate spectral application, not for the new hypercontractive theorem.

The only preappendix changes replace the remaining analytic import with this proved appendix and update the bridge-status sentence. A read-only exact text comparison confirmed that the inverse proof from `Require h>=r, e<=1/2` through the entire subsequent preappendix manuscript is unchanged. Thus the inverse constants, error absorption, dimension bounds, parameter order, downstream reductions and main theorem statements have not drifted in this increment.

This integration discharges the specified binary analytic import at the level of the supplied finite mathematical proof, using the separately reviewed lower chain through (A12). It does not discharge the other upstream PCP, compilation or learning contracts, and does not establish Lean formalization or a P-versus-NP result. The appendix explicitly preserves attribution and disclaims novelty and Lean verification. Existing PDF output has not been verified against this candidate and requires the separately routed build and visual review.
