# MZ standing assumptions and actual application

S3126/S3132/E004, primary-source application audit; no Lean edits or compilation. This supplements the preceding conditions note, not its independent three-lens review.

## Primary context

Freshly inspected [MZ arXiv:2510.23991v1, §4 and §4.2](https://arxiv.org/html/2510.23991v1#S4). Lemma 4.1 starts with positive rho and sufficiently large h, and fixes subspace sets of widths 2h and 2(1−rho)h. Section 4.2 explicitly carries those sets into its matrix calculation. Consequently its append widths must be integral and geometrically realizable; no rounding convention is supplied. Positive rho and valid center width imply a positive append width, with center width nonnegative.

Its L2 inner product uses uniform matrix expectation and complex conjugation. The local real-function specialization removes conjugation legitimately. Basis invariance means invariance under every full-rank square right factor, for all input matrices. Equation (7) occurs under Lemma 4.8's basis-invariant indicator hypotheses. Its argument uses the adjoint/composition identities and rank-degree preservation from MZ24 A.10–A.13. Arbitrary-function post-append orthogonality is not asserted there.

The displayed 4.6/4.7 statements give no explicit numerical lower bound on n. Their inherited MZ24/EKL prerequisites were not independently reconstructed in this follow-up. Do not infer unrestricted ambient applicability from that omission, or invent a cutoff from memory.

## Actual source mapping

| Fact inspected | Established mapping / caller obligation |
| --- | --- |
| `ActualTaggedComplementInverseInput.complement_weight_ratios`, line 84 | `sideComplement_finrank I copies U A` proves complement ambient dimension **2J**. The original tagged U ambient dimension must not be substituted for this complement dimension. |
| Same module's transported tables and ordinary matching masses | Center rank is **t**, leaf rank **2h**, so matrix c=t and s=2h−t once ht:t≤2h is supplied. Generic consumer retains positive increment and ambient guards. |
| `ActualStarFixedRhoDimensionGuard.leafT`, `leafK`, `badExponent` | Intended selected c=leafT m h, s=leafK m h, with h=hBlock L m and J=blocks A h. Exact rational rho identification additionally requires actual divisibility and fixedRho reciprocal identity; generic table consumer alone does not specialize these. |
| `ActualFixedFunctionalAppendOperator.appendAverage`, line 261 | Coordinate ambient is `Fin n→ZMod 2`; its mean has no rank conditioning. Existing acceptance covers this coordinate carrier, not an automatic linear-equivalence transport from every complement A. |
| Complement-to-coordinate application | A caller still needs an explicit linear equivalence A≃ₗFin(2J)→ZMod 2, transport of the SAME C/T/f, and preservation of Grassmann uniform laws/matching masses. Finrank equality alone is not that transport theorem. |
| Source spectral application | Supply even total width 2h, integral c/s and actual right-basis invariance. Any selected ambient cutoff or `hsmall` estimate remains a separate local arithmetic proof. Post-level orthogonality needs its own exact proof, currently Luna-owned. |

The source-context audit does not settle hidden hypotheses of the cited MZ24 append/adjoint results. That is the precise remaining provenance obligation before claiming a maximally general spectral subcontract. It does not obstruct a conservatively parameterized contract whose explicit dimensional premises are recorded and proved at the intended caller. No analytic moment upper bound, inverse, robust-8S result, external-contract inhabitant, or core certification is supplied here.
