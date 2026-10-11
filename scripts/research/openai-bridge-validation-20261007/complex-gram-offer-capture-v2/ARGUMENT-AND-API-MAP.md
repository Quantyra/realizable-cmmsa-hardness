# Literal complex two-function rank-Gram candidate

Status: v2 source-shaped candidate with routed static repairs. No Lean
compilation, GCP diagnostics, native certification, or independent review has
been performed for this offer. The v1 offer remains immutable and records the
pre-repair static findings.
The frozen dependencies below are exact captured bytes, but remain uncompiled
candidate dependencies.

## Target argument

Use the literal definitions in `ExactComplexAppendContinuation` and
`ExactComplexOperatorLaws`. For `F=f.re+i f.im` and `H=h.re+i h.im`, the
conjugate-first inner product has real part
`E[f.re*h.re + f.im*h.im]` and imaginary part
`E[f.re*h.im - f.im*h.re]`. The proof applies the real two-function
rank-Gram theorem four times (RR, II, RI, IR), then recombines those exact
component identities. This retains arbitrary invariant complex `F,H`, the
unrestricted append matrices, the original carrier normalizations and the
conjugate-first sign convention. Cross-rank orthogonality is separately
derived from four real cross-rank identities; it does not infer a bilinear
identity by polarization of a same-function result.

The all-rank theorem has no `i ≤ d` or `j ≤ d` premise. The eigenvalue is the
captured real `rankGramEigenvalue (c+s) s j` cast to `Complex`. At `s=0` its
product is empty and equals one; for `i>d` and `j>d`, the literal Fourier
rank filters are empty and the transported real projections vanish. The
append and finite means remain the exact definitions, including their
totalized division behavior.

## API mapping and dependency pins

* `complexRightInvariant_iff_components` transports paired-inverse right
  invariance in both directions; the new projection-invariance theorem then
  invokes the real rank-projection covariance theorem separately on re/im.
* `complexRankProjection_re/im` transports the literal complex Fourier
  projection to the real projection of each component.
* `complexAppendAverage_re/im` transports the literal unconditional append
  mean componentwise.
* `complexInnerProduct_re/im` supplies the conjugate-first RR+II and RI−IR
  formulas. The source adds real normalized-mean add/subtraction steps.
* Four calls to the frozen real `append_rank_two_function_gram` prove the
  complete arbitrary two-function complex Gram identity. Four calls to
  `rankProjection_cross_rank_inner_eq_zero` prove complex cross-rank
  orthogonality without invariance assumptions.
* The exact complex source pins supplied by root are:
  `ExactComplexAppendContinuation.lean`, 11,799 bytes,
  SHA-256 `0C9E6F1302137019BA430AD02E38DBA28664A93734B098D0A04C84440ECB0541`;
  `ExactComplexOperatorLaws.lean`, 6,073 bytes,
  SHA-256 `3ECB1956FF48159272E4A0320A4D0F794760790A99D866B387C4938439BC91C7`.
  Both were copied into `complex-operator-complete-offer-capture-v4` and
  root reports exact-byte verification. They are uncompiled and unaccepted.
* Real dependency: `ExactRealRankGram.lean` from
  `real-gram-offer-capture-v1`, 12,167 bytes, SHA-256
  `ff8981b60487a904f74f58903636fc7501e804247d5fdf45a8b9737f9246e06d`;
  `ExactRealRankGramChecks.lean`, 1,853 bytes, SHA-256
  `3153243ca433843841b76750e4e40a08bcca45e0b5f658752ab2a5ba5d1f47a5`.
  Root reports immutable capture and exact-byte verification. Both remain
  uncompiled and unaccepted.

The imported real theorem bodies transitively depend on the actual append,
G/Phi, restricted-adjoint, rank-projection, and Phi eigenrelation candidate
sources. This candidate introduces no axiom and does not certify those
dependencies. The separate `Checks.lean` contains fully qualified public
checks and fresh axiom requests; the requests have not been run.

## Open verification gaps

1. No source in this directory has been elaborated or compiled. Tactic/API
   compatibility and all proof obligations are therefore unresolved.
2. The exact real Gram offer and complex v4 offer are not native-certified
   dependencies. Their captured status is custody only.
3. No full-source GCP profile, import-closure trace, warning comparison,
   standard-axiom result, or independent three-lens review is supplied here.
4. Manuscript/caller alignment, novelty, runtime/source-witness and all
   broader certification gates remain outside this candidate.

No material theorem acceptance or manuscript claim follows from this offer.
