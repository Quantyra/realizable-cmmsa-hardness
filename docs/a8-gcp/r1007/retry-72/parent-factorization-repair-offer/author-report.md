# Retry-72 ParentFactorization repair offer

This is a fresh source-only successor to the immutable retry-71 offer. The Checks file is unchanged byte-for-byte from retry-71; the retry-71 path and all earlier captures remain untouched.

The source changes address the complete 13-error retry-72 ParentFactorization packet and the single owned unused-simp warning. They add an instance-irrelevance lemma for `a18UniformMean` using the captured `Subsingleton (Fintype ?)` API; normalize mismatched mean endpoints before transitivity; add explicit linear-equivalence type annotations; unfold the local `f0` when proving its pointwise source identity; normalize let-bound top/bottom finrank proofs without rewriting local values as proof names; simplify the quotient kernel in the hyperplane endpoint; and annotate the two line/hyperplane filter map binders. The unused `LinearEquiv.coe_toLinearMap` simp argument was removed.

Public theorem statements, premises, strict lower-induction dependency, endpoint inequalities, and options are unchanged. No axiom, sorry, heartbeat change, carrier redesign, or current-level oracle was added. This report records authoring and source inspection only; Sol owns remote compiler/Git verification and will report the next captured diagnostics.

The source was written UTF-8 without BOM and checked for malformed placeholders and remaining `?` characters. No local Lean, Lake, or Elan command was run; no Git command was run.

## SHA-256

- ParentFactorization source: `AFAFBFF448DF4F370FE21FAE5396C3DA2BABBECC70528B07850765CB0FAF24D7`
- Unchanged Checks file: `FF0B1F32E7581F0893A3D08DDEE8A0139AA59E45F12FF720B773E2915BFDB7D6`
- Unified diff against immutable retry-71/E4BB source: `A3CD9F8CED6E7808A07FC5E846A0B0EC915508AB05E87DBBFA6662838BFF3C1E`
