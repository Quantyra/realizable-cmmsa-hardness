# Rectangular GL completion and finite marginal step

Status: this original v2 map is superseded on rectangular completion and
row-prefix marginal by the later addenda in this directory. All Lean sources
remain uncompiled candidates; no helper acceptance is claimed.

## Pinned source/API findings

The following source bodies were read from `full107-trace-qualified-source-record-v1/review-sources` and cross-pinned against Full109's package source hash ledger (`full109-qualified-native-record-v1/079-package-source-hashes.json`). These are source identities, not fresh build evidence.

| API/body | Exact source SHA-256 | Relevant declaration |
|---|---|---|
| `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean` | `AC31F64E47BA76F80C1C9BAB4E58645175A13C23C9175449C41ACD22B1E44F1F` | `card_linearIndependent`, `Matrix.equiv_GL_linearindependent`, `Matrix.card_GL_field` |
| `Mathlib/LinearAlgebra/Basis/VectorSpace.lean` | `CDBE0FD512F13EA3E563290D2896C89E3882ED0040ECC7C3314676A8F278728A` | `Basis.sumExtend`, `Basis.extend`, `LinearMap.exists_extend` |
| `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean` | `A3E88C4FE00BA476440D68A1568AFECF6BE685A488B5B8718F6B2EF969A15FA4` | `Module.finrank_eq_card_basis'` |
| `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` | `FD2F40B42AAC48256B11C2A395DB0544CD441B04A9F75350D7C46F353FC7D912` | `basisOfPiSpaceOfLinearIndependent`, `coe_basisOfPiSpaceOfLinearIndependent` |
| `Mathlib/Data/Fintype/EquivFin.lean` | `891FDB687FC067B1511701992301E28DE0D4FD6AB53D74A96F51BE39D5AA8F92` | `Fintype.equivOfCardEq` |
| `ActualFixedFunctionalAppendOperator.lean` pinned Full107 body | `EB71A55A38E8922333058F0D05D8E48472003AAA9BEE2B9F01A9DE00668A7B77` | actual unrestricted `appendAverage`, ordered `appendBinaryMatrixEquiv` |
| `0604-ActualAppendFourierCrossLevelOrthogonality.lean` Full107 body | `AE8D620F887E45B9B4445375640E5EB3AE54C5B56A81186DF77B6FC55D741652` | actual `appendAverage_character`, cross-level orthogonality |

Full109 itself records native GREEN for 348 sources / 261 requested profiles / seven stages. Its cross-level identity trace and review are still pending per the current handoff, so this candidate does not reuse that identity as accepted evidence.

## Candidate finite argument

For a finite map `f : A → B`, write `F_b={a | f a=b}`. The sigma type
`Σ b, F_b` is equivalent to `A`, with maps `⟨b,⟨a,h⟩⟩ ↦ a` and
`a ↦ ⟨f a,⟨a,rfl⟩⟩`; the two inverse laws use the stored equality exactly.
If every fiber has cardinal `k`, grouping the finite sum by this sigma
equivalence yields
`sum_a g(f a) = k * sum_b g(b)` and `card A = card B * k`. For positive `k`
and nonempty `B`, both finite normalizers are nonzero, and field cancellation
gives equality of the uniform means. No conditional draw or altered measure
appears. The code includes both directions of the sigma-fiber equivalence and
the explicit denominator nonzero steps.

Mathlib's `card_linearIndependent` counts ordered independent families in any
finite-dimensional binary space by the exact `frameProduct` formula. The
Full109-pinned `GrassmannCounting.card_frame` already packages it for the
binary coordinate carrier; the candidate directly specializes that API.
Its `c=0` frame-count candidate simplifies to one, preserving the
empty-prefix case.

## Rectangular GL marginal: exact remaining composition

For `d=c+s`, define the first-column map
`q : GL(Fin d, F2) → Frame(Fin d → F2,c)` by restricting the columns of
`Matrix.equiv_GL_linearindependent d U` along `Fin.castAdd s`. The desired
identity is

`E_{U uniform GL(d,2)} g(q(U)) = E_{R uniform Frame(d,c)} g(R)`.

It follows from the candidate finite-fibre mean lemma once two facts are supplied:

1. `q` is surjective: extend an arbitrary independent c-frame to a basis using
   `Basis.sumExtend`; show its complement index has cardinal s by
   `Module.finrank_eq_card_basis'` and `Module.finrank_fintype_fun_eq_card`;
   choose the complement equivalence with `Fintype.equivOfCardEq`; reindex the
   completed basis along `finSumFinEquiv`; map the resulting full independent
   d-frame back to `GL(d,2)` with `Matrix.equiv_GL_linearindependent.symm`.
2. All fibers of q are equivalent: for frames R,R', choose the completions U0,
   U1 above. Left multiplication by `U1*U0⁻¹` maps the fiber over R bijectively
   to the fiber over R'; its inverse is left multiplication by the inverse.
   The first-column compatibility is matrix multiplication on each standard
   basis vector. This proof uses equal-size fibers, not an unproved numerical
   completion count.

The cited Mathlib declarations exist and their pinned bodies were inspected.
The missing item is the project-level composition theorem connecting
`Basis.sumExtend`'s `Fin c ⊕ complement` basis to the matrix-column frame and
the GL prefix map, with both inverse/fiber laws. Neither Full109's native
project sources nor Full107's reviewed project bodies contain this rectangular
completion/marginal theorem. The candidate proves the finite sum/cardinality
step that consumes it, but does not claim that the above composition has been
formally discharged.

Next action is to author `extendFrameToGL` and `prefixFiberEquiv` against these
exact pinned APIs, then apply
`uniformMean_map_of_equipotent_fibers`. G/Phi, Phi's pointwise eigenrelation,
and the restricted-adjoint proof remain open. Phi's eigenrelation target is
for arbitrary real F; invariance is required only for G(TF) and the restricted
adjoint. No Lean/Lake/elan, GCP, Git, network, or provider action was run.

Remaining to-do list: prove the basis-to-GL rectangular completion and
fiber-equivalence steps including c=0 and s=0; connect the matrix frame to
the actual operator subtype; then translate G/Phi/eigenrelation/restricted
adjoint and run GCP plus required trace/reviews.
