# Independent proof-adversarial review

Verdict: **GO-WITH-NOTES** for the exact ambient fixed-final A9 carrier, its two-sided section/extension equivalence, rank/A8 incidence correspondence, and stated cardinality. **No blocking mathematical defect found in that scope.** This is one completed review lens, not Root acceptance of the milestone, closure of S3132, or certification of S3137.

Review date: 2026-10-04. Reviewer role: `proof-adversarial-reviewer`, independent top-level review. No delegation or sub-agents.

## Exact scope and identity

Repository: `C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness`.

| Artifact | SHA-256 independently verified |
| --- | --- |
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientFiber.lean` | `024850F649001829158FF0AB474CBFB7D8B228F6695EF673CB9EDF2D311226F9` |
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientFiberChecks.lean` | `C9C59633F0F34AA91CF28A47665AA78D3438406B63434796AB685C74181F3989` |

All candidate line references below refer to these exact source bytes. Reviewed the complete candidate and Checks, the mathematical dependencies used for its Grassmann and affine-map counts, the retained compiler evidence, the ambient definition decision, relevant manuscript A8/A9 text, and planning acceptance context.

Principal declarations reviewed: `A9AmbientInitialDatum`, `A9AmbientFixedFinalFiber`, `A9AmbientSectionExtensionCarrier`, `a9Ambient_section_existsUnique`, `a9AmbientForward`, `a9AmbientInverse`, `a9AmbientFiberEquiv`, both exported inverse laws, `a9Ambient_A8_sideConditions_iff_rank_preservation`, `a9Ambient_fiber_A8_sideConditions`, the section/extension and nested-`B0` cardinality theorems, Gaussian symmetry, and `a9_ambient_fiber_card`.

## What the theorem actually counts

Work over `F = ZMod 2`. Fix ambient modules `V,W`, subspaces `A ≤ V`, `B ≤ W`, and the actual map `Y : B →ₗ[F] V/A`. The fiber consists of triples satisfying

\[
A_0\le A,\quad \dim A_0=i;\qquad
B\le B_0\le W,\quad \dim(W/B_0)=j;\qquad
X:B_0\longrightarrow V/A_0,
\]

\[
q_{A_0,A}\circ X\circ\iota_{B,B_0}=Y,
\qquad \operatorname{rank}X=k.
\]

These are actual ambient subspaces and maps, not graph coordinates relabeled as ambient data. The fixed-final equation is a field of the initial datum (lines 124–142). `a9AmbientQuotientMap` is induced by the quotient maps, and `a9AmbientBIncl_toAmbient` establishes the inclusion's actual ambient meaning (lines 84–119).

For the equivalence, the additional hypothesis is `rank Y = k`. For the final count, the hypotheses also identify `a = dim A`, `b = dim(W/B)`, and require `i ≤ a`, `j ≤ b`, with the displayed finite/free/Fintype module instances. The asserted result is exactly

\[
|\mathcal F^{i,j}_{A,B}(Y)|
=\genfrac{[}{]}{0pt}{}{a}{i}_2
 \genfrac{[}{]}{0pt}{}{b}{j}_2
 2^{k(a-i)}2^{k(b-j)}.
\]

It is a census for a supplied fixed `Y` of rank `k`, not a sum over all final frequencies. It does not supply the analytic reindexing theorem or any bound on a general complex input.

## Mathematical audit

### Vacuity and hypotheses

**Pass.** There is no contradiction premise, assumed equivalence/count, or postulated inverse law. The fixed-final equation restricts the carrier legitimately. The rank premise is substantive and visible; finite-dimensional hypotheses prevent misuse of `finrank` on infinite-dimensional spaces. Over `F₂`, the free-module assumptions are compatible with the intended finite vector spaces. Necessary upper bounds on `rank Y` follow from the supplied map and need not be separately assumed.

The permitted parameter range is nonvacuous. For each allowed subspace pair, the quotient is surjective and admits a linear lift of `range Y`; the restriction `Y.rangeRestrict` extends from `B` to `B0`. A section is injective and an extension is surjective onto `range Y`, so their composite gives an actual rank-`k` member. Subspaces of the permitted dimensions exist in the relevant finite spaces. At `k = 0`, `Y = 0`, both affine factors are singletons, and the census reduces to the two subspace counts.

As an independent check, a read-only Python GF(2) enumeration used actual subspaces, quotient cosets, and all linear maps; it did not import or execute Lean. It checked both inverse directions and the formula in 11 finite cases:

- `V=W=F₂²`, `A=B=span(e1)`, `Y(e1)=e2+A`, `i=j=0`, `k=1`: four actual triples and four section/extension pairs.
- `V=W=F₂³`, `A=span(e1,e2)`, `B=span(e1)`, `Y(e1)=e3+A`, `k=1`: for all nine `(i,j)` in `{0,1,2}²`, the counts were respectively `16,24,4; 24,36,6; 4,6,1`, agreeing with the formula and both inverse laws.
- The same three-dimensional subspaces with `Y=0`, `i=j=1`, `k=0`: nine triples and nine pairs.

These fixtures establish concrete satisfiable instances and provide finite sanity checks. They are not substitutes for the general argument or kernel evidence; no fixture artifact or test source was written.

The rank premise must remain attached to every application. For example, with `V=W=F₂²`, `A=B=span(e1)`, `A0=0`, `B0=W`, `Y=0`, and `X(e1)=0`, `X(e2)=e1`, the fixed-final equation holds but `rank X=1>rank Y=0`; both A8 incidence equalities fail. The candidate does not claim its equivalence or fiber-side-condition theorem for this mismatched rank case.

### Canonical factorization and inverse-law fidelity

**Pass.** Put `g = X ∘ inclusion(B,B0)` and `q = q_(A0,A)`. The fixed-final equation gives `qg=Y`. Consequently

\[
\operatorname{rank}Y\le\operatorname{rank}g\le\operatorname{rank}X=k.
\]

Under `rank Y=k`, both inequalities are equalities. Finite-dimensionality then gives `range g = range X`. The quotient restricted to this image has image `range Y` and zero kernel by rank-nullity. These are proved in lines 361–441 and used in lines 446–530; they are not missing assumptions hidden in a choice operation.

The forward section `ell : range Y → V/A0` is the unique section satisfying **both** `q ∘ ell = subtype` and `ell ∘ Y.rangeRestrict = g`. Uniqueness is relative to the predecessor `X`, not a claim that the entire affine section fiber is a singleton. Surjectivity of `Y.rangeRestrict` proves uniqueness. The forward extension is `q ∘ X` with its codomain restricted to `range Y`. The equality of images above makes that codomain restriction well-defined.

The inverse sets `X = ell ∘ psi` (lines 597–645). It proves the actual final equation using the two prescribed restrictions. Applying `q` proves `ell` injective; the restriction of `psi` to `B` is already onto `range Y`, so `psi` is surjective. Hence the composite has rank exactly `k`, without an extra genericity or compatibility premise.

Both round trips recover the original data:

- `inverse(forward(x)) = x`: the source reconstructs `X` pointwise using `range g = range X`, and retains the same `A0,B0` (lines 557–592, 716–735).
- `forward(inverse(c)) = c`: uniqueness recovers the supplied section, and the section equation recovers the supplied extension (lines 676–713).

The exported inverse laws at lines 752–770 inherit these proved equivalence fields. Equality of the dependent sigma/subtype data is genuine equality; proof irrelevance removes only proposition witnesses, not subspaces or map values. The fixed `(A,B,Y)` stays in the types throughout. `a9AmbientInverse_map` and `a9AmbientInverse_factorization` expose respectively the composite and retained final equation.

### A8 correspondence and statement/proof alignment

**Pass for the stated incidence correspondence.** `a9AmbientImageLift` is the preimage of `range X` under `V → V/A0`; `a9AmbientKernelInW` embeds the actual kernel from `B0` into `W`. Thus the predicates are precisely

\[
A\cap A_1=A_0,\qquad B+\ker X=B_0.
\]

Lines 774–891 prove the second equality equivalent to `X(B)=X(B0)`, and the first equivalent to injectivity of the quotient on `range X`. Lines 894–975 prove their conjunction equivalent to preservation of rank by quotient-after-restriction. Both implications are present. Lines 979–987 apply this to every fiber member with the stated final-rank hypothesis.

This matches the selector geometry and quotient convention in `paper/body.tex:1279–1309` and the approved `docs/a7-certification-20261003/a9-ambient-definition-decision.md`. The candidate delivers the fixed-final combinatorial obligation described there. The `A8` names do not mean it proves the analytic inequality labeled (A8), its shift/Fubini transport, or its downstream use.

### Cardinality and variance

**Pass.** Each numerical factor has a faithful carrier explanation:

| Factor | Carrier and argument |
| --- | --- |
| `w6Gaussian a i` | Actual `A0 ≤ A` of dimension `i`, transported by subtype map/comap to `W6Grass A i` (lines 60–82). |
| `2^(k*(a-i))` | Affine sections of `q`; after choosing one base lift, their differences are all maps `range Y → ker q`. Rank-nullity and the two quotient dimensions give `dim ker q = a-i` (lines 239–269, 992–1033). |
| `w6Gaussian b j` | Actual containing `B0`, represented by `B0/B ≤ W/B` of dimension **`b-j`**, with inverse the preimage under `W → W/B`. Gaussian symmetry changes the scalar count to `[b choose j]₂` (lines 1089–1206). |
| `2^(k*(b-j))` | Affine extensions of `Y.rangeRestrict`; differences factor uniquely through the actual quotient `B0/(B.comap B0.subtype)`, whose dimension is `b-j` (lines 273–332, 1038–1084). |

The `B`-side variance is correct: the difference maps go **from** `B0/B` **to** `range Y`. The annihilator/coannihilator argument is confined to numerical Gaussian symmetry. It does not identify `B0/B` with its dual or turn it into a dimension-`j` domain for an extension map.

The section and extension fibers are affine fibers, not unconstrained map spaces. Their basepoints are proved to exist, and their translation equivalences have both inverse laws. Any section/extension pair reconstructs a valid `X`, so multiplying these independent fiber counts requires no additional compatibility factor. No `GL(k)` or basis factor belongs in the answer: `Y` itself is fixed, and the section/extension equations fix the labeling of its image.

The final proof (lines 1221–1249) transfers cardinality through the proved ambient equivalence and sums the product over the dependent subspace choices. It does not invoke the normalized actual-fiber count as a replacement for an ambient theorem.

The inherited `w6Gaussian` is independently grounded in the frame double count: `ActualBinaryMatrixHC46A7PredecessorCount.lean:645–798` defines the Grassmann carrier, ordered frames, positive frame denominator, exact double count and Gaussian quotient. Its mathlib `card_linearIndependent` dependency counts frames, rather than assuming the desired Gaussian result. Thus no unproved division/integrality or out-of-range cardinality premise is smuggled into the final formula.

### Axiom leakage and choice

**Pass within the recorded profile scope.** Checks lines 46–50 request profiles for the ambient equivalence, section count, extension count, nested-`B0` count and final count. The retained fresh output prints each with exactly `propext`, `Classical.choice`, and `Quot.sound`; none includes `sorryAx`, a new theorem axiom, or a native-decision axiom. Static inspection found no executable `sorry`, `admit`, new axiom, or `native_decide` in the candidate or captured project source closure; the keyword-search hits in that closure were comments.

This is standard classical Lean mathematics, not an axiom-free or constructive algorithm claim. `Classical.choose` in the forward map selects a uniquely specified factor. Arbitrary right inverses, extensions and bases appear as auxiliary devices for counting (notably lines 1007–1019 and 1052–1069), and can change the translation coordinates. They do not define the ambient carrier or its canonical predecessor/factor round trips. Acceptance must preserve that distinction. Five printed roots do not constitute an individually printed axiom audit of every declaration; the remaining A8 correspondence was also inspected at source level.

## Compiler evidence, identities, and acceptance status

Use these repository-relative evidence roots:

- `R = docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z/runs/cmmsa_a9_ambient_20261004T090505Z_189bd32b`
- `C = docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z/compiler-repair-20261004T090127Z`
- `I = docs/a7-certification-20261003/a9-ambient-gcp/session-20261004T062223Z/captures/capture-compiler-repair-20261004T090127Z/inputs`

Read `C/report.txt`, `C/report.json`, `C/source-repair.diff`, `R/audit.json`, all four `R/remote-evidence/stage-N.command.json` records, their terminal exits and fresh Checks output. Independently recomputed the stdout/stderr hashes for all four stages and matched `C/report.json`. Stage exits were `0/0/0/0`; errors and unsolved goals were zero. Warning occurrences were `748/761/761/1`. These are repeated stage occurrences, not 2271 distinct proof defects. The source/Checks stages include 13 pre-existing owned style warnings; the fresh-stage stderr warns of the captured cslib repository's local changes.

The compiler is recorded as Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, executable SHA-256 `E8BAAA71855A616DC351028F3AD2200051B0671F423A1696A100E809302D5550`. No compiler was invoked by this reviewer.

Identity checks performed:

- Current candidate/Checks match `C/source-after.lean.snapshot` and `C/checks-before.lean.snapshot` and the remote source inventory.
- All 166 entries in `R/remote-evidence/source-before.json`—163 Lean files and three configuration files—match both the retained capture under `I` and the current workspace. Remote before/after source inventories are equal.
- Input archive SHA-256: `FF69B8CF61F03C3BBBE51C47D537B5E0DA5AB66945E89FA9E4478B9998992DB4`.
- Evidence archive SHA-256: `7577C17AD2586768A55BA7F2F5815B54230AA0AB7C6CF97C4F3E95A018498280`.

Relevant project dependency identities from the matched inventory:

| Dependency | SHA-256 |
| --- | --- |
| `ActualBinaryMatrixHC46A7PredecessorCount.lean` | `8D8AF4E559179D081E58330ACA37DED52430CEE717294C5DEAF444348B982F64` |
| `ActualBinaryMatrixHC46A9InitialGraph.lean` | `BF06040FF7C849A6F26B2BD15602AEEE7939CF8A8D4045BF850BF3102EC0A903` |
| `ActualBinaryMatrixHC46A9ActualFiber.lean` | `906E8E84E99333DB286BF8431B9D274CF1D5DD32045B953993F6CE7E23EDF223` |

Reviewed relevant mathlib source bytes directly inside `R/remote-evidence/package-sources.tar.gz`, without filesystem extraction, and checked their hashes against `package-source-hashes.json`: `FieldTheory/Finiteness.lean`, `Algebra/Module/Projective.lean`, `LinearAlgebra/Basis/VectorSpace.lean`, `LinearAlgebra/FreeModule/Finite/Matrix.lean`, `LinearAlgebra/Dual/Lemmas.lean`, and `LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean`. These supply the vector-space cardinality, linear-map dimension, lifting/extension, annihilator and frame-count facts used here. This review does not assert that every dependency repository was a pristine upstream checkout.

**Compiler evidence and mathematical acceptance are separate.** The retained GCP results support elaboration/kernel acceptance of these exact declarations under the captured dependency graph. The argument audit above supports their intended bounded mathematical meaning. Neither substitutes for the other or for the remaining review lenses.

The executed legacy audit remains `green=false`, `certified=false`, with the sole failure `Warnings/errors/unsolved goals are not all zero`. It has not been rewritten. `C/report.txt` predates the later planning decision and therefore still labels the strict bounded-increment gate unaccepted. The subsequent milestone context in `C:\Users\Dan\Desktop\Projects\IGH\Quantyra-Planning\stories\S3126-realizable-hardness-formal-proof-and-paper.md:3266–3276` makes this exact compiler-green candidate eligible for review under the warning-baseline/no-regression decision, retaining 748 inherited dependency warnings and 13 pre-existing owned warnings as separate S3137 certification debt. This review follows that context and does not declare the legacy audit green or clear warning debt.

## Notes, blockers, and claims boundary

**Blocking findings for the exact bounded mathematical candidate: none.** GO-WITH-NOTES reflects the following material limits, not an unresolved inverse or cardinality gap:

1. Preserve all rank, finite-module and index-range hypotheses. The fiber abbreviation itself permits a separate `k`; its equivalence and A8 consequences require the supplied equality `rank Y=k`.
2. Canonical carrier/factorization does not mean choice-free counting coordinates or a constructive polynomial-time procedure. The temporary affine origins are auxiliary choices.
3. This result proves the ambient fixed-final census and A8 incidence/rank correspondence. It does not construct a canonical equivalence with the older normalized graph carrier. That older result is imported but is not used to stand in for this count.
4. Analytic A9 reindexing into the actual sums, the analytic (A8) inequality, A11/W6, positive-degree A7, outward HC46/support, encoded reduction/runtime, Theorem 1 and Corollary 2, full-manuscript assembly, final reviews and warning debt remain outside this acceptance. A missing degree premise `a+b+k≤D` is not a defect in this unrestricted finite census; it must be proved where an analytic application needs it.

S3132 remains partial/open pending Root's milestone decision and all required lenses. S3137 remains incomplete/not certified. The three-lens protocol read was `C:\Users\Dan\Desktop\Projects\IGH\Quantyra-Planning\docs\formal-three-lens-closeout-protocol.md`; this report supplies only its proof-adversarial lens. No public hardness, learning, P-versus-NP, route-final, or release claim is supported by this report.

Only this requested report was written. No Lean/source/Checks, warning evidence, planning document, index, commit, push, or cloud resource was changed; no Lean/Lake/elan execution or delegation occurred. Existing worktree dirt was preserved.
