# Actual one-way leaf transport: complexity-theory review

Date: 2026-09-15  
Frozen source commit: `bba6dbb380fa5dde490c45fd7806ccb05aa1e8a8`  
Requested certification commit: `419d70a629a560f0bf9a358dc433fa76aaf9fbbb`  
Evidence-preservation replacement on `main`: `7e06ca3260b140cc7e0c58c22473f09d1b30f2a2`  
Canonical certification directory: `research/evidence/2026-09-15-actual-leaf-transport-fresh-run/`  
Verdict: **GO-WITH-NOTES**

This increment proves the conditional one-way label transport required by the MZ star construction for one pair of actual presented leaves. Its quantifiers and side conditions match the local content of MZ Lemma 3.4: after fixing two related presentations and a source label satisfying the source equations, there is a unique target label that is the restriction of a common extension respecting the target equations. This is force-bearing rather than generic packaging because it consumes the actual occurrence-allocation supports and RHS values, the actual `GoodQuestion` predicate, the actual presented-leaf domains, and the previously certified actual glued-functional theorem.

The increment does **not** establish that `PresentedLeaf.Rel` is an equivalence relation. In particular, transitivity is false for the bare submodule formula in general and needs the actual MZ incidence argument. It also does not yet lift transport from presentations to presentation-independent leaf vertices or prove identity, inverse, composition/coherence, repeated-address semantics, center restriction, sampling/stationarity, acceptance, hardness, or a reduction. Those are real remaining dependencies rather than consequences of this theorem's name.

## Frozen statements and quantifier audit

The relation is the manuscript relation written in terms of the already assembled domains:

```lean
def PresentedLeaf.Rel (P Q : PresentedLeaf I J h) : Prop :=
  P.domain ⊔ Q.H = Q.domain ⊔ P.H
```

Because `P.domain = P.L ⊔ P.H` and `Q.domain = Q.L ⊔ Q.H`, this is exactly

`L + H_U + H_U' = L' + H_U + H_U'`.

The module then defines compatibility by existence of a linear functional on `P.domain ⊔ Q.H` whose source restriction is `f`, whose values on the target equation vectors are the actual `I.rowRhs`, and whose target restriction is `g`. The exported result is:

```lean
theorem existsUnique_compatibleTransport
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    ∃! g : RawLeafLabel I Q.domain,
      RespectsAt Q rfl g ∧ TransportCompatible P Q hPQ f g
```

The quantifier order is correct. One actual source instance and fixed construction parameters `J,h` are implicit; `P,Q`, their relation witness, the source functional, and its source-RHS proof are arbitrary. The target functional is produced uniquely. No favorable target label, common extension, satisfying assignment, sampler outcome, or consistency conclusion is assumed.

`TransportCompatible` states the target-RHS part of the common extension explicitly. Its source-RHS part follows from the equality of the source restriction with `f` together with the separate premise `hf`. Thus the theorem matches MZ's requirement that the common extension respect both `U` and `U'`; it has not silently dropped the source equations. The separate conclusion `RespectsAt Q` is mathematically redundant given compatibility but is the useful typed output for the next consumer.

The proof uses `P.rightDomain_le_common Q hPQ` to restrict the unique glued functional to `Q.domain`. This is where the pair relation is genuinely consumed. The uniqueness theorem compares any compatible common extension against `actual_existsUnique_gluedLeafRhsFunctional`, then restricts that equality to the target. It does not derive uniqueness merely from target-RHS values.

Both presentations carry `GoodQuestion`, cardinality `J`, transverse `L`, and `finrank L = 2h`. The local proof only needs the actual glued-functional theorem plus the relation inclusion; the unused geometric fields remain legitimate carrier invariants required by later counting and sampling. `U` is presently a `Finset`, whereas MZ samples an ordered tuple. This loses no information for this algebraic transport statement, but the future representative sampler must recover the manuscript's ordered law and weights rather than infer a uniform-subset law from this module.

## Exact MZ and manuscript correspondence

The preserved MZ v1 text, SHA-256 `E8CB21FB8279F7881A5CF5C53B87B09B215F0BB3C8466B8FBDFCD4517EE5FBCE`, states in Section 3.3.3 and Lemma 3.4 that related leaves satisfy the displayed common-sum equality and that every source side-condition label has a unique target side-condition label admitting a common extension. The authoritative submission manuscript, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`, records the same imported contract at lines 171--183.

| Manuscript dependency | Frozen Lean evidence | Status after this increment |
|---|---|---|
| Pair relation `L+H_U+H_U' = L'+H_U+H_U'` | `PresentedLeaf.Rel` | Defined exactly |
| Target domain lies in the common extension domain | `PresentedLeaf.rightDomain_le_common` | Proved conditionally on `Rel` |
| Construct target label by common RHS-preserving extension | `transportedLabel` | Defined |
| Target label respects `U'` | `transportedLabel_respectsAt` | Proved |
| Constructed label has the required common extension | `transportedLabel_compatible` | Proved |
| Any compatible target label equals the constructed label | `transportedLabel_unique` | Proved |
| MZ Lemma 3.4 local existence and uniqueness | `existsUnique_compatibleTransport` | Proved for actual presented leaves |
| `Rel` reflexive, symmetric, and transitive | No theorem in this increment | Open; actual-incidence bridge required |
| Presentation-independent transport on `LeafVertex`/`LeafLabel` | No theorem in this increment | Open |
| Identity, inverse, and coherence | No theorem in this increment | Open |
| Repeated-address semantics and presentation descent for transport | No theorem in this increment | Open |
| Center restriction, representative sampler, and stationarity | No theorem in this increment | Open |
| Actual-star acceptance and all hardness/reduction claims | No theorem in this increment | Open |

The nonempty Checks fixture uses two distinct original-row questions in one actual occurrence-allocation instance. Their allocated three-variable supports are distinct even though the source owner data repeat, the source RHS is nonzero, and the target type is not definitionally the source type. It invokes the exact exported existence/uniqueness theorem and separately checks target RHS preservation. The empty fixture checks the `J=0,h=0` boundary. These are meaningful signature fixtures; they are not evidence for relation transitivity, sampler behavior, or acceptance probability.

## Why the relation bridge remains open

Reflexivity and symmetry follow readily from the displayed equality, but transitivity is not a generic lattice fact. A concrete abstract counterexample can be built with one-dimensional `H_i ≤ D_i` and two-dimensional `D_i`: take

`D_P=⟨e1,e2⟩, H_P=⟨e1⟩`,  
`D_Q=⟨e2,e3⟩, H_Q=⟨e3⟩`,  
`D_R=⟨e4,e2+e3⟩, H_R=⟨e4⟩`.

Then `P Rel Q` and `Q Rel R`, while `P Rel R` fails. Adding a common direct summand gives the same failure with leaf-domain complement dimension `2h`. Therefore a proof of `Rel.trans` cannot come from generic `sup` algebra or from the one-way transport theorem. The next force-bearing theorem must use the actual incidence representation, including the retained-question no-cross structure/private-coordinate mechanism, to instantiate MZ Lemma 3.3. Only after that bridge is available is it sound to define cliques and prove transport identity, inverse, and coherence.

## Claims boundary

This increment does not prove:

- a generic equivalence relation on arbitrary submodule presentations;
- the actual-incidence transitivity theorem or a finite clique partition;
- that transport is independent of presentation or of the proof of `Rel`;
- identity, inverse, composition, path independence, or repeated-address equality;
- the alphabet cardinality `2^(2h)`;
- center-label restriction or any distribution on representatives;
- uniformity or stationarity of clique resampling;
- actual-star completeness, acceptance, soundness, or value preservation;
- outer source hardness, the HN compiler, an encoded randomized polynomial-time reduction, fixed-`L` asymptotics, NP-hardness, `P = NP`, or `P ≠ NP`.

The next manuscript consumer is the actual-incidence equivalence bridge. The remaining headline path is:

```text
actual-incidence Rel transitivity / clique equivalence
  → identity, inverse, and proof-independent coherence
  → presentation descent and repeated-address semantics
  → center restriction
  → representative sampler and stationarity
  → actual-star acceptance
  → outer soundness and source hardness
  → reduction, runtime, and fixed-L asymptotics
  → manuscript reconciliation and release package
```

## Certification, provenance, and cloud audit

The requested certification commit `419d70a` is a sibling of the current `main` certification commit `7e06ca3`, both directly based on frozen source commit `bba6dbb`. The current `main` replacement adds the raw logs and a corrected local preservation manifest; it does not change the source commit, frozen hashes, stage outcomes, object hashes, transfer receipt, cost receipt, or cloud state. The authoritative ledger should name `7e06ca3` as the preserved certification commit and retain `419d70a` only as the superseded receipt identifier, avoiding two apparent canonical certifications for one source.

I independently rehashed the current retained artifact manifest: all **144** rows exist and match, with zero mismatches. `artifact-hashes.txt` has SHA-256 `0BD43BFD1113C6C8DB98230AB66061EFA1B67500BAAF33DD4C93ACC237EDF41E`, matching its manifest. The original `419d70a` receipt reported 143 matching rows with manifest `F6132331A74C0560C18156360AA0BBCD64EF82691A64C9F0BA702AD540F59BA3`; the replacement is the independently reproducible retained form.

| Artifact | SHA-256 |
|---|---|
| `ActualLeafTransport.lean` | `F1548559AE3135E8F75F2E8C255B530582DDEFA2E6D58AE02FC53C02460EE3E8` |
| `ActualLeafTransportChecks.lean` | `D9BF5ED9B8CDCA2431584B4577C4C8BEE3011A82DC23FD819B02C22F96FBC3D9` |
| Fresh Linux main object | `1CEE9647728163F2BBC71D6AA429BEFD78AA1883BB24CDE9A307A060B6465AE2` |
| Fresh Linux Checks object | `C015F98C7F2172C704216A87A7E415AD832964FD899D3D4FFB5EB92D511C7FF2` |

The transfer gate checked identical local and remote bundle SHA-256 `2738FFBE05550A5858D9CB1F4474D1DB1A14DDA736E2723BCFF62DA9188A9313`, a clean detached checkout at `bba6dbb`, the two frozen source hashes, and 40 source-stability assertions before, between, and after stages. The returned archive hashes match at `AF6E14AC898E91581D243FACA7B2FECDE92E68793E226EBDFC75D806C6BFE3DF`. The remote evidence manifest is `8A65E548F77536078D40FFBA7D61640ADD45E4A2D630BF47BFF6CEECEE6A1E3B`, 129 rows with zero mismatches.

The target-fresh cloud build used Lean `4.34.0-rc2`, rebuilt the complete 16-module reachable project-source closure, then main and Checks; all 18 stages exited `0`. The final syntax-aware forbidden-token scan is clean. Printed theorem profiles contain only `propext`, `Classical.choice`, and `Quot.sound`. Main took 2.04 seconds and Checks 16.30 seconds; peak RSS was 3,481,316 KiB. Cross-platform object bytes differ from the Windows cached objects, and the receipt correctly treats that as informational rather than a certification failure.

The builder was one `c3-highmem-8` instance, inside the authorized 8-vCPU/64-GiB boundary. The evidence records no external IP, IAP-only SSH, VM state **TERMINATED**, increment estimate **$0.096222**, and cumulative estimated GCP spend **$0.436993**, leaving **$249.563007** below the $250 ceiling. The retained 200-GiB balanced disk remains `READY` and accrues an estimated **$0.657533/day** while the VM is stopped.

## Disposition

**GO-WITH-NOTES.** Accept `bba6dbb` as the canonical conditional one-way transport increment, with `7e06ca3` as its retained certification evidence. The theorem exactly discharges the local MZ Lemma 3.4 existence/uniqueness obligation for a supplied related pair of actual presentations and a supplied source RHS label. It must not be recorded as MZ Lemma 3.3, as clique equivalence, or as coherent/presentation-independent transport. Table-ready note: **conditional actual one-way leaf transport is certified; the actual-incidence equivalence bridge, transport laws/descent, repeated-address semantics, sampling/stationarity, acceptance, and all hardness claims remain open.**
