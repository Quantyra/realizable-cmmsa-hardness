# Actual presented-leaf gluing: complexity-theory review

Date: 2026-09-15  
Frozen source commit: `e599567a629f6e4eb960b4b2543960095293d1d3`  
Certification commit: `6422609d04c6632035892431b7c77af0b6db7b08`  
Canonical certification directory: `research/evidence/2026-09-15-actual-presented-leaf-gluing-fresh-run/`  
Verdict: **GO-WITH-NOTES**

This increment is force-bearing for the manuscript's star-transport route. It realizes the actual-source leaf presentation, makes the label side condition independent of the presentation of a fixed leaf domain, and constructs the unique RHS-compatible functional on the exact next domain `D ⊔ H_U'`. It therefore advances beyond a carrier-only or generic-algebra increment. It does not yet define the leaf equivalence relation or its transport map, and it supplies none of the later stationarity, acceptance, hardness, reduction, or `P`-versus-`NP` conclusions.

## Frozen declarations reviewed

The actual-source presentation is

```lean
structure PresentedLeaf
    (I : ActualOccurrenceAllocation.Instance N m) (J h : Nat) where
  U : Finset I.RowId
  goodU : GoodQuestion I.support U
  card_U : U.card = J
  L : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)
  L_le : L ≤ coordinateSpace I.support U
  finrank_L : Module.finrank (ZMod 2) L = 2 * h
  transverse : L ⊓ equationSpan I.support U = ⊥
```

with `P.H := equationSpan I.support P.U` and `P.domain := P.L ⊔ P.H`. Thus the Lean object records exactly the manuscript's actual-source data `D = L + H_U`, `dim L = 2h`, and `L ∩ H_U = {0}`, as well as the retained-question size and admissibility conditions. `RawLeafLabel I D` is a linear functional `D →ₗ[ZMod 2] ZMod 2`. `RespectsAt P hD f` says, for every `e ∈ P.U`, that `f` takes the actual equation indicator vector to `I.rowRhs e`. `LeafVertex` identifies the vertex by the domain `D`, with a presentation only as existence evidence; it does not retain `(U,L)` as vertex identity. `LeafLabel` is a functional on that domain carrying evidence that it respects one presentation.

The same-domain results are, without omitted mathematical premises,

```lean
theorem H_eq_of_domain_eq
    (P Q : PresentedLeaf I J h)
    (hD : P.domain = Q.domain) : P.H = Q.H

theorem respectsAt_iff_of_domain_eq
    (P Q : PresentedLeaf I J h)
    (hP : P.domain = D) (hQ : Q.domain = D)
    (f : RawLeafLabel I D) :
    RespectsAt P hP f ↔ RespectsAt Q hQ f
```

The extension theorem is

```lean
theorem actual_existsUnique_gluedLeafRhsFunctional
    (I : ActualOccurrenceAllocation.Instance N m)
    (P : PresentedLeaf I J h)
    (U' : Finset I.RowId)
    (hU' : GoodQuestion I.support U')
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    ∃! F : ↥(P.domain ⊔ equationSpan I.support U') →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      ∀ e (he : e ∈ U'),
        F ⟨equationVector I.support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan I.support U' e he)⟩ =
          I.rowRhs e
```

The quantifier order is appropriate: one actual occurrence-allocation instance is fixed, then an arbitrary legitimate presented leaf, arbitrary second good question, and arbitrary existing leaf label are accepted. The theorem produces the unique compatible map on the displayed sum. It neither chooses a favorable `U'` nor assumes the desired glued map or its uniqueness. The absence of a `U'.card = J` premise is a sound strengthening of this local algebraic statement; the future star relation must impose the manuscript's size-`J` carrier when constructing actual sampled leaf vertices.

## Manuscript correspondence

The authoritative submission manuscript, SHA-256 `DC749B0EF184E5D0792C3D366B2461C4478ADD9FACBD4D653627731ADC4DB240`, states at lines 171--180 that a retained `J`-tuple defines `H_U`, leaf domains are `L + H_U` with `dim L = 2h` and transversality, labels satisfy the equation RHS on `H_U`, leaf equivalence is

`L + H_U + H_U' = L' + H_U + H_U'`,

and the intended next result is unique side-condition-preserving label transport. The current increment discharges the following exact subdependencies of that paragraph:

| Manuscript dependency | Lean evidence | Status |
|---|---|---|
| Actual leaf presentation `D=L+H_U`, `dim L=2h`, `L∩H_U=0` | `PresentedLeaf`, `PresentedLeaf.H`, `PresentedLeaf.domain` | Defined |
| Actual label and equation-RHS side condition | `RawLeafLabel`, `RespectsAt`, `LeafLabel` | Defined |
| Vertex identity is the domain rather than its presentation | `LeafVertex` | Defined |
| Same domain determines the equation span | `H_eq_of_domain_eq` | Proved |
| RHS side condition descends across presentations of the same domain | `respectsAt_iff_of_domain_eq` | Proved |
| Unique compatible functional on `D + H_U'` | `actual_existsUnique_gluedLeafRhsFunctional` | Proved |
| Leaf equivalence `Rel`, transport, inverse and coherence | No declaration in this increment | Open |
| Alphabet cardinality `R=2^(2h)` | No declaration in this increment | Open |
| Center, sampler, stationarity and acceptance | No declaration in this increment | Open |

The increment is integrated: the glued-functional theorem consumes the actual `PresentedLeaf`, actual support and RHS functions, the compiled actual compatibility bridge, and the compiled unique submodule gluing theorem. Its output is precisely the ambient label needed to restrict to a future related representative. This is a necessary construction inside transport rather than another detached generic universal property.

## Assumption and incidence audit

For `H_eq_of_domain_eq`, equality of the two domains puts `P.H` inside the other presentation's coordinate space and conversely. The certified span-intersection identity then reduces each inclusion to common equation rows. Its abstract premises are discharged with `I.support_card` and `I.pair_intersection`; both presentations provide their own `GoodQuestion` hypotheses. No source satisfiability, favorable RHS assignment, or desired span equality is assumed.

For RHS descent, arbitrary stored RHS values are legitimate locally because a good question has pairwise-disjoint nonempty three-variable supports, so its selected equation vectors are independent. The proof extends the supplied functional from `D` to the ambient vector space, invokes the certified actual compatible-RHS functional on the second equation span, and uses `H_eq_of_domain_eq` to place each second-presentation equation vector in the needed intersection. Noncomputable extension is mathematically sufficient here and carries no algorithmic or runtime claim.

For gluing, the supplied `f` already respects the first presentation. The actual compatible-RHS theorem constructs the unique RHS functional on `H_U'` and proves intersection agreement; the submodule gluing theorem then yields the unique map on `D ⊔ H_U'`. The final uniqueness argument also uses uniqueness of the RHS functional on `H_U'`. Thus actual-source three-uniformity, pairwise linearity, and both explicit `GoodQuestion` conditions suffice for this increment. The proof does not use `card_U`, `finrank_L`, or `transverse`; these fields are not hidden assumptions in the local argument, but they correctly remain in the presentation because the manuscript's later relation, count, center, and sampler consumers need them.

`GoodQuestion` remains an explicit condition on `P.U` and `U'`. This module does not itself sample those questions or prove retained mass. Earlier actual tagged-question results may supply that distributional input, but it must be connected explicitly when the star sampler is assembled. In particular, actual pairwise support intersection alone does not imply the no-cross clause of `GoodQuestion`.

The nonempty one-row fixture constructs an actual label and invokes the exact glued-functional theorem with RHS `1`; it is not vacuous. The empty fixture checks the legitimate `J=0` boundary. The two same-presentation checks exercise theorem signatures but do not test distinct presentations of one domain. That coverage limitation does not invalidate the general proofs; a later transport fixture should exercise genuinely different presentations and repeated addresses.

## Exact remaining boundary

This increment does **not** prove any of the following:

- the manuscript relation `Rel(P,Q)` given by equality after adjoining the opposite equation spans;
- reflexivity, symmetry, or transitivity of that relation, including the private-coordinate bridge needed for transitivity;
- a transported label obtained by restricting the glued map to a related target domain;
- one-way transport correctness, identity, inverse, composition, or proof-independent coherence;
- repeated-address semantics or equality of labels when two star slots reach the same representative;
- the leaf alphabet count `2^(2h)` or any finite/enumerable bound;
- a center `K`, center restriction, representative sampler, equivalence-class uniformity, or stationarity;
- actual-star acceptance, value preservation, clique consistency, outer soundness, or source hardness;
- an encoded randomized polynomial-time reduction, runtime/coin/asymptotic bounds, NP-hardness, the manuscript headline theorem, publication readiness, `P = NP`, or `P ≠ NP`.

The next force-bearing consumer should define the exact manuscript relation, use `actual_existsUnique_gluedLeafRhsFunctional` to define one-way transport to a related target, and prove well-defined restriction. The risk-first continuation is:

```text
leaf equivalence + one-way transport
  → transitivity/private-coordinate bridge
  → identity, inverse, and coherence
  → presentation descent and repeated-address semantics
  → alphabet count and center restriction
  → representative sampler and stationarity
  → actual-star acceptance
  → outer soundness and source hardness
  → reduction, runtime, fixed-L asymptotics
  → manuscript reconciliation and release package
```

## Certification and cloud audit

I independently rehashed the canonical `artifact-hashes.txt`: all **139** listed rows are present and match, with zero mismatches. Its SHA-256 is

`3EADD48379297AAD61EF5ADF24D73498770D1529A32969D008FE6D742E502BED`,

matching `artifact-hashes-manifest.sha256`.

| Artifact | SHA-256 |
|---|---|
| Frozen main source | `D19126D4962A13AF182462F56548FE74252100108D5BC1C9EF1C51EAEEBD1452` |
| Frozen Checks source | `E76DB5B1AF64E31131E785CAB057F194DF3428CE67E159693C61EE3B4AB0564E` |
| Cloud main object | `3AE5AB5229E44A73D0AB545987E93E028E5F0C522DF88149ED10983F51E82C4B` |
| Cloud Checks object | `A6F2D6F0D0B023265916D4BD7F58DDE23D9A35F1A1A34208D65BE96538D31165` |

The transfer receipt records matching local and remote bundle SHA-256 `FD98C5DB3B89F6C04552916E9E6315D806F26B8A596694278DA2E9EBBFC27A21`, a clean detached checkout at the frozen source commit, matching frozen source hashes, and 36 source-stability assertions. The target-fresh Linux run rebuilt the 15-module project-source import closure and then main and Checks; all 17 stages exited `0`. The forbidden-token scan is clean. Printed theorem profiles contain only `propext`, `Classical.choice`, and `Quot.sound`.

The cloud and local object bytes differ because the cloud run rebuilt into a fresh Linux target while the local cache came from a different target/OS context; the receipt correctly does not treat cross-platform object-byte equality as an invariant. The initial cloud attempt stopped before the main module when pinned Complexitylib PCP objects were absent; after those pinned dependencies were built, the successful run started in a new empty target. This is useful route-changing diagnostic evidence, not a theorem failure.

The builder used one `c3-highmem-8` VM rather than the originally requested unavailable `n2d-highmem-8`; it remains within the authorized 8-vCPU/64-GiB ceiling. The evidence shows no external IP, IAP-only TCP 22 from `35.235.240.0/20` targeted to the builder service account, and VM state `TERMINATED`. The cumulative list-price estimate is **$0.340771**, leaving **$249.659229** below the $250 ceiling. The retained 200-GiB balanced disk continues to accrue about **$0.657533/day** even while the VM is stopped; future closeouts must include that storage accrual. These controls establish build provenance and bounded operations, not mathematical validity by themselves.

## Disposition

**GO-WITH-NOTES.** Accept the frozen increment as the canonical completion of actual-source `PresentedLeaf`/`LeafLabel` representation, same-domain equation-span equality, RHS presentation descent, and unique functional gluing on `D ⊔ H_U'`. It is a force-bearing precursor to the manuscript's unique transport theorem. The table-ready note is: **actual leaf labels now descend across same-domain presentations and extend uniquely over `D ⊔ H_U'`; equivalence, transport/coherence, repeated-address semantics, sampling/stationarity, acceptance, and all hardness claims remain open.**
