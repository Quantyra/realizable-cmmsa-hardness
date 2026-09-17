# Actual leaf relation laws — complexity-theory review

Date: 2026-09-15  
Lens: top-level complexity-theory review  
Verdict: **GO-WITH-NOTES**

## Reviewed frozen state

- Proof source commit: `e77fda3102152ca111daf3464af4a45931178f81` (`prove actual leaf relation laws`).
- Certification commit: `6da7f1ce41535cceea462bd4c756dbf08f84034d` (`certify actual leaf relation laws`).
- Main source SHA-256: `87BE216E92B19AD2044BF5DB1551A3D36BE3993ABBD456FDCF16FA379274610C`.
- Checks source SHA-256: `EBCFCE831F66382614D9D0EF9FBD30D566E0B019BC9C955F943FD61658C90626`.
- Fresh main object SHA-256: `2AD7B111371F0523DD0AC037F519919A4224F5317EDCE980CF380A6D214C3F13`.
- Fresh Checks object SHA-256: `EDB86FCD8906B7296900346248C2CA564C5DC27CEB937293AC38C9B48C2A0357`.
- Certification evidence manifest SHA-256: `7D7F000045660B422CEF18FCCA2A427B3D2421D7D17659782C172D113E51CBDB` (`artifact-hashes.txt`, 130 rows, independently rehashed with zero mismatches).
- Bundle SHA-256 on both sides: `5C86BC88686EBA1376AE06FB3EDC8AF93A92EEF4CFF1C38E69EDEC90A0BB8C25`.
- Returned evidence archive SHA-256 on both sides: `ED5C90A89C9FD4548A4456937F5A0BB506C6BF4D4776630DC30B98CAB98CDAA4`.

The content-addressed gate checked the exact detached source commit, a clean checkout, both frozen source hashes, and bundle equality before compilation. Forty-two before/between/after source assertions retained the same commit and hashes. A fresh isolated target rebuilt the complete reachable 17-module project-source closure and then the frozen main and Checks modules; all 19 stages exited `0`. The forbidden-source scan was clean for `sorry`, `admit`, `native_decide`, and source-level `axiom`. Printed theorem profiles contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact obligations discharged

The increment proves the following actual-incidence structural statements, universally over the displayed finite types or actual occurrence-allocation parameters:

```lean
theorem row_private_outside_two_questions ... :
    ∃ x ∈ row e,
      x ∉ questionSupport row U₁ ∧
      x ∉ questionSupport row U₃ ∧
      x ∉ questionSupport row (U₂.erase e)

theorem equationSpan_inf_sup_coordinateSpace_le ... :
    equationSpan row U₂ ⊓
        (coordinateSpace row U₁ ⊔ coordinateSpace row U₃) ≤
      equationSpan row U₁ ⊔ equationSpan row U₃

theorem actual_equationSpan_inf_sup_coordinateSpace_le ... :
    equationSpan I.support U₂ ⊓
        (coordinateSpace I.support U₁ ⊔ coordinateSpace I.support U₃) ≤
      equationSpan I.support U₁ ⊔ equationSpan I.support U₃

theorem PresentedLeaf.Rel.refl (P : PresentedLeaf I J h) : P.Rel P
theorem PresentedLeaf.Rel.symm {P Q : PresentedLeaf I J h} : P.Rel Q → Q.Rel P
theorem PresentedLeaf.Rel.trans (P Q R : PresentedLeaf I J h) :
    P.Rel Q → Q.Rel R → P.Rel R

theorem transportedLabel_identity_canonical ... :
    transportedLabel P P (PresentedLeaf.Rel.refl P) f hf = f

theorem transportedLabel_inverse_canonical ... :
    transportedLabel Q P (PresentedLeaf.Rel.symm hPQ)
      (transportedLabel P Q hPQ f hf)
      (transportedLabel_respectsAt P Q hPQ f hf) = f

theorem transportedLabel_proof_irrel ... :
    transportedLabel P Q hPQ₁ f hf₁ =
      transportedLabel P Q hPQ₂ f hf₂
```

The supporting `transportCompatible_refl` and `transportCompatible_symm` theorems establish the compatibility witnesses used for identity and inverse, rather than obtaining those equalities by an unrelated extensional shortcut.

## Match to the manuscript's MZ Lemmas 3.3–3.4 contract

The authoritative submission manuscript states the imported MZ Section 3.3 / Lemmas 3.3–3.4 contract as follows: a leaf presentation has domain `L + H_U`; two presentations are equivalent exactly when

```text
L + H_U + H_U' = L' + H_U + H_U',
```

and equivalent presentations admit unique side-condition-preserving label transport. The formal relation

```lean
P.Rel Q := P.domain ⊔ Q.H = Q.domain ⊔ P.H
```

is the same ordinary-subspace-sum equation after expanding `P.domain = P.L ⊔ P.H` and `Q.domain = Q.L ⊔ Q.H`. It is not a quotient, an isomorphism up to dimension, or a weakened containment relation.

The transitivity proof supplies the nontrivial actual-incidence step needed by the MZ Lemma 3.3 role. If an equation `e` of the middle question lies in neither endpoint question, its three-variable support meets each endpoint question support in at most one variable. Hence at most two coordinates are occupied by the endpoints, leaving a coordinate that is also private within the middle good question. Evaluating a middle-span linear combination at that coordinate isolates the coefficient of `e`, forcing that coefficient to zero whenever the vector lies in the sum of the endpoint coordinate spaces. This establishes

```text
H_U₂ ∩ (Coord(U₁) + Coord(U₃)) ⊆ H_U₁ + H_U₃,
```

which is then used to cancel the middle equation-space term and prove ordinary-sum relation transitivity. This is the force-bearing part of the increment; it is not generic lattice packaging.

The hypotheses match the local manuscript representation:

- every actual row has cardinality three (`I.support_card`);
- distinct actual rows intersect in at most one coordinate (`I.pair_intersection`);
- each `GoodQuestion` has pairwise-disjoint selected rows and forbids a third equation from containing points from two distinct selected rows;
- each `PresentedLeaf I J h` carries a good question of cardinality `J`, an `L` of rank `2h` inside its coordinate space, and transversality from `H_U`.

The relation proof actually needs fewer presentation fields than the complete leaf carrier, which strengthens rather than weakens the statement. It does not assume relation transitivity, a global satisfying assignment, or the target RHS compatibility it is meant to derive. The actual occurrence-allocation wrapper discharges the 3-uniform/linear-incidence premises from the constructed source.

For the MZ Lemma 3.4 role, the previously certified one-way unique transport is now supplemented by canonical identity and inverse laws. The identity theorem proves transport along reflexivity returns the same raw label. The inverse theorem proves transport to a related presentation and back returns the source raw label. `transportedLabel_proof_irrel` removes dependence on proofs of the same endpoint relation and RHS-respecting premise. These are substantive coherence components, although they are not the full three-presentation composition law.

The repository's source note says the complete STOC 2026 text was unavailable and bounds its MZ claims to the accessible arXiv v1. Accordingly, this review verifies exact agreement with the authoritative submission manuscript's stated MZ Lemmas 3.3–3.4 contract and the locally retained source boundary; it does not independently certify that an unavailable later publication uses identical numbering or wording.

## Quantifiers, assumptions, and fixtures

No harmful quantifier or assumption drift was found. The public theorems quantify over all natural `N,m,J,h`, every constructed `ActualOccurrenceAllocation.Instance N m`, and arbitrary qualifying presentations and labels. There is no positivity assumption on `J` or `h`, so the empty boundary remains included. Noncomputable choice appears in transport construction, so these declarations are mathematical existence/canonicity results and do not establish an efficient transport algorithm.

The Checks module includes a nonempty three-question fixture using three genuinely distinct original-row questions and separately exercises transport between two distinct presentations with differing source RHS values. It also exercises the empty-question, zero-dimensional boundary. The nonempty fixture has `h = 0` and `L = ⊥`, so it does not test positive-dimensional transverse `L` or the eventual sampled-star geometry; the universally quantified theorem signatures, rather than the fixtures, carry that scope.

## Force versus packaging

| Component | Assessment |
|---|---|
| Private-coordinate lemma and span containment | **Force-bearing.** Uses the actual 3-uniform linear incidence and `GoodQuestion` structure to remove a middle-only coefficient. |
| `PresentedLeaf.Rel.trans` | **Force-bearing.** Closes the non-generic obstruction to treating the manuscript's ordinary-sum relation as an equivalence relation. |
| Transport identity and inverse | **Force-bearing local coherence.** They turn conditional one-way transport into a reversible canonical operation for a related pair. |
| Reflexivity, symmetry, compatibility wrappers, proof irrelevance | Primarily API/packaging, but correctly expose the equivalence and canonical transport laws needed by later consumers. |

This increment therefore satisfies the instruction that the accepted unit not be merely carrier algebra. It closes a genuine manuscript bridge. It is still only one bridge in the star construction.

## Open obligations and claim boundary

This review explicitly does **not** credit any of the following as discharged:

1. **Three-way/path coherence:** for `P.Rel Q` and `Q.Rel R`, direct transport `P → R` must equal transport `P → Q → R`. Identity, inverse, and proof irrelevance do not imply this theorem at the present API without a proof.
2. **Presentation descent:** raw labels on presentation domains must be packaged/descent-compatible as `LeafLabel` values on `LeafVertex`, independent of all presentation witnesses.
3. **Repeated-address semantics:** repeated occurrences of the same leaf address must have the exact shared-variable behavior required by the formula compilation.
4. **Label count/alphabet bound:** the exact `2^(2h)` count (and the claimed alphabet bound `R`) remains to be derived for the actual quotient/leaf labels.
5. **Center restriction:** construction and well-definedness of restriction to the transverse center label are absent.
6. **Representative sampler and stationarity:** no finite representative-class sampler, uniformity/stationarity proof, or executable enumeration/cost bound is provided here.
7. **Actual-star acceptance:** neither completeness nor soundness of the full `(m+1)`-query star test follows from these local relation laws.
8. **Outer soundness and source hardness:** the MZ outer-game contract and concrete hardness-producing source map remain unformalized/uninstantiated at headline scope.
9. **Reduction, runtime, and asymptotics:** no randomized many-one reduction, formula semantics, runtime/coin bound, fixed-parameter enumeration, leaf bound, or asymptotic gap theorem is established.
10. **P versus NP:** the increment proves neither `P = NP` nor `P ≠ NP`, and does not by itself prove NP-hardness of CMMSA.

The next direct consumer should be the exact three-way transport composition/path-coherence theorem over `P,Q,R`, using the newly proved `Rel.trans`. It must then feed actual `LeafLabel` presentation descent rather than remain a raw-label-only identity.

## Verdict table note

| Lens | Verdict | Accepted scope | Required next consumer |
|---|---|---|---|
| Complexity theory | **GO-WITH-NOTES** | Actual-incidence private-coordinate cancellation; ordinary-sum relation reflexivity, symmetry, and transitivity; pairwise canonical transport identity, inverse, and proof independence. | Three-way transport composition, followed by `LeafLabel` presentation descent and repeated-address semantics. |

`GO-WITH-NOTES` means this frozen increment is suitable for inclusion in the formal dependency chain at exactly the scope above. It does not promote the MZ star construction, the manuscript theorem, the hardness claim, or the release package to complete.

## Cloud state and cost at certification closeout

- Builder: `quantyra-lean-builder-01`, `c3-highmem-8`, private interface with no external IP/access configuration.
- VM power state: **TERMINATED** at `2026-09-15T17:38:16.459-07:00`.
- Increment estimated cost: `$0.077977695621`.
- Cumulative estimated GCP spend: **`$0.514970682121`**.
- Remaining under the `$250` hard operational ceiling: `$249.485029317879`.
- The retained 200 GiB balanced disk continues to accrue the recorded estimated `$0.6575328/day` while the VM is stopped.

The cost values are on-demand estimates from the canonical certification receipt, not invoice data.
