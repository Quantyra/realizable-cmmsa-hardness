# Actual CMMSA randomized-reduction complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `c0583486d30e65fa3c672a21b163be6f5c1c5b0e`. Independently rehashed main `9CDDC139FCF64A07A4E759AD8F5AA78337123FB0EA131E77924421FC4F776283`, Checks `BF1C7E8BAA430A75CDC94F6E5DE8A68406000C8E23CE0D4955B18546B7390850`; objects `427BFF0D…42B3` / `A5B5B80C…117F`. Evidence `research/evidence/2026-09-16-actual-cmmsa-randomized-reduction-fresh-run/` gate PASS naming `c058348`. `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports.

This increment is a well-formed encoded Gap-CMMSA promise plus a randomized many-one *interface*. It is not a hardness theorem.

## Force

`cmmsaPromise L sig gam` is the encoded string promise: yes iff `decode L` yields an instance with `Yes 0`; no iff it yields an instance with `No sig gam`. Quantifiers are honest. Malformed strings, including `[]`, sit outside the promise. `disjoint` is proved, not stored: `decode` is a function, so the two `some` instances coincide; `Yes 0` supplies an assignment of cost `≤ budget` and satisfaction `≥ 1`; `1 ≤ sig` and `budget > 0` send that witness into the `No` quantifier (`cost ≤ σ·budget`); `No` then gives satisfaction `< gam < 1`. That is the Gap-CMMSA gap (perfect completeness versus a strict universal soundness bound under a scaled budget). `hgam : 0 < gam` is unused in the arithmetic and is only a family parameter.

`cmmsaPromise_yes_of_encode` / `_no_of_encode` are the `decode_encode` membership lemmas. They do not construct a producer.

`RandomizedMapReduces` is a randomized polynomial-time *many-one* predicate: existence of a `SeededMap` with `Preserves` at error `1/3` on each side (success `≥ 2/3`). It is not deterministic `PromiseNPHard` / `MapReducesPoly`. `SeededMap` already requires `run ∈ FP`, an `FP` length ruler, and therefore polynomial coins (`coinCount_poly`). The map is Karp-style (`apply x seed = run (pair x seed)`), not a Turing/oracle reduction, and not one-sided RP.

`RandomizedPromiseNPHard` is the matching hardness *shape*: every `A ∈ NP`, viewed as the total promise `ofLanguage A` (yes `= A`, no `= Aᶜ`), `RandomizedMapReduces` to the target. The definition is uninhabited for `cmmsaPromise`. That is the intended contract, not a theorem.

`two_stage_seededMap` is certified `exists_preserving_composition` at `1/6+1/6=1/3`. Error addition is the assembly’s one-sided lower bound on the good-good path (`1-(e₁+e₂)`), not a new disintegration. The statement keeps polynomial coins and an actual TM clock in the *original* input length (`rawClock` on `pair x seed`, `inputClock` on `|x|`). `two_stage_randomized_map` drops the clock and returns only `RandomizedMapReduces`. `preserves_mono` is the standard weakening `e ≤ e' ⇒ Preserves e → Preserves e'`; it is the permitted 0-error to `1/6` lift.

`identitySeededMap` is `pairFst` with zero coins. `apply x seed = x` on the pairing. `Preserves P P 0 0` is the identity reduction of an arbitrary promise to itself. It is a runtime/asymptotics baseline, not SAT-to-CMMSA and not a source map.

## Packaging and theater

The composition force lives in certified `RandomizedReductionAssembly`. This module only pins the `1/3` endpoint and the encoded promise. Do not treat `two_stage_seededMap` as a SAT-to-source or source-to-CMMSA construction: both stages are hypotheses.

`RandomizedMapReduces` does not mention two stages and does not package the original-input clock. Any problem reduces to itself: `preserves_mono` of identity inhabits `RandomizedMapReduces P P` for every `P`, including `cmmsaPromise`. Checks do exactly that. That is identity, not hardness.

`RandomizedPromiseNPHard` is a name, not a proof. There is no `RandomizedPromiseNPHard (cmmsaPromise …)` theorem, no quantification over NP languages, and no SAT `SeededMap`. Do not read the definition as NP-hardness of Gap CMMSA.

The promise is a parameterized family `(L, σ, γ)` with `σ : ℕ`, `σ ≥ 1`, `γ ∈ (0,1)`. It is not a fixed-`L` family with constructed `σ_L`, `γ_L`, logarithmic growth, or `γ → 0`. `Yes` is frozen at `eps = 0` (perfect completeness). Satisfaction is the average of Boolean formula evaluations on a nonempty list, so `Yes 0` is completeness 1. The increment does not prove that any concrete instance is `Yes 0` or `No`.

Next consumer remains an actual SAT-to-source `SeededMap` with `Preserves (1/6) (1/6)`, then a source-to-`cmmsaPromise` `SeededMap`. Do not skip those maps.

## Checks and non-credits

Checks `#check` / `#print axioms` of every public theorem. Fixture is the existing `CMMSACodecChecks` `concrete : Instance 1`. `cmmsaPromise 1 1 (1/2)` typechecks. `decode 1 [] = none`; empty string is neither yes nor no. `identitySeededMap_preserves` on that promise; `two_stage_randomized_map` on identity twice after `preserves_mono` `0 → 1/6`. No `Yes 0` / `No` evaluation on `concrete`. No false `1/6` instance without monotonicity. Axioms standard.

Not a SAT reduction. Not source-to-CMMSA `Preserves`. Not deterministic `PromiseNPHard`. Not inhabited randomized NP-hardness. Not credited: Theorem 1, Corollary 2, P vs NP.

Usable as the encoded Gap-CMMSA promise (disjoint Yes 0 versus No), the randomized many-one predicate, and the two-stage `1/3` composition wrapper with coins and TM clock. Identity is the zero-coin baseline only. Do not close the hardness route on this increment.
