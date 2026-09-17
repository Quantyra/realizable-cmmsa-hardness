# Actual Theorem 1 (conditional two-stage Preserves) complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `10c3b9b9653852f56e300fc2b8cc202ece2dbf71`. Independently rehashed local main `C62AAE87A1A4319198D648A431206750C3F48F8562590DAB56DDBA962678ABAF`, Checks `CE241ECFC419AC0D93E7A703B7980BBE92BFDD4613F6EDB6452A1E5524FF2029`; objects `56CC9970…7C3C` / `61B212CF…20CD`. Evidence `research/evidence/2026-09-16-actual-theorem1-fresh-run/` gate PASS naming `10c3b9b`. `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports.

This increment is a genuine Cook–Levin zero-coin `SeededMap` lift plus a *conditional* inhabitation of `RandomizedPromiseNPHard (cmmsaPromise L σ γ)` from two hypothesized `Preserves (1/6)` maps at total error `0+1/6+1/6=1/3`. It is not unconditional manuscript Theorem 1.

## Force

`fpSeededMap f hf` is the correct embedding of a deterministic FP many-one map as a randomized reduction: `run = f ∘ pairFst`, empty ruler, `coinCount = 0`. `apply x seed = f x` ignores coins. On `Fin 0 → Bool` there is one empty seed, so `successProbability` is `1` exactly when `f x` lands in the target set and `0` otherwise. `fpSeededMap_preserves` therefore converts `MapReducesVia` into `Preserves … 0 0`. That is Karp, not Turing, and not RP.

`np_to_sat_seeded` is the Cook–Levin lift. Complexitylib `SAT.NPHard_language` is `∀ A ∈ NP, A ≤ₚ SAT.language`: an FP function with `x ∈ A ↔ f x ∈ SAT.language`. `SAT.language` is encoded CNF-SAT (`∃ φ, z = φ.encode ∧ φ.Satisfiable`). `ofLanguage A` is the total promise `yes = A`, `no = Aᶜ`. The `mp`/`mt` constructor is exactly `MapReducesVia` on those total sides. Quantifiers are honest: every NP language, zero coins, error `0` on both sides.

`theorem1_realizable_cmmsa` is a transfer lemma, not a hardness construction. Fix `A ∈ NP`. `np_to_sat_seeded` supplies `R₀` at error `0`. Hypotheses supply `R₁ : SAT → source` at `1/6` and `S : source → cmmsaPromise` at `1/6`. `exists_preserving_composition` of `R₀` with `R₁` uses the certified one-sided good-good lower bound at `0+1/6=1/6` (the `0 ≤ 1` side conditions hold; Cook–Levin is *not* weakened to `1/6` first). `two_stage_randomized_map` then composes that composite with `S` at `1/6+1/6=1/3`. The result is `RandomizedMapReduces (ofLanguage A) (cmmsaPromise …)`, hence `RandomizedPromiseNPHard`. Error `1/3` is two-sided success `≥ 2/3`, matching the certified many-one predicate, not deterministic `PromiseNPHard`.

The two `1/6` hypotheses are non-vacuous. Empty `source` cannot inhabit `hSatSrc` (SAT yes/no are nonempty). Identity plus `preserves_mono 0 → 1/6` can collapse *one* stage (`source = ofLanguage SAT` or `source = cmmsaPromise`), but never both: a SAT-to-`cmmsaPromise` `SeededMap` remains missing. Constant maps cannot hit both sides of a disjoint promise.

`L`, `σ`, `γ` stay parameters under `1 ≤ σ` and `0 < γ < 1`. The statement is for whatever family those hypothesized maps target.

## Packaging and theater

Module/commit titles that say "Actual Theorem 1" / "prove actual theorem1", and the docstring "Manuscript Theorem 1, from SAT-to-source and source-to-CMMSA Preserves (1/6)", are catalog labels for this *conditional* inhabitation. Manuscript Theorem 1 is: for every sufficiently large *fixed* `L`, Gap CMMSA with constructed `σ_L` (`log σ_L / log L → 1`) and `γ_L → 0` is NP-hard under randomized polynomial-time many-one reductions. This increment does not pick those parameters, does not quantify "sufficiently large `L`", and does not construct either `1/6` map.

`source` is an arbitrary `PromiseProblem`. It is not pinned to regularized 3-Lin, Gap-3LIN, or any star/sampling object. This module does not import those surfaces. A SAT-to-source map must start from Complexitylib encoded CNF-SAT, not from 3SAT unless a further SAT-to-3SAT stage is supplied.

`two_stage_randomized_map` still drops the original-input clock/coin witnesses retained on `exists_preserving_composition`. They are recoverable: `SeededMap` already has `run ∈ FP` and `coinCount_poly`. Error addition remains the assembly’s one-sided `1-(e₁+e₂)` bound, tight here because the Cook–Levin stage is deterministic.

Do not read inhabited `RandomizedPromiseNPHard (cmmsaPromise …)` off this theorem without the two maps. The type still has `hSatSrc` and `hSrcCmmsa` as hypotheses.

## Checks and non-credits

Checks `#check` / `#print axioms` of every public theorem. `fpSeededMap id` on `[]` and on `[true, false]` is zero-coin identity *runtime*, not a SAT-to-CMMSA map. `np_to_sat_seeded` is inhabited only on `SAT.language` (via `language_mem_NP` and `NPComplete_language.1`): a 0-error SAT-to-SAT Cook–Levin self-map. Checks do **not** inhabit `theorem1_realizable_cmmsa`, including not using identity as `hSrcCmmsa`. Axioms standard.

Not a constructed SAT-to-source `Preserves (1/6)`. Not a constructed source-to-`cmmsaPromise` `Preserves (1/6)`. Not a fixed-`L` `σ_L`/`γ_L` family. Not deterministic `PromiseNPHard`. Not credited: unconditional Theorem 1, Corollary 2, P vs NP.

Usable as (i) the zero-coin Cook–Levin `SeededMap` from every NP language to encoded SAT, and (ii) the error-budgeted composition that would inhabit randomized many-one NP-hardness of parameterized Gap CMMSA *once* the two `1/6` maps exist. Next consumer remains those maps (SAT-to-regularized-3-Lin source, then source-to-encoded CMMSA including sampling/repair/FP), then Corollary 2 from an inhabited Theorem 1 plus HN parameters. Do not skip those maps.
