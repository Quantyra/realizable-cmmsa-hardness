# Actual SAT → 3SAT source complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `1488ff84c6d1daad1c1174aa469aeeddedc360aa`. Independently rehashed local main `5ADF857840ED4242C184AE248BCFC90703E8D1F250776A975C67B0A6E1A988E4`, Checks `16E3EF2C31E2BF2B1BDFE16D5C324793BBDC9553631FA22E9C7683CB4143B8E9`; objects `B96F861C…E4BB` / `D9F19106…1435`. Evidence `research/evidence/2026-09-16-actual-sat-to-threesat-source-fresh-run/` gate PASS naming `1488ff8`. `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean. No leaf-star imports.

This increment is a genuine Cook–Karp SAT → encoded exact-3SAT many-one reduction, lifted as a zero-coin then `1/6` `SeededMap` that inhabits the SAT-to-source slot of certified `theorem1_headline`. The source is `ofLanguage ThreeSAT.language`, not regularized 3-Lin. It is not unconditional Theorem 1.

## Force

`threeSatSource` is the total promise of Complexitylib encoded 3SAT: yes = `ThreeSAT.language` (satisfiable CNFs whose every clause has *exactly* three literals), no = the complement. `CNFSAT.language` is an abbrev of `SAT.language`. Quantifiers are honest: this is a decision language, not a gap.

`SAT.ThreeSAT.reduction` is the certified total Tseitin *clause-splitting* Karp map, not identity. On a well-formed CNF encoding it runs `CNF.to3Aux (|z|+1) φ` (fresh variables start past every unary source variable) and re-encodes; short clauses pad by repeating literals, empty clauses become a contradictory width-three pair, wide clauses use the standard `(a ∨ b ∨ z) ∧ (¬z ∨ rest)` chain. Malformed strings map to `fallbackEncoding`, a fixed unsatisfiable exact 3-CNF. `reduction_mem_FP` is a concrete TM with an explicit quartic clock (`reductionTM_computesInTime`). `reduction_correct` / `mem_language_iff_reduction_mem` is `z ∈ SAT ↔ reduction z ∈ 3SAT`. `cnfsat_le_language` is that pair as `SAT.language ≤ₚ ThreeSAT.language`.

`satToThreeSat_mapReducesVia` is the matching `PromiseProblem.MapReducesVia` on the total embeddings: yes-to-yes and no-to-no are the two directions of that iff (`mapReducesVia_ofLanguage_iff`). It is Karp, not Turing, and not RP.

`satToThreeSatMap` is certified `fpSeededMap` of that function: `run = reduction ∘ pairFst`, empty ruler, `coinCount = 0`. `satToThreeSatMap_apply` is `apply x seed = reduction x`; coins are ignored. On `Fin 0 → Bool` there is one empty seed, so `successProbability` is `1` exactly when the image lands in the target set and `0` otherwise. `satToThreeSat_preserves_zero` is therefore `fpSeededMap_preserves` at error `0`. That is the deterministic Karp lift.

`satToThreeSat_preserves` is `preserves_mono` `0 ≤ 1/6`. The `1/6` figure is interface slack for `theorem1_headline`, not a coin-using algorithm and not a new error analysis. `satToThreeSat_exists` inhabits `hSatSrc` at `source = threeSatSource`. Empty `threeSatSource` cannot do that: SAT yes/no are nonempty, and the map hits both 3SAT and its complement (wide-clause SAT instances are not already 3SAT; unsat and malformed inputs land outside 3SAT). Constant maps cannot.

`theorem1_from_threeSat_to_cmmsa` is definitional specialization: `theorem1_headline` with `source = threeSatSource` and `hSatSrc = satToThreeSat_exists`. Side conditions `1 ≤ σ_L` and `0 < γ_L < 1` remain hypotheses. `hSrcCmmsa` — existence of a `SeededMap` with `Preserves (1/6)` from `threeSatSource` to encoded `cmmsaPromise L (sigmaL L) (gammaL L)` — remains a hypothesis. The type is not inhabited. Error budget is still Cook–Levin `0` plus billed `1/6+1/6=1/3` (this stage is actually error `0`). The result, if the missing map existed, would be `RandomizedPromiseNPHard`, randomized many-one, not deterministic `PromiseNPHard`.

## Packaging and theater

Module/commit titles that say “actual SAT-to-3SAT source” name this Karp lift. The manuscript SAT-to-source map is SAT → regularized 3-Lin (a gap/promise source). This increment does **not** construct that object, does not prove a 3SAT → Gap-3LIN / 3-Lin value-preserving map, and does not produce a CMMSA instance. `threeSatSource` is a total decision promise. A later 3SAT → `cmmsaPromise` map must therefore create the Gap-CMMSA gap from yes/no 3SAT, not merely transport an already-gapped 3-Lin source.

Library `Tseitin` here is unbounded-CNF → exact-3CNF clause splitting with a polynomial TM. It is **not** the expander Tseitin tautologies of proof complexity, and it is not the `PvNP.Tseitin*` width/size surfaces. Do not read a switching-quality ratio, Frege/PHP bound, or Tseitin-on-graphs lower bound off this module.

`Preserves (1/6)` does not mean the reduction tosses coins or fails on a `1/6` fraction of seeds. `coinCount = 0`. Do not describe this as a randomized SAT-to-3SAT algorithm. The force is `SAT ≤ₚ 3SAT` plus the zero-coin `SeededMap` embedding.

`theorem1_from_threeSat_to_cmmsa` is a transfer lemma with one remaining map, not Theorem 1. Identity plus `preserves_mono 0 → 1/6` could still inhabit `hSrcCmmsa` only if `threeSatSource = cmmsaPromise …`, which it is not; checks do not supply a dummy identity as 3SAT-to-CMMSA. Do not read inhabited `RandomizedPromiseNPHard (cmmsaPromise …)` off this theorem.

No bound here feeds a switching-quality ratio.

## Checks and non-credits

Checks `#check` / `#print axioms` of every public theorem. `satToThreeSatMap.apply [] [] = SAT.ThreeSAT.reduction []` is zero-coin *runtime*, including the malformed-input fallback if `[]` does not decode. Examples inhabit `MapReducesVia`, `Preserves 0 0`, `Preserves (1/6)`, and `satToThreeSat_exists`. `#check theorem1_from_threeSat_to_cmmsa` only: the theorem is **not** inhabited. Axioms standard.

Not regularized 3-Lin. Not a constructed 3SAT → `cmmsaPromise` `Preserves (1/6)`. Not deterministic `PromiseNPHard`. Not credited: unconditional Theorem 1, Corollary 2 NP-hardness, P vs NP.

Usable as (i) the certified SAT → encoded exact-3SAT Karp `SeededMap` at true error `0`, billed `1/6` to match the headline interface, and (ii) the still-conditional Theorem 1 specialization that needs only 3SAT → encoded Gap CMMSA `Preserves (1/6)`. Next consumer remains that map (star/HN/sampling/repair/FP, or 3SAT → regularized 3-Lin then that map). Do not close the hardness route on this increment.
