# Actual headline σ_L / γ_L parameters complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `605b07e8d192f13772bdeac9ab16e3772b491d5a`. Independently rehashed local main `29767BDCE518085DB0590A260293003083858169FCC30D49A299217D913FC20C`, Checks `1000E3BD838BF74C7C3EE923F5816E45421169C471FBC7BE49C3A556EE949B48`; objects `D0631689…A7B1` / `7353C5A3…06E2`. Evidence `research/evidence/2026-09-16-actual-headline-parameters-fresh-run/` gate PASS naming `605b07e`. `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`; `mOf_spec` axiom-free). Forbidden-token scan clean. No leaf-star imports.

This increment is a faithful explicit manuscript parameter family plus eventual domain lemmas and a *conditional* specialization of certified `theorem1_realizable_cmmsa` at those functions. It is not SAT-to-source construction and not unconditional Theorem 1.

## Force

The public functions instantiate manuscript lines 1298–1335 with `b_m = m` (freeze-permitted; `m ≤ sqrt(log2 L)` already implies the extra `b_m` bound). `qOf m = Nat.sqrt m` is `floor(sqrt m)`. `mOf L` is `0` if `sqrt(log2 L) < 256`, else that square root: the unique largest admissible `m`. `mOf_spec` / `mOf_maximal` are the corresponding disjunction and maximality. `mOf_unbounded` is the manuscript line “every fixed `m` is admissible for all sufficiently large `L`, so `m(L) → ∞`”: `∀ M, ∃ L0, ∀ L ≥ L0, M ≤ mOf L`, with explicit witness `L0 = 2^{(max(M,256))^2+1}`. Quantifiers are honest.

`hOf` is `b_m * floor(log2((L-1)/(q(m+1))) / (2 b_m))` with Nat floors. `ROf L = 2^(2 hOf L (mOf L))`. `GammaOf L = 2 * (3/4)^(qOf (mOf L))` as exact `Rat`. `sigmaL L = (ROf L / 4) / 2` is `floor(floor(R/4)/2)`. `gammaL L = 2 * GammaOf L = 4 * (3/4)^q`. That is the manuscript `σ_L` / `γ_L` pair, with `R` used as the manuscript’s inner `sigma` input to the floor formula.

`hOf_le_log2` is `2 h ≤ log2 L` for every `L`: `2 b_m floor(log2(num)/(2 b_m)) ≤ log2(num) ≤ log2 L` because `num = (L-1)/den ≤ L`. `sigmaL_le_ROf` is the two Nat floors. The freeze’s `∨ True` nearlinear template was **dropped**, not shipped. These are real inequalities, not tautologies.

`sigmaL_ge_one_eventual` is `∃ L0, ∀ L ≥ L0, 1 ≤ sigmaL L`. The proof is not vacuous: from `mOf_unbounded 256` it gets `s = mOf L ≥ 256`, then `2^(s^2) ≤ L`, then `q(s+1) 2^(4s)+1 ≤ 2^(s^2)` (`two_pow_sq_dominates`), hence `num ≥ 2^(4s)`, `log2(num) ≥ 4s`, `h ≥ 2s ≥ 2`, `R ≥ 8`, and `floor(floor(R/4)/2) ≥ 1`. `gammaL_pos` holds for **every** `L` (`4 * (3/4)^q > 0`). `gammaL_pos_lt_one_eventual` is the live-range pair `0 < γ_L < 1`, using `mOf_unbounded 36` so `q ≥ 6` and `4*(3/4)^6 < 1`. `gammaL_small_eventual` is `γ_L → 0` over positive rationals: for `ε > 0` pick `k` with `(3/4)^k < ε/4` (`exists_pow_lt_of_lt_one`) and take `m ≥ k^2`. That is the manuscript `gamma_L → 0` limit, not a packaging synonym.

`adviceLeaf` / `sigmaLearn` / `gammaLearn` are the Corollary 2 *parameter maps* (lines 81–85, 1322–1325): `L = a - 2 log2(a+1) - c_U` with `Nat.sub`, `floor(0.49 σ_L)` as `(49 * sigmaL _)/100`, and `5 γ_L`. They are definitions. They do not inhabit learning hardness.

`theorem1_headline` is definitional specialization: `theorem1_realizable_cmmsa` at `cmmsaPromise L (sigmaL L) (gammaL L) …`. Side conditions `1 ≤ σ_L` and `0 < γ_L < 1` remain hypotheses (the eventual lemmas are not inlined). The two `Preserves (1/6)` maps remain hypotheses. Error budget is still Cook–Levin `0` plus `1/6+1/6=1/3`, randomized many-one, not deterministic `PromiseNPHard`. `source` is an arbitrary `PromiseProblem`. The type is not inhabited.

## Packaging and theater

Module/commit titles that say “actual headline” name this parameter family and the conditional specialization. Manuscript Theorem 1 is: for every sufficiently large *fixed* `L`, Gap CMMSA with constructed `σ_L` satisfying `log σ_L / log L → 1` and `γ_L → 0` is NP-hard under randomized polynomial-time many-one reductions. This increment supplies the functions, `m(L) → ∞`, eventual `1 ≤ σ_L`, eventual `γ_L ∈ (0,1)`, and `γ_L → 0`. It does **not** prove `log σ_L / log L → 1`. The missing lower bound is the manuscript identity `log R = log L - O(log(m+1)+b_m)` coming from `2h` being `log2((L-1)/(q(m+1)))` rounded down to a multiple of `2 b_m`. `hOf_le_log2` is only the matching upper bound. Do not read `hOf_le_log2` + `mOf_unbounded` as nearlinearity.

`hOf` totalizes the manuscript formula outside the live range: `Nat.max den 1` and `Nat.max m 1` so `m = 0` uses `b_m = 1` and divides by `1` rather than `q(m+1) = 0`. In the intended regime `m ≥ 256` both maxima are identities (`q ≥ 16`). Concrete `L = 2^20` is **not** that regime (`log2(2^20) = 20`, `sqrt 20 < 256`), so `#eval` there exercises the totalization (`mOf = 0`, `h` with `b_m = 1`, `sigmaL = 32768`, `gammaL = 4 ∉ (0,1)`). Do not treat `L = 2^20` as a headline instance.

Eventual `L0` is existence-only (huge, from `2^(t^2+1)`). The manuscript also asks `h` to exceed every fixed cutoff used upstream, including `σ ≥ 8` and the `ξ = 1/m^2` numerical inequalities. The freeze asked for `1 ≤ σ_L`; that is what is proved. The same `h ≥ 2s ≥ 512` chain would give far more, but no named `sigmaL ≥ 8` or error-budget lemma is shipped. `theorem1_headline` is still per-`L` with caller-supplied side conditions; it does not quantify “sufficiently large `L`” internally. That matches the manuscript’s fixed-`L` (not uniform-in-`L`) convention, but it is not the assembled “for all large `L`” Theorem 1 even under the map hypotheses.

Corollary 2 maps use `log2nat = floor(log2 ·)` rather than manuscript `ceil(log2(a+1))`. The freeze specified that. The subtracted term differs by at most `2`; `Nat.sub` silently zeros when `a < 2 log2(a+1) + c_U`, sending `adviceLeaf` to `0` and `gammaLearn` to `5 * gammaL 0 = 20`. There is no eventual `adviceLeaf ≥ 256`, `1 ≤ sigmaLearn`, or `gammaLearn < 1` lemma, and no HN `c_U` construction. Do not read these defs as Corollary 2 NP-hardness.

`theorem1_headline` does not construct SAT-to-regularized-3-Lin or source-to-encoded-CMMSA `Preserves (1/6)`. Identity is not used as `hSrcCmmsa`. Checks do not inhabit the theorem. Next consumer remains those maps (sampling/repair/FP), then an unconditional Theorem 1 at `sigmaL`/`gammaL`, then Corollary 2 via HN transfer.

## Checks and non-credits

Checks `#check` / `#print axioms` of every public theorem and invoke `hOf_le_log2` / `sigmaL_le_ROf` at `L = 0` and `L = 2^20`. `#eval`: `mOf 0 = 0`, `sigmaL 0 = 0`, `gammaL 0 = 4`, `mOf (2^20) = 0`, `sigmaL (2^20) = 32768`, `gammaL (2^20) = 4`. Empty/zero types: `mOf 0 = 0`, `sigmaL 0` is a `Nat`. `#check theorem1_headline` only. Axioms standard.

Not a constructed SAT-to-source `Preserves (1/6)`. Not a constructed source-to-`cmmsaPromise` `Preserves (1/6)`. Not `log(sigma_L)/log L → 1`. Not Corollary 2 NP-hardness. Not deterministic `PromiseNPHard`. Not credited: unconditional Theorem 1, P vs NP, DOI.

Usable as (i) the explicit `σ_L` / `γ_L` family with honest eventual `1 ≤ σ_L`, `γ_L ∈ (0,1)`, and `γ_L → 0`, (ii) the Corollary 2 numeric maps as functions, and (iii) the still-conditional headline specialization of certified Theorem 1 at those functions. Do not close the hardness route on this increment.
