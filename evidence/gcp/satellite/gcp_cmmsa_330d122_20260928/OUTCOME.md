# GCP exact-source ordered-center transport receipt

Run: 2026-09-28 UTC and Pacific. Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. Source commit: `330d122628f2980983f892f6b48134f27c8ec050`. Scope: `PvNP.RealizableHardness.ActualOrderedCenterJointTransport` only.

The input was a `git archive` of that commit's `lean/`, `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`, SHA-256 `90c06fe7835731865e325b93fa4709f780d51ed68c2e1e30cab0649f9ea85ce2`. The builder checked the archive before extraction. The committed and Windows-checkout source bytes matched, SHA-256 `27efd2b69446a79ad6482f2be3260fb96fb2bfe38177909259ec18b3d86725b7`, checked before build and after replay. The fresh tree reused the builder's pinned `.lake/packages` and rebuilt `.lake/build` from scratch on replay.

Lean 4.34.0-rc2 / Lake 5.0.0 built the target successfully twice, **3,279 jobs each**, with zero `error:` lines in either build log. The axiom audit of `orderedCenterToQuestion`, `centerKernelLaw`, `sourceQuestionLaw_mixture`, `actualOrderedCenterLaw_mixture`, and `actualOrderedCenterLaw_pushforward_eq_source` reports only `propext`, `Classical.choice`, and `Quot.sound`. The scoped forbidden-token scan was empty. `OUTCOME.txt` records `EXIT=0` at `2026-09-28T10:31:57Z`.

The sealed evidence archive SHA-256 is `a6ad8c2543e3fd00ca9e72ecca630e430f1a90b9e3823f6e312ea452ff40396c`; its 10-file internal manifest was verified after download. The hidden collector stopped the builder, and the final GCP instance state was **TERMINATED**.

**Review boundary:** the proved pushforward transports the explicitly defined initial ordered-U/conditional-K law to the stored `QuestionCenter` law under `J * (J - 1) * 157 < Fintype.card I.RowId` and `t ≤ 2 * J`. It does not prove the concrete source's tagged-copy row-count threshold, equality with the manuscript's initial-vertex/clique-resampling sampler, stationarity of a clique-resampled U′ marginal, or a joint question/leaves/table law. MZ NO soundness, YES completeness, the encoded source-to-CMMSA reduction, Theorem 1, and Corollary 2 remain open.
