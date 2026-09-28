# GCP exact-source question-center source-law receipt

Run: 2026-09-28 UTC and Pacific. Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. Source commit: `22bb9ee34d2ba342b4de752fa651d84a7c465a6d`. Scope: `PvNP.RealizableHardness.ActualQuestionCenterSourceLaw` only.

The input was a `git archive` of that commit's `lean/`, `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`, SHA-256 `b0228326ac3923663461338b621824e0b140ad5a017691d93db64d0b70ea2c0b`. The builder verified the archive before extraction. The committed source SHA-256 was `9bce744563c4d4808f96a166b752fc2ae70eabd47a8052221df9989af15ad820`, verified before the build and after replay; the Windows checkout had the same bytes. The fresh source tree reused the builder's pinned `.lake/packages` and rebuilt `.lake/build` from scratch on replay.

Lean 4.34.0-rc2 / Lake 5.0.0 built the target successfully twice, **3,219 jobs each**, with zero `error:` lines in either build log. The axiom audit of `sourceQuestionEquiv`, `sourceQuestionLaw`, and `sourceQuestionLaw_atom` reports only `propext`, `Classical.choice`, and `Quot.sound`. The scoped source forbidden-token scan was empty. `OUTCOME.txt` records `EXIT=0` at `2026-09-28T09:11:07Z`.

The sealed evidence archive SHA-256 is `9b84e5cf845c64436e6f8e98a7d5f7c46a740de5918c39a007d419223c822883`; its 10-file internal manifest was verified after download. The hidden collector stopped the builder, and the final GCP instance state was **TERMINATED**.

**Review boundary:** this is a conditional finite U-first/K law over `GoodU`, requiring `Nonempty (GoodU I J)` and a nonempty `CenterOver I t U` fibre for every admitted U (`hcenter`). It proves the law's atom formula in that domain. The ordered source tuple-to-`Finset` U pushforward is not proved. A source comment says “as stated in the manuscript”; reviewers judged that wording broader than the formal evidence. This receipt does not certify the manuscript sampler, joint leaves/representatives, soundness, completeness, the source-to-CMMSA reduction, Theorem 1, or Corollary 2.
