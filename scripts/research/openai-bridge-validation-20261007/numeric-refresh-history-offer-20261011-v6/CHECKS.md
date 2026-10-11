# Checks and custody

- Offer directory: `scripts/research/openai-bridge-validation-20261007/numeric-refresh-history-offer-20261011-v6`.
- Exact Lean sources: `ActualRefreshGaussian.lean` and `ActualRefreshCandidateCount.lean`.
- Source status: uncompiled author offer. No Lean/Lake, GCP, or Git command was run by this author.
- Compiler authority: Sol (`/root/compiler_custody`) is the sole GCP compiler/Git custodian. Request immutable capture before any successor edit and request GCP compile of these exact bytes.
- v5 was separately captured and remains frozen: capture index `EA55CB65AFA9FFB3C51FE6B9351D2E33FF2191FFB8A0FED53A9346B6B9D4954C`; v5 Candidate source SHA-256 `C3A9A9AC316497801B6DC89B67C667A78062EC5E88797250C164F1F14ADAAB69`. v6 does not modify v5.
- Prior v4 capture index: `87EF362E0A5A11A87C5343971993C97DCF737F9102C3340B5940149B35300BE4`. The known v4 Gaussian/API defects have been repaired in this disjoint source, but v6 remains uncompiled.
- Full114 archive pin supplied for source ownership: `input-archive.tar.gz` SHA-256 `70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`. The local source-level API inspection used the full107 trace-qualified source record because it contains the mirrored module sources; no claim is made that it substitutes for native compilation against full114.
- Pinned mathlib: `e06eff5f95374108acfaf19f1ff7473aa7771df2`.
- No compiler diagnostics, native acceptance, wrapper, or terminal claim is asserted. In particular, `encodeCandidate_injective`, the dependent Sigma/Subtype cardinal rewrites, `candidate_zoom_card_lower_aux`, and `allCandidateFreshFailures_mass_le_uniform` still require GCP compilation. Root should route any diagnostics as exact source locations.
- The theorem's guards are explicit: `r <= d`, `r+d <= n`, and `finrank V=n`; the Candidate cardinal lemma additionally uses `r<=n`, discharged by arithmetic from the supplied guards.
- Remaining proof risk: the handwritten injectivity proof reconstructs equality across dependent Sigma/Subtype fields and has not been compiler-checked. No hidden `hcount` premise or conditional count wrapper is present.