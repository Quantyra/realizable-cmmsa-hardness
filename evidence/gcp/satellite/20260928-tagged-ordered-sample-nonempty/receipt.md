# Tagged ordered sample nonemptiness: exact-source GCP receipt

- Source commit: `c0234ac` (`Quantyra/realizable-cmmsa-hardness`, `main`).
- Builder: `quantyra-lean-builder-01`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`; isolated checkout `/tmp/tagged-ordered-nonempty`. Local GCP connections used `CREATE_NO_WINDOW`.
- Main Lean source SHA-256, local committed file and remote file: `89a9c9f582cf8e5445706c4d74e0951e8c8cc349029d4014b90e8433791da4cf`.
- Checks Lean source SHA-256, local committed file and remote file: `18209d060b75898ec9ba820517fdf2a3a91bcfb312a6466d1ae41a06011f5678`.
- Isolated `lake build` PID `7571`, terminal exit `0`, `3245` jobs. Full [build log](build.log), SHA-256 `929892dbf7ea13ff24d9db628f2cbb76599a1d1f3592f944f430fd02cc296d7e`.
- Exact-source `lake env lean` replay PID `8857`, terminal exit `0 0` for main and Checks. [Main replay](replay-main.log) SHA-256 `681315362cfb3c95a0b38998fd122302a57b8e73d0c77de02859ca8bcba15562`; [Checks replay](replay-checks.log) SHA-256 `67090db6521da35b2ad690770aeb4100570b4045574d4130b5e3195a95d45661`.
- Checks printed the theorem signatures and axioms. The new center, leaf, ordered-selection, and rank declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, `native_decide`, or new `axiom` declaration in the two new files.

The theorem `ordered_sample_exists_selected_of_padding` constructs a normalized tagged ordered star law under `4 ≤ T`, `0 < m`, `t ≤ 2*h`, and `h ≤ J`; it applies the existing arbitrary-fixed-raw-table selection inequality without caller-supplied center or leaf nonemptiness. The leaf witness satisfies the stronger `K ≤ L` condition. This establishes a populated sample carrier and selection comparison, not a numerical NO-soundness bound. The manuscript-exact uniformity of presented vertices versus presentation pairs and the tagged collision and MZ decoder bounds remain open. Formal three-lens review is pending; this receipt is not route-final. The builder was left running for other agents' live jobs.
