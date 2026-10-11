# Checks and validation status

- Source: `ActualRefreshHistory.lean` (UTF-8, no BOM).
- Imported captured source: `ActualRefreshCandidates` (candidate carrier and actual one-step tail) and its frozen dependencies.
- Static review: theorem dependencies inspected against captured tail source, actual candidate source, Real cutoff source, Gaussian ratio source, and ActualMaximalPairLadder definitions.
- Native compilation: not run by this author, per workflow boundary. No kernel acceptance is claimed.
- Git/GCP: not run; Sol is sole custodian.
- Known open interfaces: actual zoom-cardinality lower bound and actual dependent candidate-cardinality upper bound. These are listed in `ARGUMENT.md`; downstream conclusions remain conditional on them.
- The actual bounded history is instantiated for arbitrary state transitions, including transitions depending on the chosen table; connecting it to the fixed-coordinate inverse and proving growth/termination remains open.