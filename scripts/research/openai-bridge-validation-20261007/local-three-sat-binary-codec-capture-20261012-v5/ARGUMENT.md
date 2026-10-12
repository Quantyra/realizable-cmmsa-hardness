# Joint local 3-SAT codec to upstream BinaryLanguage (v5)

This successor joins the concrete total local converter to the actual pinned OAI binary SAT parser. Its endpoint is the all-input statement

`w ∈ Complexity.SAT.ThreeSAT.language ↔ OAI.UniqueGamesTheorem.BinaryLanguage.language (convert w)`.

The proof retains the local runtime conversion and its explicit FP witness. Malformed local inputs convert to `[]`, which the upstream parser rejects. Successful local decoding emits the exact upstream `formulaBits` encoding of the sparse-renamed formula, including the empty local formula case, which encodes as `[false]` and parses as the empty upstream formula.

For local variable `n`, the upstream name is `bitsValue (List.replicate n true)`, whose canonical ordinary-binary digits are exactly `n` true bits. This avoids generating an exponential unary expansion. Injectivity follows from the canonical digits and their length. A local finite assignment is extended to the upstream namespace by choosing the unique local preimage for names in the sparse image and assigning false elsewhere. Conversely, restrict an upstream assignment to the first `phi.maxVar + 1` local variables using the sparse name map; every literal in `phi` lies in this range. The `localFormulaToBinary_satisfiable` equivalence proves both assignment directions.

The parsing direction uses the real `OAI.UniqueGamesTheorem.BinaryLanguage.language`, `BinaryEncoding.decodeFormula`, and the pinned `BinaryParsing.decodeFormula_sound` / `BinaryEncoding.decodeFormula_encoded` results. It does not clone the parser or assume an FP premise. Imports are the runtime source and `OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas`; the latter imports the actual formula, name-machine, and model declarations.

The v5 runtime copies the v4 implementation into a separate successor and removes `run_success_implies_microFold`, whose claimed exact output equation is false for an accepting empty input at state `between0` because the concrete scanner adds the terminal `[false]`. The correct `run_success_implies_machineFold` retains the terminal suffix explicitly. Three calls to `microFold_payload_decomp` now pass the required `MicroState` constructor `.ready q'`.

This is authored source only. No Lean compiler has run on v5, no joint environment compatibility is established, and the theorem and its axiom profile remain unaccepted pending exact-byte capture and GCP checks.

Remaining to-do list: exact-byte capture and GCP compile/repair; then finite-alphabet TM2-to-local Cobham transfer and full joint environment acceptance.