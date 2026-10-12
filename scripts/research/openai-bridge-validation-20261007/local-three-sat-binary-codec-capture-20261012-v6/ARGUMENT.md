# Joint local 3-SAT codec to upstream BinaryLanguage (v6)

This successor joins the concrete local converter to the actual pinned OAI binary SAT parser. Its endpoint is the all-input statement

`w ∈ Complexity.SAT.ThreeSAT.language ↔ OAI.UniqueGamesTheorem.BinaryLanguage.language (convert w)`.

The proof retains the local runtime conversion and its explicit FP witness. Malformed local inputs convert to `[]`, which the upstream parser rejects. Successful local decoding emits the exact upstream `formulaBits` encoding of the sparse-renamed formula, including the empty local formula case, which encodes as `[false]` and parses to the empty upstream formula.

For local variable `n`, the upstream name is `bitsValue (List.replicate n true)`, whose canonical ordinary-binary digits are exactly `n` true bits. This avoids generating an exponential unary expansion. Injectivity follows from the canonical digits and their length. A local finite assignment is extended to the upstream namespace by choosing the unique local preimage for names in the sparse image and assigning false elsewhere. Conversely, restrict an upstream assignment to the first `phi.maxVar + 1` local variables using the sparse name map; every literal in `phi` lies in this range. `localFormulaToBinary_satisfiable` proves both assignment directions.

The parser direction uses the real upstream `BinaryLanguage.language`, `BinaryEncoding.decodeFormula`, `BinaryParsing.decodeFormula_sound`, and `BinaryEncoding.decodeFormula_encoded`; it does not clone the parser or assume an FP premise. Imports are the runtime source and `OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas`, which imports the actual formula, name-machine, and model declarations. Upstream namespace references are fully qualified to avoid collision with local `Complexity.SAT` declarations.

This successor preserves the captured v5 bytes and makes review repairs in v6: the data definition using `Classical.choose` is marked `noncomputable`; the malformed-input proof rewrites directly with scanner equality; the actual upstream clause payload is related to local output with its leading `true` clause marker; and the formula induction accounts for that marker. The v5 runtime repair also remains: it removes the false `run_success_implies_microFold` equation for the accepting empty input at state `between0`, retains the correct terminal `[false]` suffix in `run_success_implies_machineFold`, and supplies `.ready q'` to all three `microFold_payload_decomp` calls.

This is authored source only. No Lean compiler has run on v6, no joint environment compatibility is established, and the theorem and its axiom profile remain unaccepted pending exact-byte capture and GCP checks.

Remaining to-do list: exact-byte capture and GCP compile/repair; then finite-alphabet TM2-to-local Cobham transfer and full joint environment acceptance.