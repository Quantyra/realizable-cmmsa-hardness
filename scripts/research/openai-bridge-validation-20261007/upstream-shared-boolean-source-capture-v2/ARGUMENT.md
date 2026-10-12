# Shared Boolean source transport: upstream offer v2

This offer transports the pinned uncloned binary source reduction into the literal shared Boolean parity interface. It belongs in the original upstream environment at Lean 4.34.1 and mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. It is an uncompiled candidate, not an accepted theorem or a verified cross-toolchain import.

`BooleanParityInput.lean` is byte-identical to the shared interface candidate in `shared-boolean-parity-input-capture-v1` (SHA256 `704B76A68488A6473613A2B69C53A962A54E9914AC298FE24CFAED78865A1414`). Its path in the upstream environment is `lean/PvNP/RealizableHardness/BooleanParityInput.lean`. `SharedBooleanSource.lean` is copied byte-for-byte from inherited offer v1; no inherited bytes were edited. Its expected upstream path is `lean/OAI/Quantyra/SharedBooleanSource.lean`. The original uncloned source adapter is the captured v1 module at `lean/OAI/Quantyra/UnclonedBinarySource.lean`, source SHA256 `59DE2FA84DF55CD04FB30C4EC72D9B00F212B02FC6843787BD198C37A447F056`.

For each equation, the two constructors preserve the four fields and are inverse by cases. Mapping equation lists preserves order, multiplicity, length, and nonemptiness; the input maps are inverse. The shared satisfaction Boolean is definitionally the original `CloneGap.satisfied`. The failed-entry count is therefore the same list count. The complement-count lemma proves failed plus satisfied entries equals list length. Since the list is nonempty, division by its length and upstream `HastadSource.failure_add_success` yield the exact equality `BooleanParityInput.failureRate (toShared I) a = (HastadSource.asSource I).failure a`. The `inputWords` theorems explicitly retain each ordered four-word equation row, including repeated rows and owners.

`sharedBits` is defined by applying the original `SourceEncoding.inputBits` to the inverse map. The roundtrip theorem shows that a transported output serializes to exactly the original output bit list. `transportComputation` reuses the original TM2 auxiliary machine and time polynomial, and discharges its output field with this exact equality. The finite-alphabet witness is reused from the original computation. Thus no polynomial-time cost is asserted for a newly executed list conversion.

The exported `Reduction ε` retains arbitrary positive rational YES error and fixed raw NO failure at least `1/4`, with an actual computation and finite-alphabet witness. `exists_reduction ε positive` delegates to the captured upstream source theorem. This bundle makes no claim that the source or shared module compiled, that their dependency closure passed an axiom audit, or that either module imports successfully in the CMMSA toolchain. Encoded occurrence production, local runtime conversion, smooth-game compatibility, manuscript transfer, and all downstream acceptance and review gates remain open.

## Pinned upstream API dependencies

The byte-pinned readback is `upstream-uncloned-binary-source-readback-v1/result.json` (SHA256 `8B52463294CA180A43B7070C19256560A0E8F94C3A3C1930521A481750DB16B1`) at upstream revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It verifies the following source blobs:

- `SourceEncoding.lean`: `BDCA10116E729EB88B26CE63A77A099905CC8CC9BE2B06EF4A706CA47B8AC845`
- `CloneGap.lean`: `F2322290F5F33A575C27FD09213E8E56AF41427A50C349BA192C8DFF1F4E357C`
- `TableGapReductionLemmas.lean`: `FA173F78419F7643578D850B5DB40BDBF9BA961902CC822CF5C21C04235332A8`
- `MachineBinaryInputReductionLemmas.lean`: `6E17E44283D03EF0EB55BB4D164F3F8F8356AF9A8CFBF19734BCD9F826281E02`
- `MachineBinaryParsingLemmas.lean`: `FD748296ADA3050ADCCD1C834F467B0A580330CB8C6CFBB461E53F1CF682F926`
- `ActualSourceLemmas.lean`: `C4AFD459BB8A4CA1DDF285EDF4A10E88174B72AA45C23CD1237D87EF1F3D7CAF`
- `SourceGapLemmas.lean`: `3E8B9E3CC9A4501E530D8DEC62BBFB6924D9FABB2A7DCAB7DCBAD97BA8D9CCDC`
- `TableGapReductionLemmas.lean` and the three upstream build files are also recorded in the readback and prior adapter manifest.

The planning argument is `docs/research/pvnp/openai-math-source-bridge-crosswalk-2026-10-06.md`, section “2026-10-11 Shared literal interface and exact machine-output transport argument”, committed head `efc7f45`, section SHA256 `D23149B02E90565BCE84E5016171C3D70BBCDFE912061447080BAB09C40BBE41`.

## Verification status

No Lean command was run for this offer. `Checks.lean` requests declaration types and axiom profiles for the public transport statements. Acceptance, compiler status, and independent review remain false until exact GCP capture and review evidence are attached by the designated compiler/research workflow.