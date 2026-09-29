# Encoded source-to-tagged-PCP stage: first missing interface

Status: **INCOMPLETE**. This is a source and Lean-interface audit, not a new
runtime theorem or a certificate of Theorem 1.

The externally supplied MZ reduction in
`ActualMZOuterSourceContract.lean` gives an FP `SeededMap` with zero coins and
an output bit string parsed by `OuterEncoding.decode`. The parser is an
unconstrained function `Bits → Option Encoded3Lin`; the external structure has
no inhabitant in this repository. For a parsed `E`, the proved
`occurrenceOfEncoded E` in `ActualOuterEncodedOccurrenceYesBridge.lean` is the
actual copied-occurrence input, and the source violation count is preserved.
The late copy count, positive-error assignment, all required finite geometric
fibres, and declared-draw YES rejection bound are likewise proved there,
conditional on the external source structure and SAT YES input.

The **first missing encoded theorem/interface** is a bit-level realization of
that semantic map: a fixed tagged-PCP instance encoding and a total FP
transducer on the *MZ output bits* whose decoded value is the actual padded
copied-occurrence/tagged construction for every successfully parsed
`Encoded3Lin`. Its correctness statement must commute with
`OuterEncoding.decode`, and its runtime bound must keep the exponent fixed
when the manuscript's `L` and the NO parameters are fixed, even though the
later positive `τ`, selected `ε`, and copy count may affect constants.
Neither the target tagged-PCP codec nor that transducer/correctness theorem
currently exists. In particular, the arbitrary `OuterEncoding.decode` alone
does not supply a computable source-row parser or a polynomial relation
between source bit length and `E.rows`/`E.vars`.

There are useful local components: `ActualOccurrenceLookup.lean` proves FP
owner lookup for its explicit unary triple wire;
`ActualOccurrenceScan.lean` proves FP ordinal scanning on the same wire;
`ActualOccurrenceAllocation.lean` bounds the finite copied row count by a
fixed multiple of the source row count. These are not a producer for the
tagged PCP description. `ActualTaggedOrderedSampleNonempty.lean` constructs
the finite padded ordered star law with nonempty fibres, but gives neither a
bit-level sampler nor the center/leaf enumeration machine. The existing
`CMMSACodec.lean` encodes a different final CMMSA data tree and explicitly
disclaims a full polynomial-time reduction.

Consequently no fixed-parameter source-to-tagged-PCP `SeededMap`, polynomial
output-length bound, polynomial-magnitude denominator bound, or encoded
center/leaf enumeration is certified here. Such claims would require the
missing bit-level target and source compatibility theorem before the local
lookup and count facts can be composed into an FP proof. The HN compilation
and NO decoder remain separate dependencies; this audit does not absorb them
into the MZ contract.
