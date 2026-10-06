# Retry-71 ParentFactorization repair offer

This is a source-only successor to the immutable retry-70b/CF9 ParentFactorization offer. The unchanged checks file is copied byte-for-byte from CF9. No frozen capture, prior offer, compiler/controller file, or repository Git state was modified.

The repair addresses the complete ParentFactorization diagnostic packet for run `cmmsa_a8_output_20261006T173127Z_4511df96`. Changes are limited to imports/namespace opens needed to resolve captured declarations, ordinary Lean API and coercion repairs, explicit field-alias normalization for rank arithmetic, replacing unavailable `Submodule.map_map` rewrites with a local inverse-equivalence proof using captured `Submodule.map_comp`, and proof-body normalization for the existing endpoint and reindex arguments. Both parent branches continue to use the original strict lower-induction witness. The theorem statements, premises, rank bound, and options are unchanged; no axiom, sorry, heartbeat change, carrier redesign, or current-level oracle was added.

The 7 previous `simp`-argument warnings in the codomain-hyperplane branch are removed by replacing the warning-producing simp rewrites with the explicit quotient-rank and endpoint-cost derivations. The `try simp` warning in the nonzero-submodule witness helper is removed by simplifying the membership hypothesis directly. The `sorry`/unused-hypothesis warnings were parser/elaboration fallout in the captured run and are expected to clear when the declarations elaborate; this authoring report does not claim that compiler result.

The source was written as UTF-8 without a BOM and checked for remaining `?` characters and malformed `??[F]` placeholders; neither remains. No local Lean, Lake, or Elan command was run. Compiler/Git verification and immutable capture are pending Sol's custody process. No mathematical acceptance or native-claim status is asserted.

## SHA-256

- ParentFactorization source: `E4BBBD5764E0703CC9EEC00605E950A79A8C7F8DA09CBE90AA4336E9E6186E2B`
- Unchanged checks file: `FF0B1F32E7581F0893A3D08DDEE8A0139AA59E45F12FF720B773E2915BFDB7D6`
- Unified diff against immutable retry-70b/CF9 source: `FCC6FB10812C82616CFA66AC81BA71628E99A2614BDEE00E2B78761269396A09`
