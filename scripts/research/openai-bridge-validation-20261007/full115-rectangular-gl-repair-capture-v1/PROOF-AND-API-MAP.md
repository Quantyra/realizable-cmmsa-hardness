# Rectangular GL row-prefix finite-instance bridge repair

Status: uncompiled source offer. The change repairs only the `hcard` instance mismatch in `row_prefix_uniform_mean`; it claims no Lean acceptance or certification.

## Repair and proof route

In the captured Full114 source, `hcard` proves equal `Fintype.card` values for fibers with the decidable-predicate instance present when that local proof was elaborated. At the call to `RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers`, typeclass synthesis chooses the classical predicate decision instance, so Lean rejects `hcard` as an argument even though the fibers have the same underlying types and the cardinalities are mathematically equal.

The successor first converts each fiber-card equality to the instance-independent `Nat.card` equality using `Nat.card_eq_fintype_card`. It then transports that equality back to the `Fintype.card` proposition expected at the generic theorem application. The theorem call receives this `hcardExpected`, so both sides are elaborated with the consumer's local instance. No carrier, mean, sampling law, normalizer, or theorem statement changes.

The surrounding proof is unchanged: `rowPrefix_fiber_equiv` supplies equal fibers; `rowPrefix_fiber_card_eq` gives the cardinal equality; `X?` establishes codomain nonemptiness and a positive fiber size; the generic equipotent-fiber pushforward theorem then identifies the normalized means. The zero-row and zero-complement cases retain the original statements and proof path.

## Exact input and dependency pins

The source input is `full114-native-diagnostic-packet-v1/RectangularGLRowCompletion.lean`, SHA-256 `9409767AA9F0C6BC736B06CA73EF9D7B080A27EF96F6BAF4E41DA5019E7CD0C1`; unchanged Checks SHA-256 `D17BF262EB0E9ABA0110C7E6C6CD51EAFFECE4AC03D68E033C3320383E6984FB`. Diagnostic packet index SHA-256: `88B4D5C260CC78504DC33E717A18B3794FB02CC1DE5ADE1DCB28AEC4B5F85EF3`. The exact Full114 input archive is `C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz`, SHA-256 `70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`.

The imported project helper `RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers` has source SHA-256 `F1DBDBF44468D72573F2B15FACFFD3435A700B5AAB98362E2B70F217777C9B8F` in that archive; its argument explicitly expects `hcard : ? b, Fintype.card (Fiber f b) = k`. Other direct project imports and hashes are listed in `manifest.json`. The Full114 evidence package-source archive is SHA-256 `494F97020D23F28340A2FC74049646C06BF07DF5E62EBA4FC4672C7704AB512D`; its pinned `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card` source member is 4,219 bytes, SHA-256 `AC31F64E47BA76F80C1C9BAB4E58645175A13C23C9175449C41ACD22B1E44F1F`. `Nat.card_eq_fintype_card` is the only new API used; it is used solely to pass through an instance-independent cardinal equality. The source offer has not been compiled.

Candidate source SHA-256 `32490329F5E11E19F7EC26D64A09143BCABE15836156B4656E2422382C0462E7` (18528 bytes); unchanged Checks SHA-256 `D17BF262EB0E9ABA0110C7E6C6CD51EAFFECE4AC03D68E033C3320383E6984FB` (1822 bytes).

## Validation boundary

Imports, all existing declaration headers, Checks, and the local `maxHeartbeats 400000` cap are retained. No Lean/Lake, GCP, or Git operation was performed. UTF-8/no-BOM, delimiter, placeholder, and diff checks are recorded in the manifest. Root owns compiler and immutable capture.
