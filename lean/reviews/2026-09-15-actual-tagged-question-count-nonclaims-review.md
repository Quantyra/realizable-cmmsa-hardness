# Actual tagged-question count: non-claims-boundary review

2026-09-15. Top-level read-only review of the frozen `ActualTaggedQuestionMass` increment, its Checks module, and the canonical fresh-run evidence. No Lean source, compilation, commit, push, release, or public action was performed.

## Verdict

**GO-WITH-NOTES.** The frozen increment stays within the split-A counting boundary. It proves the actual occurrence allocation has conflict degree at most `157`; rewrites the tagged row-universe cardinality exactly as `K * I.rows.length`; specializes the tagged bad-ordered-question theorem to the raw count

```text
J * (J - 1) * 157 * (K * I.rows.length)^(J - 1);
```

and defines the positive arithmetic copy count

```text
actualPaddingCopies J T = 1 + T * (J * (J - 1) * 157).
```

The positivity theorem says only that this natural-number constructor is nonzero. The increment does not normalize the count to a probability, prove a useful retained mass, choose `T` from `tau`, connect the constructor to a target inequality, define or verify an FP producer, condition a law, prove a star or hardness result, resolve P versus NP, or establish novelty or publication readiness.

## Frozen artifacts and evidence

| Artifact | SHA-256 | Result |
|---|---|---|
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionMass.lean` | `7BC31AAB2765EB0E0463751DCF2447230D40FC520F2A2D3948DBF40142C139F7` | Matches the routed freeze. |
| `certifications/realizable-hardness/lean/PvNP/RealizableHardness/ActualTaggedQuestionMassChecks.lean` | `9A39682BB023B6A47D3FDD5C432B492671CB0AA4DA24A6857AC2BB6C199DF82B` | Matches the routed freeze. |
| `research/evidence/2026-09-15-actual-tagged-question-count-fresh-run/artifact-hashes.txt` | `C3B4B5CE10ABF9EB7046187A4464AEDF05B123D353AAA147945A06406055714D` | Matches the routed evidence-manifest hash. |

An independent hash pass verified every one of the 26 entries listed in `artifact-hashes.txt`. The evidence records unchanged before/after source hashes, main and Checks exit codes `0`, empty stderr, and newly emitted object hashes `1741C3CE78523148933F3E186C2604A26E4692DEFBF34D28DF20725DB35D16B2` and `13975746469228B4C2C14A7259F2301681C928EE724217E5127A9CBED5A1A8BB`.

The output root was seeded with 2,802 dependency files from the prior canonical tagged-question-mass bridge target. The two reviewed target objects were excluded and absent before compilation; main then Checks were compiled sequentially. Temporary and probe roots were excluded from `LEAN_PATH`. This is direct fresh compilation of the frozen main and Checks files against a recorded precompiled dependency set, not an independent clean rebuild of every transitive dependency.

The source scan found no `sorry`, `admit`, `native_decide`, or source-level `axiom`. Checks profiles all five public declarations. `actualPaddingCopies` has no axioms; the four proof declarations report only `[propext, Classical.choice, Quot.sound]`. The three main-module messages are style or maintenance lints (`letI`, unnecessary `simpa`, and a no-op `change`), with no effect on theorem scope.

## Exact split-A boundary

`actual_conflict_degree_le` proves, for every actual occurrence row `q`,

```lean
((Finset.univ : Finset I.RowId).filter
  (rowConflict (Finite3LinSource.ofActual I).support q)).card ≤ 157.
```

It transports the previously reviewed construction facts that each support has cardinality three and each global variable occurs in at most four occurrence rows. The final arithmetic specialization is

```text
1 + 3*4 + 9*4^2 = 157.
```

Thus `157` is a conservative upper bound on the conflict-neighbourhood cardinality. It is not an exact conflict count, a probability, a retained fraction, a soundness parameter, or a copy count.

`actual_tagged_row_card` proves the exact finite cardinality identity

```lean
Fintype.card (Fin K × I.RowId) = K * I.rows.length.
```

The right side uses the existing occurrence-row identity `Fintype.card I.RowId = I.rows.length`. Tags therefore multiply occurrence identities; equal source owners are not silently merged.

`actual_tagged_bad_ordered_question_count_le` proves

```lean
((Finset.univ : Finset (Fin J → Fin K × I.RowId)).filter
  (fun u => ¬ GoodOrderedQuestion
    ((Finite3LinSource.ofActual I).taggedCopy K).support u)).card ≤
  J * (J - 1) * 157 * (K * I.rows.length) ^ (J - 1).
```

This is a one-sided raw cardinality bound on bad elements of the full ordered function space. It specializes the generic tagged theorem with the internally proved actual conflict bound and rewrites the base row cardinality. It remains valid at `K = 0`, empty row universes, and small `J`; that generality does not supply the positivity required by a later probability denominator.

`actualPaddingCopies` is a transparent arithmetic definition, and `actualPaddingCopies_pos` proves it is positive because of the leading `1`. The name may be used for this candidate copy-count constructor. The reviewed declarations do not prove that tagged copying preserves an optimum or source value, is computable within a stated complexity bound, has controlled output size, or makes a normalized bad mass less than `1/T`, `tau/100`, `1/4`, or any other threshold.

## Checks boundary

The `smallActual` fixture is an `Instance 1 1`, so its base source parameter is positive. Checks instantiate the raw count theorem with `K = 2` at `J = 0`, `1`, and `2`; verify the row-cardinality rewrite at `K = 2`; and instantiate positivity as `0 < actualPaddingCopies J 4`.

These checks exercise elaboration at the small-`J` boundaries, the concrete tagged cardinality rewrite, and constructor positivity. They do not enumerate an exact bad count, normalize a finite law, compare the resulting ratio with a target, exercise a `tau` parameter, construct an algorithm, or test a conditioned or star distribution.

## Required wording

The strongest justified description is:

> Lean verifies that actual occurrence rows have conflict degree at most `157`, that `K` tagged copies have exactly `K * rows.length` row identities, and that the number of bad ordered tagged `J`-tuples is at most `J(J-1)·157·(K·rows.length)^(J-1)`. It also defines and proves positive the arithmetic candidate `1 + T·J(J-1)·157`. Probability normalization, target-mass selection, producer complexity, conditioning, and downstream star and hardness claims remain outside this increment.

Do not describe this increment as proving or certifying:

- an exact conflict degree or exact bad-tuple count;
- a normalized bad probability or positive retained mass;
- a `tau`-dependent padding threshold or any target inequality for `actualPaddingCopies`;
- value, optimum, degree, or semantic preservation sufficient for a completed padded source;
- a computable, polynomial-time, output-size-bounded, or FP producer;
- a conditioned law, uniformity after rejection, clique resampling, or stationarity;
- star acceptance, a completed randomized reduction, or a hardness consequence;
- P versus NP, another complexity separation, novelty, manuscript correctness, or publication readiness.

## Material findings

1. The actual conflict theorem correctly preserves occurrence-row identities and exports the conservative constant `157`.
2. The tagged row cardinality is exactly `K * I.rows.length` for every natural `K`.
3. The bad-question result is a raw one-sided count, with no hidden probability or nonemptiness premise.
4. `actualPaddingCopies_pos` certifies only positivity of the stated arithmetic constructor; no target-mass consequence is present.
5. The evidence supports the frozen main and Checks targets, subject to the documented seeded-dependency scope.
6. The normalized probability, retained mass, `tau`, producer, conditioning, star, hardness, P-versus-NP, novelty, and publication lanes remain excluded.

No public-claim promotion follows from this review.
