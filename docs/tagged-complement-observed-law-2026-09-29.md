# Fixed-U tagged complement observed law

Status: **bounded Lean proof; route-final NO soundness incomplete**. This
supersedes the first missing identity recorded in
`tagged-complement-law-first-missing-2026-09-29.md` without changing the
remaining decoder obligation.

`ActualTaggedComplementIncidence.sideConditionalDensity_eq_ordinaryComplementStarDensity`
proves the manuscript complement-law density identity for every actual
occurrence instance `I`, copy count, eligible **fixed** `U`, arbitrary
`t,h,k` with `t ≤ 2h` and `h ≤ J`, and arbitrary **fixed** center table `C`
and globally predrawn selected leaf table `T'`. The left side is the actual
transverse source density from `ActualTaggedMZSideDraw`. The right side draws
a uniform complement `A` of `H_U`, a uniform `t`-center `K ≤ A`, then an
independent uniform ordinary `2h`-leaf in `A` containing `K` for each of the
`k` coordinates. It tests `C,T'` on the same observed full domains
`H_U + L'_i`. The equality concerns the observed domain star and fixed-table
acceptance, not equality of raw transverse and ordinary leaf presentations.

`ordinaryComplementStarDensity` retains the copied-row right-hand-side
checks in `fullAccepts`. In contrast, `ActualChangedAmbient8SBoundary.StarDensity`
tests only agreement of center and leaf restrictions. The pending same-table
bridge therefore requires actual complement density to be **at most** ordinary
`StarDensity`; equality would require a separate row-validity justification.

The proof uses a fixed-center tagged-leaf to full-domain tuple pushforward,
the ordinary complement leaf to full-domain equivalence, exact center to
complement incidence balance, and the pointwise observed-atom weight
identity. `side_fixedCenter_acceptance_mass_eq_full` preserves the same
`C,T'` in the actual acceptance event. The final equality is an exact finite
sum reindex, with no sampler approximation or added loss.

Verification: direct `lake env lean
lean/PvNP/RealizableHardness/ActualTaggedComplementIncidence.lean` exited
zero; `lake build PvNP.RealizableHardness.ActualTaggedComplementIncidenceChecks`
completed **3261 jobs**, exit zero. The Checks file prints exact theorem
types. Its axiom audit for the seven checked bridge results lists only
`propext`, `Classical.choice`, and `Quot.sound`.

The arbitrary-fixed-table representative-selection inequality and explicit
class-collision charge remain upstream in `ActualTaggedFixedUDensityForce`;
this theorem does not re-charge or remove that loss. It has not yet been
applied to the changed-ambient robust 8S decoder, and the inverse,
refreshing, and numeric comparison at the manuscript's double-exponential
`J` remain open. Thus the numeric NO-soundness gap is **unchanged**.

| Review lens | Status | Scope |
| --- | --- | --- |
| Proof adversarial | Pending top-level review | Fixed `U,C,T'`, law normalization, and ordinary leaf equivalence. |
| Complexity theory | Pending top-level review | Link to changed-ambient robust 8S and numeric NO bound. |
| Non-claims boundary | Pending top-level review | Observed density only; no core Theorem 1 or raw-presentation law claim. |
