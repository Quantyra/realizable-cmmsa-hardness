# Counting proof wording erratum

The review packet and the Lean module header describe the `i > d` case as
covered by the `i ≤ d` guard of `GrassmannCounting.card_frame`. That wording
is inaccurate. The guard is used only in the in-range branch of
`card_surjective_coordinate_maps`; the out-of-range branch is proved
explicitly at `ActualFiniteBinarySurjectionCounting.lean:112–124`.

There, `i > d` implies the subtype of `i`-frames in the `d`-dimensional
coordinate space is empty, so its cardinality is zero. The proof separately
shows `frameProduct d i = 0` using the factor indexed by `d`. The theorem
therefore covers all widths by an explicit out-of-range proof, not by the
`card_frame` guard. No theorem statement or proof was changed by this note;
the green Lean source and Checks pins remain unchanged.
