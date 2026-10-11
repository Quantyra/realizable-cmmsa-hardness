# Checks

Author source inspection only; Lean/Lake and the pinned native environment
were not available to this author. No compile, `#print axioms` execution,
GCP run, Git action, or acceptance is claimed. `Checks.lean` records the
intended public theorem and axiom audit for compiler custody.

The core proof explicitly instantiates the universal inverse from
`fixed_coordinate_real_inverse_agreement` for every half-density table, and
the actual all-candidate event mass from
`numeric_actual_failure_mass_lt_one` for the fixed union cover. It then calls
`good_cover_mass_lower_bound` and the distinct-advice Gaussian sum theorem.
There is no inverse, bad-mass, candidate-count, or cardinality premise in the
new public theorem. The inverse's entire dependent existential is transported
from dimension `leafT+leafK` to `2h` along the selected equality; table and
density casts use that same equality. The core bound preserves the actual
original density as `D/(8*m*2^(4h^2))`; two public corollaries give
`S/(4*m*2^(4h^2))` from `D≥2S` and `S/(2*m*2^(4h^2))` from `D≥4S`.
These transports and corollaries need native validation.
