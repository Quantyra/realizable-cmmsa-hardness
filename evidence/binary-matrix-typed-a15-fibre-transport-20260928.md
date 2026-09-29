# Typed A15 affine-fibre transport

`BinaryMatrixTypedA15Transport` defines the actual affine restriction of
the manuscript A1 carrier `Hom(V/A,B)` with arbitrary fixed base, domain
constraint, and codomain variation subspace. It uses one fixed pair of
finite bases to identify this carrier with a coordinate binary matrix
space. `coordinate_fibre_image` proves that every typed fibre maps
bijectively to its coordinate actual affine fibre;
`coordinate_fibre_energy` preserves normalized complex norm-square
exactly, including empty fibres. `coordinate_order` preserves the actual
order, including zero-dimensional quotient and subtype carriers.
`coordinate_typedOfCoordinate` shows every coordinate actual affine
restriction arises from a typed one, so this comparison preserves both
directions of the globalness quantifier. The base is mapped by the same
matrix equivalence in every theorem.

This comparison is the quantified premise/conclusion bridge needed to
apply the complex coordinate A15 one-step bound at an arbitrary A1
carrier. The line/hyperplane translation distributions, polynomial P,
rank projection, and hybrid derivative still require conjugacy under
this chosen basis. Thus arbitrary-carrier A14/A15 and peeled influence
A15 remain open. The numeric NO-soundness gap is unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA15TransportChecks`
passed (2293 jobs). Fibre energy, order, and coordinate-surjectivity axiom
audits report only `[propext, Classical.choice, Quot.sound]`.
