# Notation erratum for the W6 bridge derivation

This erratum supplements, and does not alter, `a7-w6-bridge-derivation.md` (SHA256 at issue: `98b5485dcd97e26a6d9a5bc6a85db84aa50812b34265442f1eb300fd9296a9c9`). The formulas in its prose blur a coordinate linear map and its matrix representation; keep these objects distinct in Lean and in any review.

Let `u : U ~= F^m` and `b : B ~= F^r`. The typed frequency is `Z : B -> U`. Define the linear map

`J = u o Z o b^{-1} : F^r -> F^m`.

Define the matrix

`Y = carrierFrequencyEquiv A B Z : BinaryMatrix r m`.

The precise representation identity is `Y.transpose.toLin' = J` (`carrierFrequency_toLin` after instantiating `u` and `b` with the repository's `domainBasis A` and `codomainBasis B`). Thus quotient/output formulas use `range J` and `ker J`, or equivalently `range (Y.transpose.toLin')` and `ker (Y.transpose.toLin')`; rank formulas use `Y.rank`. Do not identify `J` itself with `Y` or use `range Y` where the transpose-linear-map range is required.

For `N : Hom(U / range Z, ker Z)`, the output coordinate map is induced by `u` and `b`:

`ubar : U / range Z ~= F^m / range J`,

`bker : ker Z ~= ker J`,

`N# = bker o N o ubar^{-1}`.

The actual W6 output carrier is `Hom(F^m / range (Y.transpose.toLin'), ker (Y.transpose.toLin'))`. The equality `Y.transpose.toLin'=J` identifies it with `Hom(F^m / range J,ker J)`. The physical embedded input matrix is `bker o N o ubar^{-1}` followed by the kernel inclusion and preceded by the quotient map. Its equality with the matrix-coordinate image of `N` is proved using the `J` identity; no matrix/linear-map conflation is permitted.

The matrix selector uses `w6Precedes Y Y'` on matrices. The typed selector is on maps `Z,Z'`; transport it using `Y'.transpose.toLin'=u o Z' o b^{-1}` and `Y.transpose.toLin'=J`, preserving ranks of the maps and their difference. This erratum is notation only; it does not claim that the formal bridge theorem has been implemented or certified.