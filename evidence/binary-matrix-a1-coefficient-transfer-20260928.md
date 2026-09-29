# A1 first-stage Fourier coefficient transfer

`BinaryMatrixA1CoefficientTransfer.carrierFourierCoeff_sum_characters` proves the exact coefficient of a finite sum of characters on `Hom(V/A,B)`. Each source term contributes precisely when its induced frequency equals the queried frequency, so collisions are summed rather than discarded. `initialDerivative_fourierCoeff` applies this to the first manuscript hybrid derivative for every coordinate dimension, subspace pair, arbitrary fixed affine base `T`, function `f`, and output frequency `Z`.

The derivative is given by the actual ambient Fourier coefficients and hybrid selector, with character evaluated at `T+j_B N q_A`. `initialDerivative_character_sum` uses the exact cyclic trace phase to express it as a character sum on the quotient carrier. The generic `traceCharacter_carrier_base_general` also proves cyclic phase transport on the intermediate quotient/subtype carrier for the second A1 derivative.

These are force-bearing components of manuscript (A1), including finite normalization and coalesced frequencies. Full A1 still needs the second filtered frequency sum collapsed through the coefficient equality, nested selector equivalence, and arbitrary-base phase/composition law. The numerical NO-soundness gap is unchanged.
