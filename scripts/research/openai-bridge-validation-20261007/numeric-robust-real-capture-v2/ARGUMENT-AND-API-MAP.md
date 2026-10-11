# Real robust cutoffs at the existing floor

Status: root-authored uncompiled candidate. This source translates the complete
2026-10-10 arithmetic argument already recorded in the planning note
`docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md`.
It does not prove the finite refresh law, adaptive history, many-Q output,
canonical row extension, source decoder, or actual source NO promise.

The numeric specialization uses exactly `numericHnum`, `numericRankThreshold`,
`blocks`, and the previously offered `numeric_robust_dimension_guards`. That
dependency is also uncompiled. No larger height, ambient upper bound, favorable
table, conditioned successful-complement law, or final decoder premise is added.

## Exact total failure probability

Write e for the reciprocal-square Real threshold, n=2 blocks(A,h), and r for the
existing rank threshold. The source defines B=ceil(8*2^(rn)/e)+1, the manuscript's
actual finite horizon, and E=(2h-r)(n-r-2h)+2-4h as a natural exponent. The signed
Real equality is separately exported, proving that its subtractions are honest.

For arbitrary e>=1/2^(2h), B<=2^(rn+2h+4), directly from Nat.ceil_le and the
integer upper bound 2^(rn+2h+3) for the expression inside the ceiling. There is
no asymptotic estimate or replacement of the horizon. Since r+1<=2^r, the
candidate factor D=16(r+1)^2*2^(n(r+1)) gives B*D<=2^K where
K=n(2r+1)+2h+2r+8. The existing dimension guards give E>=4, hn<=2E,
K+1<=3hn, and hn>=256. Induction proves k^2<=2^k for k>=4. Thus
2^E/12 >= (hn)^2/48 > 3hn >= K+1. The elementary exp identities and 2<=exp(1)
yield B*D*exp(-2^E/12)<exp(-1)<1/2. The last strict inequality follows from the
quadratic lower bound for exp(1), not a numerical approximation to e.

The threshold theorem proves both e>=1/2^(2h) and 2/2^(2h)<=e/2.
The existing floor implies h>=b^2, so rho^2*h>=1 for rho=1/b. This gives
2-2h<=-2(1-1000rho^2)h. Monotonicity of Real.rpow proves the required factor4
bound and hence both conclusions. The selected numeric total-failure theorem
supplies every arithmetic premise from the original floor.

## Advice correction

For S>=1/2^(2mh), let D=2^(4h^2)*m*(r+1)^3. The natural guard
4mh+m+3(r+1)+1<=h^2 and m(r+1)^3<=2^(m+3(r+1)) imply
2^(4mh)*D<=2^(5h^2). Hence the unconditioned many-Q bound 2*S^2/D is at least
1/2^(5h^2). For a<=r and n>=5h^2+r+2, the all-Q error
2^(a+1)/2^n is at most 1/2^(5h^2+1). Subtraction leaves at least
1/2^(5h^2+1)>=1/2^(6h^2). All denominator positivity is retained explicitly.
The numeric theorem supplies S as the Real cast of the exact rational
`successMargin (badExponent m h)`. The source definition gives
badExponent<=2mh without a new divisibility premise, so the needed S bound is
obtained by monotonicity of integer powers and reciprocals.

The probability expression is written using ratios of positive integer powers.
Identifying this arithmetic bound with the actual unconditioned advice event
still requires the refresh/many-Q/H-extension/incidence proofs. These statements
do not supply an event or witness by themselves.

## Pinned API evidence and verification boundary

Mathlib revision: e06eff5f95374108acfaf19f1ff7473aa7771df2.
`Nat.ceil_le` was read in `Mathlib/Algebra/Order/Floor/Defs.lean` from the retained
Full107 exact review-source record. The Real power identities and monotonicity
were read in the corresponding retained `Analysis/SpecialFunctions/Pow/Real.lean`.
`Real.exp_nat_mul`, `Real.exp_add`, `Real.exp_neg`, `Real.add_one_le_exp`, and
`Real.quadratic_le_exp_of_nonneg` were inspected in the pinned upstream source:
https://raw.githubusercontent.com/leanprover-community/mathlib4/e06eff5f95374108acfaf19f1ff7473aa7771df2/Mathlib/Analysis/Complex/Exponential.lean

The manifest pins the exact direct project sources and the original failed
Full114 input archive. A future native package must rebind to the accepted
operator successor; this offer creates no execution archive. UTF-8, glyph,
public request and source hash preflights do not establish Lean elaboration or
kernel correctness. Six public declarations and all six fresh axiom requests
are included; GCP compilation and required independent reviews remain open.

## Disjoint v2 source repair

After Sol acknowledged immutable v1 capture CA49087DCA8531CBFE4954E57351F5A314B1B71DE916FE1CDAF67A5008592052, root replaced the private horizon proof of 1<=2^k by an explicit Nat.one_le_pow invocation. This avoids relying on positivity to prove a lower bound with left side one. The change reverses exactly to the preserved v1 bytes. All six public statements, definitions and Checks are unchanged. This is a source-level repair, not a compiler result.
