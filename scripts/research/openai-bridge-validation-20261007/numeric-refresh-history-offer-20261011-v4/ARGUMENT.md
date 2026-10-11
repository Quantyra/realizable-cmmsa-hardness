# Actual refresh count bounds — v4 argument

Status: source-level mathematical argument and uncompiled Gaussian translation candidate for E002/S3137. This offer is disjoint from immutable v3. It makes no native acceptance or compiler claim.

## Exact Gaussian bounds

For `0 ≤ b ≤ N`, the pinned identity at `m=b` is

`gaussian(N,b) / gaussian(b,b) = 2^(b(N-b)) * normalizedFrame(N,b) / normalizedFrame(b,b)`.

The exact lower bound follows from `gaussian(b,b)=1`, `normalizedFrame(b,b)≤normalizedFrame(N,b)`, and positivity of the denominator: `2^(b(N-b)) ≤ gaussian(N,b)`.

For the upper bound, every normalized-frame factor lies in `[0,1]`, so `normalizedFrame(N,b)≤1`. Splitting the last factor gives `normalizedFrame(b,b)=normalizedFrame(b,b-1)/2` for `b>0`; the existing half bound gives `normalizedFrame(b,b-1)≥1/2`. Thus `normalizedFrame(b,b)≥1/4` and `gaussian(N,b)≤4*2^(b(N-b))`. At `b=0`, both Gaussian count and power are one.

## Actual Zoom cardinality and lower bound

For actual `Q : Grass V a` and `P : DecodedPair Q d`, the zoom is the subtype of actual `d`-spaces `L` satisfying `Q.val ≤ L.val ∧ L.val ≤ P.W`. The pinned `GrassmannFlagPosterior.card_relativeUpper` identifies its `Nat.card` exactly with `gaussian(finrank P.W-a,d-a)`. The actual finite-instance conversion identifies that with `Fintype.card (Zoom Q P)`, and `candidateZoom` has the same cardinality.

Write `c=codim P.W`, assume `finrank V=n`, `a+c≤r`, `r≤d`, and `r+d≤n`. Then `finrank P.W=n-c`. The budget gives `d-r≤d-a` and `n-r-d≤n-c-d`; the guards make these terms nonnegative. Therefore `(d-r)(n-r-d)≤(d-a)(n-c-d)`. Apply the exact Gaussian lower bound with `b=d-a` and `N=n-c-a`, whose exponent is `(d-a)(n-c-d)`. Monotonicity of `2^k` gives

`2^((d-r)(n-r-d)) ≤ Fintype.card (Zoom Q P)`.

For `d=2h` this is `2^((2h-r)(n-r-2h))`. The guards `r≤h` and `n≥8h+4r+16` imply all dimension and subtraction guards above.

## Actual dependent Candidate cardinality

The actual carrier is `Σ a : Fin (r+1), Σ Q : Grass V a.val, {P : DecodedPair Q d // a.val + codim P.W ≤ r}`.

For each admissible `(a,c)` with `a+c≤r`, count the larger carrier consisting of an ambient `W` with `codim W=c`, any `Q : Grass V a` (forget the actual `Q.val≤W` condition), and an actual functional `g : Module.Dual (ZMod 2) W`. The candidate injects into the disjoint union of these carriers by retaining `a`, setting `c=codim P.W`, and retaining `P.W`, `Q`, and `P.g`. The budget gives `a+c≤r`. Retained data reconstructs the decoded pair and advice; proof irrelevance identifies proof fields. This keeps the actual dependent candidate rather than replacing it by an unrelated random-variable carrier.

For `finrank V=n`, each slice has these bounds:

- The actual dual-annihilator map injects codimension-`c` subspaces into `Grass (Module.Dual (ZMod 2) V) c`, so `#W≤gaussian(n,c)`.
- `#Q=gaussian(n,a)`.
- Finite-dimensional duality and `Module.card_eq_pow_finrank` give `#g=2^(n-c)`.

Applying the Gaussian upper bound twice gives

`#W * #Q * #g ≤ 16 * 2^(c(n-c)+a(n-a)+n-c)`

`≤ 16 * 2^(n(a+c+1)) ≤ 16 * 2^(n(r+1))`.

There are at most `(r+1)^2` admissible `(a,c)` pairs. Hence the actual dependent type satisfies the manuscript estimate

`Fintype.card (Candidate V d r) ≤ 16 * (r+1)^2 * 2^(n(r+1))`.

This count does not assume `Q` independent of `P`; it embeds the dependent carrier into a larger carrier that records the same `Q`, `W`, and `g`.

## Source and dependency identities

Copied `ActualRefreshGaussian.lean` bytes equal v3 source SHA-256 `9139E443DAE576293AE036D1248506E0534094DE4245A73CD0ED9B3B146E9448`. Candidate source SHA-256 is `A755C9C92474792C82236CB87C066FC16BB29E19E095DF34075AEC852226B76C`; formal and tail identities are `B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3` and `7B54EE1E137076B252C54C9268083412FE54C2FADC9705170FE4911400D4F538`. Full114 archive SHA-256 is `70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`, mathlib revision `e06eff5f95374108acfaf19f1ff7473aa7771df2`.

## Translation boundary

The copied Lean source contains the exact Gaussian lower/upper proofs and actual Zoom/cardinality bridges. The dependent Candidate slice injection and its cardinality estimate are fully specified above but are not encoded as a Lean declaration in this offer. Sol must translate that bridge in a disjoint successor and GCP-check it. The v3 source is uncompiled; no compiler or kernel evidence is claimed.