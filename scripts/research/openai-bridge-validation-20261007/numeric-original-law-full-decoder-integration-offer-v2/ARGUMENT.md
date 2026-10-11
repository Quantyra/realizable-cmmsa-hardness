# Argument: actual original-law amplification to the full decoder

This offer composes frozen V2 original-complement amplification, H11 actual center/complement incidence and all-advice correction, and selected H-side full-zoom agreement. The complement/advice law is never conditioned on success.

## Fixed objects and dimensions

Fix `I`, `copies`, `L`, `m`, `samplerA`, `U`, center table `C`, raw tagged table `Traw`, and representative choice `s`. Set `h=hBlock L m`, `J=blocks samplerA h`, `t=leafT m h`, `k=m`, `d=leafT m h+leafK m h=2h`, `r=numericRankThreshold m`, `e=refreshThreshold m h`, and `S=successMargin (badExponent m h)`. The global table is the same `taggedSelectedDomainTable I copies Traw s` on every actual domain. Every selected star and good-advice object has arity `k=m`; `samplerA` determines `J` and the law parameter only.

## Original A-first event mass and all-advice probability

V2 `actual_original_law_amplification`, applied to the actual C and the leaf table determined by `Traw,s`, supplies `a : Fin (r+1)` such that the literal event

`actualComplementSuccess(A,Q) := exists P : DecodedPair Q d, a.val+codim P.W=r and e/2 < agreement (transportedLeafTable A Tglobal) Q P`

has original A-first mass at least `B1=2*S^2/(m*2^(4*h^2)*(r+1))`. This is the exact atom-weighted sum over actual complements A and uniform actual `Grass A.1 a.val` advice Q. No successful-complement renormalization occurs.

For each success, H11's incidence equivalence sends `(A,Q)` to the actual transverse center `K=(centerInComplementEquiv A a.val Q).1`; the embedded advice is `K.1`, and the same A, pair, table, and agreement are retained. Let `F(K)` existentially state that actual A, Q and a successful ordinary pair induce precisely K. The pointwise implication follows by incidence inversion. H11 arbitrary-event reindexing gives `uniformLaw (SideCenter I copies U a.val) {K | F K} >= B1`.

The positive A-first mass gives an actual successful `(A,Q)` by finite-sum positivity and hence a concrete `K0` for H11's `Nonempty`-dependent marginal theorem. Its transverse fraction is at least `B1`. H11 `actualAllAdvice_transverseEvent_mass_lower` moves this event to the full Grassmann carrier and subtracts the exact `delta=1/2^(2*J-a.val-1)`. Numeric guards establish `a.val<=r`, `J=blocks samplerA h`, and the theorem's slack. The robust-real `numeric_all_advice_probability_lower` at `(m,h,samplerA,a.val)`, after weakening `(r+1)` to `(r+1)^3`, gives

`2*S^2/(2^(4*h^2)*m*(r+1)^3) - 2^(a.val+1)/2^(2*J) >= 2^(-6*h^2)`.

The dyadic correction is exactly delta after rewriting the exponent with the selected guards. Therefore at least `2^(-6*h^2)` of uniform `Grass (E I copies U) a.val` advice has a favorable actual full decoder. The correction is not dropped and no conditional law is substituted.

## Actual ordinary witness to actual H-side full decoder

For a successful actual `(A,Q_A,P)`, set `Kc=centerInComplementEquiv I copies U A a.val Q_A`. Then `Kc.1` is the side center, `Kc.2` gives containment in A, and `Kc.1.1.val=Q_A.val.map A.1.subtype`. Let `W'=P.W`, `g=P.g`. The side-window containment `Kc.1.1.val<=sideWindow A W'` follows from `P.hQW` and `complement_map_le_sideWindow_iff`.

The bounded ordinary carrier is `{L : OrdinaryLeaf I copies U A Kc.1 Kc.2 h // L.1.val<=W'}`. It and `Zoom Q_A P` have the same underlying Grassmann carrier `Grass A.1 (2*h)`. Their only differing field is center containment: `OrdinaryLeaf` asks `Kc.1.val.comap A.1.subtype<=L.1.val`, while Zoom asks `Q_A.val<=L.1.val`. The equality `Kc.1.val.comap A.1.subtype=Q_A.val` follows from `Kc.1.1.val=Q_A.val.map A.1.subtype` and `Submodule.comap_map_eq_of_injective A.1.injective_subtype`. This gives the subtype equivalence without mapping any leaf. On that shared carrier, prove the local pointwise event bridge directly from `actualOrdinaryAgreement`: its equality `g.comp (Submodule.inclusion hLW)=transportedLeafTable ... L.1` is equivalent, by `LinearMap.ext` and symmetric `LinearMap.congr_fun`, to `AgreesOn` for P and the same `Tglobal`. `rationalAgreement_eq_of_carrierEquiv` then identifies the exact finite agreement fractions.

Since `e/2>0` and success agreement exceeds `e/2`, `zoom_card_ne_zero_of_pos_le` gives a nonempty ordinary Zoom. Map one leaf through the inverse carrier equivalence and then `A.1.subtype` to obtain `SideLeaf I copies U h Kc.1`. Transversality follows from `equation_map_eq` and `A.2`; K containment follows by mapping `Q_A<=L`. This leaf yields a nonempty bounded OrdinaryLeaf. `boundedOrdinaryFullEquiv` yields a nonempty bounded SideFullDomain. These are the nonemptiness witnesses required by H11 `actualSideLeaf_k1_originalRatio_eq_ordinaryRatio`; none is independent of the original success.

The ordinary agreement ratio equals the original success ratio. H11's ratio identity makes it the original H-side `SideLeaf` conditional ratio for `(W',g)`. Apply `selected_actual_hside_full_agreement` with the same `Traw,s`; it yields full-zoom agreement greater than `e/3` for `sideDecodedPair` on `totalHLeafTable`. The pair has advice K, window containing K, and decoder exactly `H + W'` with canonical RHS extension on H and g on W'.

The exact budget `a.val+codim P.W=r`, `sideWindow_finrank_budget`, and the ambient coordinate dimension `finrank E=3J` show that the canonical side window has ambient codimension `codim P.W`; hence that codimension is at most `r`. The window contains H by its left-summand inclusion. The restriction of `sideExtensionOnWindow` along this inclusion is exactly `sideCanonicalRhs`, by `sideExtensionOnWindow_restrict_H`.

For the public full-decoder endpoint, take the favorable witness `(A,Q_A,P)`. The stored embedding equality identifies the center Grass object `K.1.1` with the requested ambient advice `Q`: subtype extensionality reduces this equality to equality of their underlying submodules. Transport the entire dependent value `sideDecodedPair ... K.1 hKW : DecodedPair K.1.1 (2*h)` along that equality using `Eq.mp` and `congrArg (fun Q => DecodedPair Q (2*h))`. This preserves both the side window and its functional. The transported pair has codimension at most `r`, contains H, restricts to the prescribed `sideCanonicalRhs` on H, and retains the same canonical total-H-table agreement above `e/3`.

## Claim boundary and static checks

This argument is not compiler/kernel evidence. The finite carrier equivalence and exact event transport still require static and mechanical checking by Sol. Any failure must be recorded against this disjoint offer; V2, H11, and all captured inputs remain immutable. All four imported proof sources remain uncompiled/unaccepted, including the Full114 archive-backed baseline.

## V2 static repairs

V1's subtype equality proof reversed the stored embedding equality. V2 first proves `QA.val.map A.1.subtype = Kc.1.1.val`, then composes its symmetry with the favorable witness equality `QA.val.map A.1.subtype = Q.val` to obtain `Kc.1.1 = Q` by `Subtype.ext`. The complete dependent `DecodedPair` remains transported along that equality. V2 also uses explicit `Submodule.inclusion` applications for the public H restriction and the canonical side-window restriction, and pins the captured H12 and Amplification V3 sources. This is static source work only; no compilation or acceptance is claimed.
