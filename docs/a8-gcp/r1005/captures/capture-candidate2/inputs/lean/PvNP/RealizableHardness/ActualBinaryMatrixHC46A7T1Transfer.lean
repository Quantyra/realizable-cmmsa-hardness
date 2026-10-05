import PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Incidence
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport

/-! T1 exact-transfer structures on the actual finite F2 carriers.

The index triple is represented by C <= A, the quotient subspace H/B <= W/B,
and the manuscript isomorphism H/B ~= A/C.  The actual ambient H is recovered
as the preimage of H/B under W -> W/B.  This representation keeps the
quotient carriers explicit; it does not identify the quotient isomorphism,
its pullback H -> V/C, and the original map q_C Y|H.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer

open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7WeightedPredecessor
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Convolution
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7HybridW6Transport
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.ActualBinaryMatrixHC46TypedFourierTransport
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18DerivativeRankProjection
open PvNP.RealizableHardness.BinaryMatrixA1CharacterBridge
open PvNP.RealizableHardness.ActualBinaryMatrixHC46DR6Incidence

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d -> F
private abbrev W (n : Nat) := Fin n -> F

/-- A T1 index triple. `K` is the actual quotient subspace H/B in W/B;
`Xbar` has the manuscript direction H/B ~= A/C. -/
structure T1IndexTriple {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) where
  C : Submodule F A
  K : Submodule F (W n ⧸ B)
  Xbar : K ≃ₗ[F] (A ⧸ C)

/-- Encode the triple by theta : A -> W/B, with the quotient map first,
then Xbar inverse, then the inclusion H/B -> W/B. -/
def t1TripleToMap {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) : A →ₗ[F] (W n ⧸ B) :=
  t.K.subtype.comp (t.Xbar.symm.toLinearMap.comp t.C.mkQ)

/-- Build the quotient triple associated to theta using its kernel and range.
C is the kernel subspace inside A; its ambient image in V is induced by A's
subtype. K is im(theta)=H/B. -/
def t1MapToTriple {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (theta : A →ₗ[F] (W n ⧸ B)) : T1IndexTriple A B where
  C := LinearMap.ker theta
  K := LinearMap.range theta
  Xbar := theta.quotKerEquivRange.symm

/-- The map-to-triple-to-map direction recovers theta on every vector. -/
theorem t1TripleToMap_mapToTriple {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (theta : A →ₗ[F] (W n ⧸ B)) :
    t1TripleToMap (t1MapToTriple theta) = theta := by
  classical
  ext a
  change ((theta.quotKerEquivRange (Submodule.Quotient.mk a) :
    LinearMap.range theta) : W n ⧸ B) = theta a
  rw [LinearMap.quotKerEquivRange_apply_mk]

/-- The map encoded by a triple has exactly C as its kernel. -/
theorem t1TripleToMap_ker {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    LinearMap.ker (t1TripleToMap t) = t.C := by
  ext a
  simp [t1TripleToMap]

/-- The map encoded by a triple has exactly K=H/B as its range. -/
theorem t1TripleToMap_range {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    LinearMap.range (t1TripleToMap t) = t.K := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact (t.Xbar.symm (t.C.mkQ a)).property
  · intro hy
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective t.C (t.Xbar ⟨y, hy⟩)
    have heq : ((t.Xbar.symm (t.C.mkQ a) : t.K) : W n ⧸ B) = y := by
      change ((t.Xbar.symm (t.C.mkQ a) : t.K) : W n ⧸ B) = y
      rw [ha]
      simp
    exact ⟨a, heq⟩

/-- Reconstructing the index triple from its encoded map recovers C and K. -/
theorem t1MapToTriple_CK_roundTrip {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    (t1MapToTriple (t1TripleToMap t)).C = t.C ∧
      (t1MapToTriple (t1TripleToMap t)).K = t.K := by
  constructor
  · exact t1TripleToMap_ker t
  · exact t1TripleToMap_range t

/-- The map encoding is injective: its kernel, range, and the induced
quotient isomorphism recover all three fields of the index triple. -/
theorem t1TripleToMap_injective {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    {t s : T1IndexTriple A B}
    (h : t1TripleToMap t = t1TripleToMap s) : t = s := by
  cases t with
  | mk tC tK tX =>
    cases s with
    | mk sC sK sX =>
      have hC : tC = sC := by
        calc
          tC = LinearMap.ker (t1TripleToMap ⟨tC, tK, tX⟩) :=
            (t1TripleToMap_ker ⟨tC, tK, tX⟩).symm
          _ = LinearMap.ker (t1TripleToMap ⟨sC, sK, sX⟩) := congrArg LinearMap.ker h
          _ = sC := t1TripleToMap_ker ⟨sC, sK, sX⟩
      subst sC
      have hK : tK = sK := by
        calc
          tK = LinearMap.range (t1TripleToMap ⟨tC, tK, tX⟩) :=
            (t1TripleToMap_range ⟨tC, tK, tX⟩).symm
          _ = LinearMap.range (t1TripleToMap ⟨tC, sK, sX⟩) := congrArg LinearMap.range h
          _ = sK := t1TripleToMap_range ⟨tC, sK, sX⟩
      subst sK
      have hX : tX = sX := by
        apply LinearEquiv.ext
        intro k
        obtain ⟨a, ha⟩ := Submodule.mkQ_surjective tC (tX k)
        have hback : tX.symm (tC.mkQ a) = sX.symm (tC.mkQ a) := by
          apply Subtype.ext
          exact DFunLike.congr_fun h a
        have hvalue := congrArg sX.toLinearMap hback
        simpa [ha] using hvalue.symm
      subst sX
      rfl

/-- Actual index triples and maps A -> W/B are equivalent in both
directions, with the two inverse laws proved above. -/
noncomputable def t1TripleEquiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    T1IndexTriple A B ≃ (A →ₗ[F] (W n ⧸ B)) where
  toFun := t1TripleToMap
  invFun := t1MapToTriple
  left_inv t := by
    apply t1TripleToMap_injective
    exact t1TripleToMap_mapToTriple A B (t1TripleToMap t)
  right_inv theta := t1TripleToMap_mapToTriple A B theta

noncomputable instance t1TripleFintype {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype (T1IndexTriple A B) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (W n ⧸ B) := Fintype.ofFinite _
  letI : Fintype (A →ₗ[F] (W n ⧸ B)) := FunLike.fintype _
  exact Fintype.ofEquiv _ (t1TripleEquiv A B).symm

set_option maxHeartbeats 2000000 in
/-- The exact cardinality of all T1 index triples, with zero-dimensional
cases included. -/
theorem t1Triple_card {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype.card (T1IndexTriple A B) =
      2 ^ (Module.finrank F A * Module.finrank F (W n ⧸ B)) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (W n ⧸ B) := Fintype.ofFinite _
  letI : Fintype (A →ₗ[F] (W n ⧸ B)) := FunLike.fintype _
  let e : T1IndexTriple A B ≃ (A →ₗ[F] (W n ⧸ B)) :=
    t1TripleEquiv A B
  letI : Fintype (T1IndexTriple A B) := Fintype.ofEquiv _ e.symm
  calc
    Fintype.card (T1IndexTriple A B) = Nat.card (T1IndexTriple A B) :=
      (Nat.card_eq_fintype_card).symm
    _ = Nat.card (A →ₗ[F] (W n ⧸ B)) := Nat.card_congr e
    _ = Fintype.card (A →ₗ[F] (W n ⧸ B)) := Nat.card_eq_fintype_card
    _ = 2 ^ (Module.finrank F A * Module.finrank F (W n ⧸ B)) := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2)
        (V := A →ₗ[ZMod 2] (W n ⧸ B)),
        Module.finrank_linearMap, ZMod.card]

/-- Recover the actual ambient H from its quotient subspace K=H/B. -/
def t1AmbientH {n : Nat} {B : Submodule F (W n)}
    (K : Submodule F (W n ⧸ B)) : Submodule F (W n) :=
  K.comap (Submodule.mkQ B)

/-- The quotient map sends the recovered H onto the original quotient
subspace K. -/
theorem t1AmbientH_quotientRange {n : Nat}
    (B : Submodule F (W n)) (K : Submodule F (W n ⧸ B)) :
    LinearMap.range
      ((Submodule.mkQ B).comp (t1AmbientH K).subtype) = K := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact w.2
  · intro hx
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective B x
    have hwmem : w ∈ t1AmbientH K := by
      change Submodule.mkQ B w ∈ K
      rw [hw]
      exact hx
    exact ⟨⟨w, hwmem⟩, hw⟩

/-- Conversely, every ambient H containing B is recovered exactly from its
quotient image K=q_B(H). -/
theorem t1AmbientH_of_quotientRange {n : Nat}
    (B H : Submodule F (W n)) (hBH : B ≤ H) :
    t1AmbientH (LinearMap.range ((Submodule.mkQ B).comp H.subtype)) = H := by
  ext w
  change Submodule.mkQ B w ∈
      LinearMap.range ((Submodule.mkQ B).comp H.subtype) ↔ w ∈ H
  constructor
  · rintro ⟨h, hq⟩
    have hdiff : w - h ∈ B :=
      (Submodule.Quotient.eq B).mp hq.symm
    have hdecomp : w = (w - h) + h := by abel
    rw [hdecomp]
    exact H.add_mem (hBH hdiff) h.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

/-- The recovered ambient H contains B, including when K is zero. -/
theorem t1AmbientH_containsB {n : Nat}
    (B : Submodule F (W n)) (K : Submodule F (W n ⧸ B)) :
    B ≤ t1AmbientH K := by
  intro b hb
  change Submodule.mkQ B b ∈ K
  have hzero : Submodule.mkQ B b = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero B).mpr hb
  rw [hzero]
  exact K.zero_mem

/-- Quotienting the recovered H by its copy of B gives exactly K. -/
noncomputable def t1AmbientHQuotientEquiv {n : Nat}
    (B : Submodule F (W n)) (K : Submodule F (W n ⧸ B)) :
    (t1AmbientH K ⧸ B.comap (t1AmbientH K).subtype) ≃ₗ[F] K := by
  let H := t1AmbientH K
  let qH : H →ₗ[F] (W n ⧸ B) := (Submodule.mkQ B).comp H.subtype
  have hker : LinearMap.ker qH = B.comap H.subtype := by
    ext h
    change Submodule.mkQ B (H.subtype h) = 0 ↔ H.subtype h ∈ B
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero B)
  have hrange : LinearMap.range qH = K := by
    simpa [qH, H] using t1AmbientH_quotientRange B K
  let e0 := qH.quotKerEquivRange
  let eqQuot : (H ⧸ B.comap H.subtype) ≃ₗ[F] (H ⧸ LinearMap.ker qH) :=
    Submodule.quotEquivOfEq _ _ hker.symm
  exact eqQuot.trans (e0.trans (LinearEquiv.ofEq _ _ hrange))

/-- The H/B equivalence preserves the actual quotient representative. -/
theorem t1AmbientHQuotientEquiv_apply_mk {n : Nat}
    (B : Submodule F (W n)) (K : Submodule F (W n ⧸ B))
    (h : t1AmbientH K) :
    ((t1AmbientHQuotientEquiv B K)
      (Submodule.Quotient.mk h) : W n ⧸ B) = Submodule.mkQ B h.val := by
  simp [t1AmbientHQuotientEquiv]

/-- Embed the internal C <= A as the actual manuscript subspace of V. -/
def t1AmbientC {d : Nat} {A : Submodule F (V d)}
    (C : Submodule F A) : Submodule F (V d) := C.map A.subtype

/-- The embedded C remains a subspace of the actual A. -/
theorem t1AmbientC_le_A {d : Nat} {A : Submodule F (V d)}
    (C : Submodule F A) : t1AmbientC C ≤ A := by
  rintro v ⟨a, ha, rfl⟩
  exact a.property

/-- The canonical inclusion of the internal quotient A/C into the actual
ambient quotient V/(C.map A.subtype). -/
noncomputable def t1AQuotientToAmbient {d : Nat}
    {A : Submodule F (V d)} (C : Submodule F A) :
    (A ⧸ C) →ₗ[F] (V d ⧸ t1AmbientC C) :=
  C.liftQ
    ((Submodule.mkQ (t1AmbientC C)).comp A.subtype)
    (by
      intro a ha
      change Submodule.mkQ (t1AmbientC C) (A.subtype a) = 0
      apply (Submodule.Quotient.mk_eq_zero (t1AmbientC C)).mpr
      exact ⟨a, ha, rfl⟩)

/-- The quotient embedding preserves representatives from A. -/
theorem t1AQuotientToAmbient_apply_mk {d : Nat}
    {A : Submodule F (V d)} (C : Submodule F A) (a : A) :
    t1AQuotientToAmbient C (Submodule.Quotient.mk a) =
      Submodule.mkQ (t1AmbientC C) a.val := by
  simp [t1AQuotientToAmbient]

/-- The actual ambient quotient map embeds A/C injectively into V/(C.map A). -/
theorem t1AQuotientToAmbient_injective {d : Nat}
    {A : Submodule F (V d)} (C : Submodule F A) :
    Function.Injective (t1AQuotientToAmbient C) := by
  intro q₁ q₂ hq
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective C q₁
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective C q₂
  have hcoset :
      Submodule.mkQ (t1AmbientC C) a.val =
        Submodule.mkQ (t1AmbientC C) b.val := by
    calc
      Submodule.mkQ (t1AmbientC C) a.val =
          t1AQuotientToAmbient C (Submodule.Quotient.mk a) :=
        (t1AQuotientToAmbient_apply_mk C a).symm
      _ = t1AQuotientToAmbient C q₁ := by
        change t1AQuotientToAmbient C (C.mkQ a) = _
        rw [ha]
      _ = t1AQuotientToAmbient C q₂ := hq
      _ = t1AQuotientToAmbient C (Submodule.Quotient.mk b) := by
        change _ = t1AQuotientToAmbient C (C.mkQ b)
        rw [hb]
      _ = Submodule.mkQ (t1AmbientC C) b.val :=
        t1AQuotientToAmbient_apply_mk C b
  have hdiff : a.val - b.val ∈ t1AmbientC C :=
    (Submodule.Quotient.eq (t1AmbientC C)).mp hcoset
  rcases hdiff with ⟨c, hc, hval⟩
  have hab : a - b = c := by
    apply Subtype.ext
    exact hval.symm
  rw [← ha, ← hb]
  apply (Submodule.Quotient.eq C).mpr
  rw [hab]
  exact hc

/-- The pullback map Xtilde:H -> V/C on the actual H and ambient quotient.
It is built from H/B=K, the isomorphism Xbar:K ~= A/C, and the canonical
map A/C -> V/C. -/
noncomputable def t1PullbackMap {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    t1AmbientH t.K →ₗ[F] (V d ⧸ t1AmbientC t.C) :=
  (t1AQuotientToAmbient t.C).comp
    (t.Xbar.toLinearMap.comp
      ((t1AmbientHQuotientEquiv B t.K).toLinearMap.comp
      (Submodule.mkQ (B.comap (t1AmbientH t.K).subtype))))

/-- The actual pullback kernel is exactly the copy of B inside H. -/
theorem t1Pullback_ker {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    LinearMap.ker (t1PullbackMap t) = B.comap (t1AmbientH t.K).subtype := by
  let H := t1AmbientH t.K
  let eH := t1AmbientHQuotientEquiv B t.K
  ext h
  constructor
  · intro hh
    change t1AQuotientToAmbient t.C
      (t.Xbar (eH (Submodule.mkQ (B.comap H.subtype) h))) = 0 at hh
    have hX : t.Xbar (eH (Submodule.mkQ (B.comap H.subtype) h)) = 0 := by
      apply t1AQuotientToAmbient_injective
      simpa using hh
    have hH : eH (Submodule.mkQ (B.comap H.subtype) h) = 0 := by
      apply t.Xbar.injective
      simpa using hX
    have hq : Submodule.mkQ (B.comap H.subtype) h = 0 := by
      apply eH.injective
      simpa using hH
    exact (Submodule.Quotient.mk_eq_zero (B.comap H.subtype)).mp hq
  · intro hh
    have hq : Submodule.mkQ (B.comap H.subtype) h = 0 :=
      (Submodule.Quotient.mk_eq_zero (B.comap H.subtype)).mpr hh
    change t1AQuotientToAmbient t.C
      (t.Xbar (eH (Submodule.mkQ (B.comap H.subtype) h))) = 0
    rw [hq]
    simp

/-- The triple map records the same quotient point as the actual pullback:
theta_t(a)=q_B(h) exactly when Xtilde(h)=q_C(a). -/
theorem t1TripleToMap_pullback_iff {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (a : A) (h : t1AmbientH t.K) :
    t1TripleToMap t a = Submodule.mkQ B h.val ↔
      t1PullbackMap t h =
        Submodule.mkQ (t1AmbientC t.C) a.val := by
  let eH := t1AmbientHQuotientEquiv B t.K
  let y : t.K := eH (Submodule.Quotient.mk h)
  have hy : (y : W n ⧸ B) = Submodule.mkQ B h.val := by
    exact t1AmbientHQuotientEquiv_apply_mk B t.K h
  constructor
  · intro htheta
    have hK : t.Xbar.symm (t.C.mkQ a) = y := by
      apply Subtype.ext
      change t1TripleToMap t a = (y : W n ⧸ B)
      calc
        t1TripleToMap t a = Submodule.mkQ B h.val := htheta
        _ = (y : W n ⧸ B) := hy.symm
    have hXbar : t.Xbar y = t.C.mkQ a := by
      calc
        t.Xbar y = t.Xbar (t.Xbar.symm (t.C.mkQ a)) := by rw [hK.symm]
        _ = t.C.mkQ a := t.Xbar.apply_symm_apply _
    change t1AQuotientToAmbient t.C (t.Xbar y) =
      Submodule.mkQ (t1AmbientC t.C) a.val
    rw [hXbar]
    exact t1AQuotientToAmbient_apply_mk t.C a
  · intro hpull
    have hXbar : t.Xbar y = t.C.mkQ a := by
      apply t1AQuotientToAmbient_injective t.C
      calc
        t1AQuotientToAmbient t.C (t.Xbar y) =
            t1PullbackMap t h := rfl
        _ = Submodule.mkQ (t1AmbientC t.C) a.val := hpull
        _ = t1AQuotientToAmbient t.C (t.C.mkQ a) :=
          (t1AQuotientToAmbient_apply_mk t.C a).symm
    have hK : t.Xbar.symm (t.C.mkQ a) = y := by
      apply t.Xbar.injective
      simpa using hXbar.symm
    change t1TripleToMap t a = (y : W n ⧸ B)
    calc
      t1TripleToMap t a = (t.Xbar.symm (t.C.mkQ a) : W n ⧸ B) := rfl
      _ = (y : W n ⧸ B) := congrArg Subtype.val hK

/-- The original restricted frequency R=q_C o Y|H; this is not Xtilde. -/
def t1OriginalRestriction {n d : Nat}
    (Y : BinaryMatrix n d)
    (C : Submodule F (V d)) (H : Submodule F (W n)) :
    H →ₗ[F] (V d ⧸ C) :=
  (Submodule.mkQ C).comp (Y.transpose.toLin'.comp H.subtype)

/-- Rank-poset relation R = Xtilde + a complementary displacement. -/
def t1RankPrecedes {U Z : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup Z] [Module F Z]
    (X R : U →ₗ[F] Z) : Prop :=
  Module.finrank F (LinearMap.range R) =
    Module.finrank F (LinearMap.range X) +
      Module.finrank F (LinearMap.range (R - X))

/-- In finite-dimensional carriers, rank additivity forces the exact image
sum and zero intersection for the two actual linear-map images. -/
theorem t1RankPrecedes_range_decomposition {U Z : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup Z] [Module F Z] [FiniteDimensional F Z]
    (X R : U →ₗ[F] Z) (hXR : t1RankPrecedes X R) :
    (LinearMap.range R =
        LinearMap.range X ⊔ LinearMap.range (R - X)) ∧
      LinearMap.range X ⊓ LinearMap.range (R - X) = ⊥ := by
  let P : Submodule F Z := LinearMap.range X
  let Q : Submodule F Z := LinearMap.range (R - X)
  have hsum : R = X + (R - X) := by
    ext u
    simp
  have hdim : Module.finrank F (LinearMap.range (X + (R - X))) =
      Module.finrank F (LinearMap.range X) +
        Module.finrank F (LinearMap.range (R - X)) := by
    rw [← hsum]
    change Module.finrank F (LinearMap.range R) =
      Module.finrank F (LinearMap.range X) +
        Module.finrank F (LinearMap.range (R - X))
    exact hXR
  have hle : LinearMap.range (X + (R - X)) ≤
      P ⊔ Q := by
    intro z hz
    rcases LinearMap.mem_range.mp hz with ⟨u, rfl⟩
    change X u + (R - X) u ∈
      P ⊔ Q
    exact add_mem (Submodule.mem_sup_left ⟨u, rfl⟩)
      (Submodule.mem_sup_right ⟨u, rfl⟩)
  have hsupdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hsupdim' : Module.finrank F ↥(P ⊔ Q) +
      Module.finrank F ↥(P ⊓ Q) =
      Module.finrank F ↥P + Module.finrank F ↥Q := by
    simpa only [P, Q] using hsupdim
  have hdim' : Module.finrank F (LinearMap.range (X + (R - X))) =
      Module.finrank F ↥P + Module.finrank F ↥Q := by
    simpa only [P, Q] using hdim
  have hsup_le : Module.finrank F ↥(P ⊔ Q) ≤
      Module.finrank F ↥P + Module.finrank F ↥Q := by
    have hnonneg := Nat.zero_le (Module.finrank F ↥(P ⊓ Q))
    omega
  have hrange_le : Module.finrank F (LinearMap.range (X + (R - X))) ≤
      Module.finrank F ↥(P ⊔ Q) :=
    Submodule.finrank_mono hle
  have hsup_eq : Module.finrank F ↥(P ⊔ Q) =
      Module.finrank F (LinearMap.range (X + (R - X))) := by
    change Module.finrank F ↥(P ⊔ Q) ≤
      Module.finrank F ↥P + Module.finrank F ↥Q at hsup_le
    change Module.finrank F (LinearMap.range (X + (R - X))) ≤
      Module.finrank F ↥(P ⊔ Q) at hrange_le
    change Module.finrank F (LinearMap.range (X + (R - X))) =
      Module.finrank F ↥P + Module.finrank F ↥Q at hdim'
    omega
  have hsum_eq : LinearMap.range (X + (R - X)) =
      P ⊔ Q :=
    Submodule.eq_of_le_of_finrank_eq hle hsup_eq.symm
  have hsum_dim := congrArg
    (fun S : Submodule F Z => Module.finrank F S) hsum_eq
  have hinf0 : Module.finrank F ↥(P ⊓ Q) = 0 := by
    rw [← hsum_dim] at hsupdim'
    omega
  have hinf : P ⊓ Q = ⊥ :=
    Submodule.finrank_eq_zero.mp hinf0
  rw [← hsum] at hsum_eq
  exact ⟨hsum_eq, hinf⟩

/-- Under rank additivity, R and X agree at every vector whose R value lies
in range X. -/
theorem t1RankPrecedes_agreement_on_preimage {U Z : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup Z] [Module F Z] [FiniteDimensional F Z]
    (X R : U →ₗ[F] Z) (hXR : t1RankPrecedes X R)
    (u : U) (hu : R u ∈ LinearMap.range X) : X u = R u := by
  obtain ⟨_, hinter⟩ := t1RankPrecedes_range_decomposition X R hXR
  have hDx : (R - X) u ∈ LinearMap.range X := by
    have hRu : R u ∈ LinearMap.range X := hu
    have hXu : X u ∈ LinearMap.range X := ⟨u, rfl⟩
    change R u - X u ∈ LinearMap.range X
    exact Submodule.sub_mem _ hRu hXu
  have hDinter : (R - X) u ∈
      LinearMap.range X ⊓ LinearMap.range (R - X) :=
    ⟨hDx, ⟨u, rfl⟩⟩
  have hDzero : (R - X) u = 0 := by
    have : (R - X) u ∈ (⊥ : Submodule F Z) := by
      rw [← hinter]
      exact hDinter
    simpa using this
  have hsum : R u = X u + (R - X) u := by
    change R u = X u + (R - X) u
    simp
  rw [hDzero] at hsum
  simpa using hsum.symm

/-- A frequency activates a triple exactly when it passes the hybrid selector
and Xtilde is a rank-additive predecessor of the actual R map. -/
def t1ActiveTriple {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (t : T1IndexTriple A B) : Prop :=
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1.Selected
      C H Y.transpose.toLin' ∧
    t1RankPrecedes (t1PullbackMap t) (t1OriginalRestriction Y C H)

/-- For an ordinarily selected frequency, descend the inverse of Y on A
through W/ker(Y), then through W/B. The kernel inclusion ker(Y)<=B makes the
second quotient map well defined. -/
noncomputable def t1SelectedTheta {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d)
    (hY : DR6OrdinarySelected A B Y) : A →ₗ[F] (W n ⧸ B) := by
  let L := Y.transpose.toLin'
  let qbar := (LinearMap.ker L).mapQ B LinearMap.id hY.2
  exact qbar.comp
    ((L.quotKerEquivRange).symm.toLinearMap.comp
      (Submodule.inclusion hY.1))

/-- The descended map theta records the actual B-coset of every preimage in
Y^(-1)(A); this representative formula is the bridge for C and H recovery. -/
theorem t1SelectedTheta_on_preimage {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d)
    (hY : DR6OrdinarySelected A B Y)
    (w : W n) (hw : Y.transpose.toLin' w ∈ A) :
    t1SelectedTheta A B Y hY ⟨Y.transpose.toLin' w, hw⟩ =
      Submodule.mkQ B w := by
  let L := Y.transpose.toLin'
  let e := L.quotKerEquivRange
  let qbar := (LinearMap.ker L).mapQ B LinearMap.id hY.2
  let y : LinearMap.range L := ⟨L w, ⟨w, rfl⟩⟩
  have hinc : Submodule.inclusion hY.1 ⟨L w, hw⟩ = y := by
    apply Subtype.ext
    rfl
  have hquot : e.symm y = Submodule.Quotient.mk w := by
    have hy : e (Submodule.Quotient.mk w) = y := by
      apply Subtype.ext
      rfl
    calc
      e.symm y = e.symm (e (Submodule.Quotient.mk w)) := by rw [hy]
      _ = Submodule.Quotient.mk w := e.symm_apply_apply _
  change qbar ((L.quotKerEquivRange).symm
      (Submodule.inclusion hY.1 ⟨L w, hw⟩)) = Submodule.mkQ B w
  rw [hinc, hquot]
  change (qbar.comp (Submodule.mkQ (LinearMap.ker L))) w =
    (Submodule.mkQ B) w
  have hcomp : qbar.comp (Submodule.mkQ (LinearMap.ker L)) =
      Submodule.mkQ B := by
    simpa [qbar] using (Submodule.mapQ_mkQ)
  exact DFunLike.congr_fun hcomp w

/-- The selected ordinary frequency's index triple is obtained from its
descended theta by the proved inverse map-to-triple direction. -/
noncomputable def t1SelectedTriple {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    T1IndexTriple A B :=
  t1MapToTriple (t1SelectedTheta A B Y hY)

/-- Encoding the selected triple recovers its ordinary theta exactly. -/
theorem t1SelectedTriple_toMap {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    t1TripleToMap (t1SelectedTriple A B Y hY) =
      t1SelectedTheta A B Y hY := by
  exact t1TripleToMap_mapToTriple A B (t1SelectedTheta A B Y hY)

/-- The kernel of the selected theta is precisely the selected image part
Y(B) intersected with A, represented internally as a subspace of A. -/
theorem t1SelectedTheta_ker {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    LinearMap.ker (t1SelectedTheta A B Y hY) =
      (LinearMap.range (Y.transpose.toLin'.comp B.subtype)).comap A.subtype := by
  ext a
  change t1SelectedTheta A B Y hY a = 0 ↔
    (a : V d) ∈ LinearMap.range (Y.transpose.toLin'.comp B.subtype)
  constructor
  · intro hzero
    obtain ⟨w, hw⟩ := hY.1 a.property
    have hAw : Y.transpose.toLin' w ∈ A := by
      rw [hw]
      exact a.property
    have heval := t1SelectedTheta_on_preimage A B Y hY w hAw
    have haeq : (⟨Y.transpose.toLin' w, hAw⟩ : A) = a := by
      apply Subtype.ext
      exact hw
    have hwB : w ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      calc
        Submodule.mkQ B w = t1SelectedTheta A B Y hY ⟨Y.transpose.toLin' w, hAw⟩ :=
          heval.symm
        _ = t1SelectedTheta A B Y hY a := by rw [haeq]
        _ = 0 := hzero
    refine ⟨⟨w, hwB⟩, by simpa using hw⟩
  · rintro ⟨b, hb⟩
    have hb' : Y.transpose.toLin' (B.subtype b) = (a : V d) := by
      simpa [LinearMap.comp_apply] using hb
    have haeq : (⟨Y.transpose.toLin' (B.subtype b), by
        rw [hb']
        exact a.property⟩ : A) = a := by
      apply Subtype.ext
      exact hb'
    have heval := t1SelectedTheta_on_preimage A B Y hY (B.subtype b) (by
      change Y.transpose.toLin' (B.subtype b) ∈ A
      rw [hb']
      exact a.property)
    rw [← haeq, heval]
    apply (Submodule.Quotient.mk_eq_zero B).mpr
    exact b.property

/-- The actual preimage space Y^{-1}(A), written as the kernel of the
quotient-valued map q_A o Y. -/
def t1SelectedPreimage {n d : Nat}
    (A : Submodule F (V d)) (Y : BinaryMatrix n d) : Submodule F (W n) :=
  LinearMap.ker ((Submodule.mkQ A).comp Y.transpose.toLin')

/-- The range of theta is exactly q_B(Y^{-1}(A)), so the quotient subspace
K is the actual H/B associated to H=B+Y^{-1}(A). -/
theorem t1SelectedTheta_range {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    LinearMap.range (t1SelectedTheta A B Y hY) =
      LinearMap.range
        ((Submodule.mkQ B).comp (t1SelectedPreimage A Y).subtype) := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨w, hw⟩ := hY.1 a.property
    have hA : Y.transpose.toLin' w ∈ A := by
      rw [hw]
      exact a.property
    have hS : w ∈ t1SelectedPreimage A Y := by
      change Submodule.mkQ A (Y.transpose.toLin' w) = 0
      exact (Submodule.Quotient.mk_eq_zero A).mpr hA
    have ha : (⟨Y.transpose.toLin' w, hA⟩ : A) = a := by
      apply Subtype.ext
      exact hw
    have heval := t1SelectedTheta_on_preimage A B Y hY w hA
    refine ⟨⟨w, hS⟩, by rw [← ha, heval]; rfl⟩
  · rintro ⟨w, rfl⟩
    have hA : Y.transpose.toLin' w.val ∈ A := by
      apply (Submodule.Quotient.mk_eq_zero A).mp
      exact w.property
    have heval := t1SelectedTheta_on_preimage A B Y hY w.val hA
    exact ⟨⟨Y.transpose.toLin' w.val, hA⟩,
      by simpa [LinearMap.comp_apply] using heval⟩

/-- Recover the actual ambient selected space H as B+Y^{-1}(A), not merely
as an abstract quotient carrier. -/
theorem t1SelectedTriple_ambientH {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    t1AmbientH (t1SelectedTriple A B Y hY).K =
      B ⊔ t1SelectedPreimage A Y := by
  ext w
  change Submodule.mkQ B w ∈
      LinearMap.range (t1SelectedTheta A B Y hY) ↔
    w ∈ B ⊔ t1SelectedPreimage A Y
  rw [t1SelectedTheta_range]
  change Submodule.mkQ B w ∈
      LinearMap.range
        ((Submodule.mkQ B).comp (t1SelectedPreimage A Y).subtype) ↔
    w ∈ B ⊔ t1SelectedPreimage A Y
  constructor
  · rintro ⟨s, hs⟩
    change Submodule.mkQ B s.val = Submodule.mkQ B w at hs
    have hdiff : w - s.val ∈ B :=
      (Submodule.Quotient.eq B).mp hs.symm
    apply (Submodule.mem_sup).2
    exact ⟨w - s.val, hdiff, s.val, s.property, by abel⟩
  · intro hw
    rcases (Submodule.mem_sup).1 hw with ⟨b, hb, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, by
      change Submodule.mkQ B s = Submodule.mkQ B (b + s)
      calc
        Submodule.mkQ B s = 0 + Submodule.mkQ B s := by simp
        _ = Submodule.mkQ B b + Submodule.mkQ B s := by
          have hb0 : Submodule.mkQ B b = 0 :=
            (Submodule.Quotient.mk_eq_zero B).2 hb
          rw [hb0]
        _ = Submodule.mkQ B (b + s) := (map_add _ _ _).symm⟩

/-- The actual ambient C of the selected triple is Y(B) intersect A. -/
theorem t1SelectedTriple_ambientC {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    t1AmbientC (t1SelectedTriple A B Y hY).C =
      LinearMap.range (Y.transpose.toLin'.comp B.subtype) ⊓ A := by
  ext v
  change v ∈ (LinearMap.ker (t1SelectedTheta A B Y hY)).map A.subtype ↔
    v ∈ LinearMap.range (Y.transpose.toLin'.comp B.subtype) ∧ v ∈ A
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := ha
    rw [t1SelectedTheta_ker A B Y hY] at ha'
    change (a : V d) ∈ LinearMap.range (Y.transpose.toLin'.comp B.subtype) at ha'
    exact ⟨ha', a.property⟩
  · rintro ⟨hvB, hvA⟩
    let a : A := ⟨v, hvA⟩
    have ha : a ∈ LinearMap.ker (t1SelectedTheta A B Y hY) := by
      rw [t1SelectedTheta_ker A B Y hY]
      exact hvB
    exact ⟨a, ha, rfl⟩

/-- The actual Xtilde pullback sends each selected preimage representative s
to Yᵀs modulo the actual ambient C. This is the representative identity
needed before forming the image of R-Xtilde. -/
theorem t1SelectedPullback_on_preimage {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (s : W n) (hs : s ∈ t1SelectedPreimage A Y) :
    t1PullbackMap (t1SelectedTriple A B Y hY)
      ⟨s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2 ⟨0, B.zero_mem, s, hs, by simp⟩⟩ =
    Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (Y.transpose.toLin' s) := by
  let t := t1SelectedTriple A B Y hY
  let theta := t1SelectedTheta A B Y hY
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  have hsH : s ∈ H := by
    change s ∈ t1AmbientH (t1SelectedTriple A B Y hY).K
    rw [t1SelectedTriple_ambientH A B Y hY]
    exact (Submodule.mem_sup).2 ⟨0, B.zero_mem, s, hs, by simp⟩
  have hA : Y.transpose.toLin' s ∈ A := by
    apply (Submodule.Quotient.mk_eq_zero A).mp
    exact hs
  let a : A := ⟨Y.transpose.toLin' s, hA⟩
  let qh : H := ⟨s, hsH⟩
  have htheta : theta a = Submodule.mkQ B s :=
    t1SelectedTheta_on_preimage A B Y hY s hA
  let y : t.K := ⟨Submodule.mkQ B s, by
    change Submodule.mkQ B s ∈ LinearMap.range theta
    exact ⟨a, htheta⟩⟩
  have hy : y = theta.quotKerEquivRange (Submodule.Quotient.mk a) := by
    apply Subtype.ext
    change Submodule.mkQ B s =
      (theta.quotKerEquivRange (Submodule.Quotient.mk a) : W n ⧸ B)
    rw [LinearMap.quotKerEquivRange_apply_mk]
    exact htheta.symm
  have hxbar : t.Xbar y =
      Submodule.Quotient.mk a := by
    change (theta.quotKerEquivRange).symm y = _
    rw [hy]
    exact (theta.quotKerEquivRange).symm_apply_apply _
  have hHquot : t1AmbientHQuotientEquiv B t.K
      (Submodule.Quotient.mk qh) = y := by
    apply Subtype.ext
    simpa [y, qh] using t1AmbientHQuotientEquiv_apply_mk B t.K qh
  change t1AQuotientToAmbient t.C
      (t.Xbar (t1AmbientHQuotientEquiv B t.K
        (Submodule.Quotient.mk qh))) = _
  rw [hHquot, hxbar]
  exact t1AQuotientToAmbient_apply_mk t.C a

/-- The selected pullback vanishes on the actual B-subspace of H. -/
theorem t1SelectedPullback_zero_on_B {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (b : B) :
    t1PullbackMap (t1SelectedTriple A B Y hY)
      ⟨B.subtype b, t1AmbientH_containsB B
        (t1SelectedTriple A B Y hY).K b.property⟩ = 0 := by
  let t := t1SelectedTriple A B Y hY
  let H := t1AmbientH t.K
  let hb : H := ⟨B.subtype b,
    t1AmbientH_containsB B t.K b.property⟩
  have hz : Submodule.mkQ (B.comap H.subtype) hb = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (B.comap H.subtype)).mpr
    exact b.property
  change (t1AQuotientToAmbient t.C).comp
      (t.Xbar.toLinearMap.comp
        ((t1AmbientHQuotientEquiv B t.K).toLinearMap.comp
          (Submodule.mkQ (B.comap H.subtype)))) hb = 0
  simp only [LinearMap.comp_apply]
  rw [hz]
  simp

/-- For h=b+s with b∈B and s∈Y^{-1}(A), the actual pullback is the
representative formula Xtilde(b+s)=Yᵀs+C. -/
theorem t1SelectedPullback_on_sum {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (b : B) (s : W n) (hs : s ∈ t1SelectedPreimage A Y) :
    t1PullbackMap (t1SelectedTriple A B Y hY)
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ =
    Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (Y.transpose.toLin' s) := by
  let t := t1SelectedTriple A B Y hY
  let H := t1AmbientH t.K
  let hb : H := ⟨B.subtype b, t1AmbientH_containsB B t.K b.property⟩
  let hsH : H := ⟨s, by
    change s ∈ t1AmbientH (t1SelectedTriple A B Y hY).K
    rw [t1SelectedTriple_ambientH A B Y hY]
    exact (Submodule.mem_sup).2 ⟨0, B.zero_mem, s, hs, by simp⟩⟩
  let hsum : H := ⟨B.subtype b + s, by
    change B.subtype b + s ∈ t1AmbientH (t1SelectedTriple A B Y hY).K
    rw [t1SelectedTriple_ambientH A B Y hY]
    exact (Submodule.mem_sup).2
      ⟨B.subtype b, b.property, s, hs, rfl⟩⟩
  have hdecomp : hsum = hb + hsH := by
    apply Subtype.ext
    change B.subtype b + s = B.subtype b + s
    rfl
  have htarget :
      (⟨B.subtype b + s, by
        change B.subtype b + s ∈ t1AmbientH (t1SelectedTriple A B Y hY).K
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ : H) = hsum := by
    apply Subtype.ext
    rfl
  change t1PullbackMap t
      (⟨B.subtype b + s, by
        change B.subtype b + s ∈ t1AmbientH (t1SelectedTriple A B Y hY).K
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ : H) = _
  rw [htarget, hdecomp, map_add]
  rw [t1SelectedPullback_zero_on_B A B Y hY b]
  rw [t1SelectedPullback_on_preimage A B Y hY s hs]
  simp

/-- The actual restricted map R on b+s is Yᵀb+Yᵀs modulo C. -/
theorem t1SelectedRestriction_on_sum {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (C : Submodule F (V d)) (b : B) (s : W n)
    (hs : s ∈ t1SelectedPreimage A Y) :
    t1OriginalRestriction Y C
      (t1AmbientH (t1SelectedTriple A B Y hY).K)
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ =
    Submodule.mkQ C (Y.transpose.toLin' (B.subtype b)) +
      Submodule.mkQ C (Y.transpose.toLin' s) := by
  change Submodule.mkQ C
      (Y.transpose.toLin' (B.subtype b + s)) = _
  rw [map_add, map_add]

/-- On a selected decomposition h=b+s, the original R map is the
pullback Xtilde plus the independently varying Y(B)/C displacement. -/
theorem t1SelectedRestriction_eq_pullback_add_B {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (b : B) (s : W n) (hs : s ∈ t1SelectedPreimage A Y) :
    t1OriginalRestriction Y
      (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (t1AmbientH (t1SelectedTriple A B Y hY).K)
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ =
    t1PullbackMap (t1SelectedTriple A B Y hY)
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ +
    Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (Y.transpose.toLin' (B.subtype b)) := by
  rw [t1SelectedRestriction_on_sum A B Y hY
    (t1AmbientC (t1SelectedTriple A B Y hY).C) b s hs]
  rw [t1SelectedPullback_on_sum A B Y hY b s hs]
  abel

/-- The pointwise rank displacement R-X on b+s is exactly q_C(Yᵀb). -/
theorem t1SelectedDisplacement_on_sum {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (b : B) (s : W n) (hs : s ∈ t1SelectedPreimage A Y) :
    (t1OriginalRestriction Y
        (t1AmbientC (t1SelectedTriple A B Y hY).C)
        (t1AmbientH (t1SelectedTriple A B Y hY).K) -
      t1PullbackMap (t1SelectedTriple A B Y hY))
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ =
    Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (Y.transpose.toLin' (B.subtype b)) := by
  change t1OriginalRestriction Y
      (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (t1AmbientH (t1SelectedTriple A B Y hY).K)
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ -
    t1PullbackMap (t1SelectedTriple A B Y hY)
      ⟨B.subtype b + s, by
        rw [t1SelectedTriple_ambientH A B Y hY]
        exact (Submodule.mem_sup).2
          ⟨B.subtype b, b.property, s, hs, rfl⟩⟩ = _
  rw [t1SelectedRestriction_eq_pullback_add_B A B Y hY b s hs]
  abel

/-- The entire displacement image is exactly the actual quotient image
Yᵀ(B)/C.  Both inclusions use actual elements: every H vector decomposes as
b+s, and each Yᵀb value is attained at the H vector b. -/
theorem t1SelectedDisplacement_range {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    LinearMap.range
        (t1OriginalRestriction Y
            (t1AmbientC (t1SelectedTriple A B Y hY).C)
            (t1AmbientH (t1SelectedTriple A B Y hY).K) -
          t1PullbackMap (t1SelectedTriple A B Y hY)) =
      LinearMap.range
        ((Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)).comp
          (Y.transpose.toLin'.comp B.subtype)) := by
  let t := t1SelectedTriple A B Y hY
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let D := t1OriginalRestriction Y C H - t1PullbackMap t
  let E := (Submodule.mkQ C).comp (Y.transpose.toLin'.comp B.subtype)
  change LinearMap.range D = LinearMap.range E
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨h, rfl⟩
    have hm : (h : W n) ∈ B ⊔ t1SelectedPreimage A Y := by
      rw [← t1SelectedTriple_ambientH A B Y hY]
      exact h.property
    obtain ⟨b, hb, s, hs, hadd⟩ := (Submodule.mem_sup).mp hm
    let b' : B := ⟨b, hb⟩
    let hsum : H := ⟨B.subtype b' + s, by
      change B.subtype b' + s ∈ t1AmbientH t.K
      rw [t1SelectedTriple_ambientH A B Y hY]
      exact (Submodule.mem_sup).2
        ⟨B.subtype b', b'.property, s, hs, rfl⟩⟩
    have hheq : h = hsum := by
      apply Subtype.ext
      change (h : W n) = B.subtype b' + s
      exact hadd.symm
    have hpoint :
        (⟨B.subtype b' + s, by
          change B.subtype b' + s ∈ t1AmbientH t.K
          rw [t1SelectedTriple_ambientH A B Y hY]
          exact (Submodule.mem_sup).2
            ⟨B.subtype b', b'.property, s, hs, rfl⟩⟩ : H) = hsum := by
      apply Subtype.ext
      rfl
    have hvalue := t1SelectedDisplacement_on_sum A B Y hY b' s hs
    rw [hpoint] at hvalue
    refine ⟨b', ?_⟩
    change E b' = D h
    rw [hheq]
    change (Submodule.mkQ C) (Y.transpose.toLin' (B.subtype b')) =
      (t1OriginalRestriction Y C H - t1PullbackMap t) hsum
    simpa [D, E, t, H, C] using hvalue.symm
  · rintro ⟨b, rfl⟩
    let hb : H := ⟨B.subtype b,
      t1AmbientH_containsB B t.K b.property⟩
    have hs0 : (0 : W n) ∈ t1SelectedPreimage A Y := by
      simp [t1SelectedPreimage]
    have hvalue := t1SelectedDisplacement_on_sum A B Y hY b 0 hs0
    have hpoint :
        (⟨B.subtype b + 0, by
          change B.subtype b + 0 ∈ t1AmbientH t.K
          rw [t1SelectedTriple_ambientH A B Y hY]
          exact (Submodule.mem_sup).2
            ⟨B.subtype b, b.property, 0, hs0, by simp⟩⟩ : H) = hb := by
      apply Subtype.ext
      change B.subtype b + 0 = B.subtype b
      simp
    rw [hpoint] at hvalue
    refine ⟨hb, ?_⟩
    change D hb = E b
    simpa [D, E, t, H, C] using hvalue

/-- The actual pullback Xtilde has exactly the embedded A/C as its range;
the H/B quotient map and Xbar are both surjective. -/
theorem t1Pullback_range {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    LinearMap.range (t1PullbackMap t) =
      LinearMap.range (t1AQuotientToAmbient t.C) := by
  let H := t1AmbientH t.K
  let eH := t1AmbientHQuotientEquiv B t.K
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨t.Xbar (eH (Submodule.mkQ (B.comap H.subtype) h)), ?_⟩
    rfl
  · rintro ⟨a, rfl⟩
    let q := eH.symm (t.Xbar.symm a)
    obtain ⟨h, hh⟩ := Submodule.mkQ_surjective (B.comap H.subtype) q
    have hq : eH (Submodule.mkQ (B.comap H.subtype) h) =
        t.Xbar.symm a := by
      rw [hh]
      exact eH.apply_symm_apply _
    refine ⟨h, ?_⟩
    change t1AQuotientToAmbient t.C
      (t.Xbar (eH (Submodule.mkQ (B.comap H.subtype) h))) =
      t1AQuotientToAmbient t.C a
    rw [hq, t.Xbar.apply_symm_apply]

theorem t1SelectedPullback_range {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    LinearMap.range (t1PullbackMap (t1SelectedTriple A B Y hY)) =
    LinearMap.range
        (t1AQuotientToAmbient (t1SelectedTriple A B Y hY).C) := by
  exact t1Pullback_range (t1SelectedTriple A B Y hY)

/-- The actual quotient images A/C and Yᵀ(B)/C intersect only at zero.
If their representatives have the same C-coset, then their difference lies
in C=Yᵀ(B)∩A, forcing the Yᵀ(B) representative itself into C. -/
theorem t1SelectedPullback_disjoint_displacement {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    LinearMap.range (t1PullbackMap (t1SelectedTriple A B Y hY)) ⊓
        LinearMap.range
          (t1OriginalRestriction Y
              (t1AmbientC (t1SelectedTriple A B Y hY).C)
              (t1AmbientH (t1SelectedTriple A B Y hY).K) -
            t1PullbackMap (t1SelectedTriple A B Y hY)) = ⊥ := by
  rw [t1SelectedPullback_range A B Y hY,
    t1SelectedDisplacement_range A B Y hY]
  ext z
  constructor
  · rintro ⟨⟨q, hqz⟩, ⟨b, hbz⟩⟩
    change z = 0
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
      (t1SelectedTriple A B Y hY).C q
    have hcoset :
        Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C) a.val =
          Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
            (Y.transpose.toLin' (B.subtype b)) := by
      calc
        Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C) a.val =
            t1AQuotientToAmbient (t1SelectedTriple A B Y hY).C
              (Submodule.Quotient.mk a) :=
          (t1AQuotientToAmbient_apply_mk _ _).symm
        _ = t1AQuotientToAmbient (t1SelectedTriple A B Y hY).C q := by
          change t1AQuotientToAmbient (t1SelectedTriple A B Y hY).C
            ((t1SelectedTriple A B Y hY).C.mkQ a) = _
          rw [ha]
        _ = z := hqz
        _ = ((Submodule.mkQ
              (t1AmbientC (t1SelectedTriple A B Y hY).C)).comp
              (Y.transpose.toLin'.comp B.subtype)) b := hbz.symm
        _ = Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
              (Y.transpose.toLin' (B.subtype b)) := rfl
    have hdiff : a.val - Y.transpose.toLin' (B.subtype b) ∈
        t1AmbientC (t1SelectedTriple A B Y hY).C :=
      (Submodule.Quotient.eq
        (t1AmbientC (t1SelectedTriple A B Y hY).C)).mp hcoset
    have hyA : Y.transpose.toLin' (B.subtype b) ∈ A := by
      have haA : a.val ∈ A := a.property
      have hdiffA : a.val - Y.transpose.toLin' (B.subtype b) ∈ A :=
        t1AmbientC_le_A (t1SelectedTriple A B Y hY).C hdiff
      have hsub := A.sub_mem haA hdiffA
      simpa using hsub
    have hyC : Y.transpose.toLin' (B.subtype b) ∈
        t1AmbientC (t1SelectedTriple A B Y hY).C := by
      rw [t1SelectedTriple_ambientC A B Y hY]
      exact ⟨⟨b, rfl⟩, hyA⟩
    have hzero :=
      (Submodule.Quotient.mk_eq_zero
        (t1AmbientC (t1SelectedTriple A B Y hY).C)).mpr hyC
    calc
      z = Submodule.mkQ (t1AmbientC (t1SelectedTriple A B Y hY).C)
          (Y.transpose.toLin' (B.subtype b)) := hbz.symm
      _ = 0 := hzero
  · intro hz
    rw [hz]
    exact Submodule.zero_mem _

/-- The actual R image is the sum of the independently realized A/C and
Yᵀ(B)/C images.  The forward containment is R=X+(R-X); the reverse uses
ordinary A<=range(Y) to realize every X value through an actual s∈Y⁻¹(A),
and B<=H to realize every displacement at an actual b∈B. -/
theorem t1SelectedRestriction_range_eq_sup {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    LinearMap.range
        (t1OriginalRestriction Y
            (t1AmbientC (t1SelectedTriple A B Y hY).C)
            (t1AmbientH (t1SelectedTriple A B Y hY).K)) =
      LinearMap.range (t1PullbackMap (t1SelectedTriple A B Y hY)) ⊔
        LinearMap.range
          (t1OriginalRestriction Y
              (t1AmbientC (t1SelectedTriple A B Y hY).C)
              (t1AmbientH (t1SelectedTriple A B Y hY).K) -
            t1PullbackMap (t1SelectedTriple A B Y hY)) := by
  let t := t1SelectedTriple A B Y hY
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let R := t1OriginalRestriction Y C H
  let X := t1PullbackMap t
  let D := R - X
  have hX : LinearMap.range X ≤ LinearMap.range R := by
    intro z hz
    rw [t1SelectedPullback_range A B Y hY] at hz
    obtain ⟨q, hq⟩ := hz
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective t.C q
    obtain ⟨s, hsY⟩ := hY.1 a.property
    have hAs : Y.transpose.toLin' s ∈ A := by
      rw [hsY]
      exact a.property
    have hsS : s ∈ t1SelectedPreimage A Y := by
      change Submodule.mkQ A (Y.transpose.toLin' s) = 0
      exact (Submodule.Quotient.mk_eq_zero A).mpr hAs
    let hS : H := ⟨s, by
      change s ∈ t1AmbientH (t1SelectedTriple A B Y hY).K
      rw [t1SelectedTriple_ambientH A B Y hY]
      exact (Submodule.mem_sup).2 ⟨0, B.zero_mem, s, hsS, by simp⟩⟩
    refine ⟨hS, ?_⟩
    change R hS = z
    calc
      R hS = Submodule.mkQ C (Y.transpose.toLin' s) := rfl
      _ = t1AQuotientToAmbient t.C (t.C.mkQ a) := by
        rw [hsY]
        exact (t1AQuotientToAmbient_apply_mk t.C a).symm
      _ = t1AQuotientToAmbient t.C q := by
        change t1AQuotientToAmbient t.C (t.C.mkQ a) = _
        rw [ha]
      _ = z := hq
  have hD : LinearMap.range D ≤ LinearMap.range R := by
    intro z hz
    rw [t1SelectedDisplacement_range A B Y hY] at hz
    obtain ⟨b, hbz⟩ := hz
    let hb : H := ⟨B.subtype b,
      t1AmbientH_containsB B t.K b.property⟩
    refine ⟨hb, ?_⟩
    change R hb = z
    calc
      R hb = ((Submodule.mkQ C).comp
        (Y.transpose.toLin'.comp B.subtype)) b := rfl
      _ = z := hbz
  apply le_antisymm
  · rintro z ⟨h, rfl⟩
    apply (Submodule.mem_sup).2
    refine ⟨X h, ?_, D h, ?_, ?_⟩
    · exact ⟨h, rfl⟩
    · exact ⟨h, rfl⟩
    · change X h + (R - X) h = R h
      simp
  · exact sup_le hX hD

/-- The selected decomposition has rank additivity: its two actual images are
the direct summands A/C and Yᵀ(B)/C. -/
theorem t1SelectedTriple_rankPrecedes {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    t1RankPrecedes
      (t1PullbackMap (t1SelectedTriple A B Y hY))
      (t1OriginalRestriction Y
        (t1AmbientC (t1SelectedTriple A B Y hY).C)
        (t1AmbientH (t1SelectedTriple A B Y hY).K)) := by
  change Module.finrank F
      (LinearMap.range (t1OriginalRestriction Y
        (t1AmbientC (t1SelectedTriple A B Y hY).C)
        (t1AmbientH (t1SelectedTriple A B Y hY).K))) =
    Module.finrank F (LinearMap.range
      (t1PullbackMap (t1SelectedTriple A B Y hY))) +
    Module.finrank F (LinearMap.range
      (t1OriginalRestriction Y
        (t1AmbientC (t1SelectedTriple A B Y hY).C)
        (t1AmbientH (t1SelectedTriple A B Y hY).K) -
      t1PullbackMap (t1SelectedTriple A B Y hY)))
  rw [t1SelectedRestriction_range_eq_sup A B Y hY]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (K := F) (V := V d ⧸ t1AmbientC (t1SelectedTriple A B Y hY).C)
    (LinearMap.range (t1PullbackMap (t1SelectedTriple A B Y hY)))
    (LinearMap.range
      (t1OriginalRestriction Y
        (t1AmbientC (t1SelectedTriple A B Y hY).C)
        (t1AmbientH (t1SelectedTriple A B Y hY).K) -
      t1PullbackMap (t1SelectedTriple A B Y hY)))
  rw [t1SelectedPullback_disjoint_displacement A B Y hY] at hdim
  simpa using hdim

/-- Every ordinary-selected frequency yields the manuscript hybrid selector
on its actual C and H; this uses A<=range(Y) and H=B+Y^{-1}(A). -/
theorem t1SelectedTriple_hybridSelected {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1.Selected
      (t1AmbientC (t1SelectedTriple A B Y hY).C)
      (t1AmbientH (t1SelectedTriple A B Y hY).K)
      Y.transpose.toLin' := by
  change t1AmbientC (t1SelectedTriple A B Y hY).C ≤
        LinearMap.range Y.transpose.toLin' ∧
      (∀ w, Y.transpose.toLin' w ∈
        t1AmbientC (t1SelectedTriple A B Y hY).C →
        w ∈ t1AmbientH (t1SelectedTriple A B Y hY).K)
  constructor
  · exact le_trans (t1AmbientC_le_A (t1SelectedTriple A B Y hY).C) hY.1
  · intro w hw
    have hA : Y.transpose.toLin' w ∈ A :=
      t1AmbientC_le_A (t1SelectedTriple A B Y hY).C hw
    have hS : w ∈ t1SelectedPreimage A Y := by
      change Submodule.mkQ A (Y.transpose.toLin' w) = 0
      exact (Submodule.Quotient.mk_eq_zero A).mpr hA
    rw [t1SelectedTriple_ambientH]
    exact (Submodule.mem_sup).2 ⟨0, B.zero_mem, w, hS, by simp⟩

/-- Every ordinary-selected frequency gives its active triple in the
manuscript direction, with hybrid selection and actual rank additivity. -/
theorem t1SelectedTriple_active {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y) :
    t1ActiveTriple A B Y (t1SelectedTriple A B Y hY) := by
  exact ⟨t1SelectedTriple_hybridSelected A B Y hY,
    t1SelectedTriple_rankPrecedes A B Y hY⟩

/-- The descended theta determines its entire T1 triple uniquely. -/
theorem t1SelectedTriple_unique {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (hY : DR6OrdinarySelected A B Y)
    (t : T1IndexTriple A B)
    (ht : t1TripleToMap t = t1SelectedTheta A B Y hY) :
    t = t1SelectedTriple A B Y hY := by
  apply t1TripleToMap_injective
  calc
    t1TripleToMap t = t1SelectedTheta A B Y hY := ht
    _ = t1TripleToMap (t1SelectedTriple A B Y hY) :=
      (t1SelectedTriple_toMap A B Y hY).symm

/-- An active triple forces ordinary selection and its encoded map is the
actual inverse-frequency selector. Rank agreement supplies an H representative
for every A value; the hybrid selector moves a C correction back into H. -/
theorem t1ActiveTriple_forces_ordinary {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (t : T1IndexTriple A B)
    (ht : t1ActiveTriple A B Y t) :
    ∃ hY : DR6OrdinarySelected A B Y,
      t1TripleToMap t = t1SelectedTheta A B Y hY := by
  classical
  dsimp [t1ActiveTriple] at ht
  rcases ht with ⟨hsel, hRank⟩
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let R := t1OriginalRestriction Y C H
  let L := Y.transpose.toLin'
  have hdecomp := t1RankPrecedes_range_decomposition X R hRank
  have hXR : LinearMap.range X ≤ LinearMap.range R := by
    rw [hdecomp.1]
    exact le_sup_left
  have hpre : ∀ a : A, ∃ h : H, L h.val = a.val := by
    intro a
    let q := Submodule.mkQ C a.val
    have hqX : q ∈ LinearMap.range X := by
      rw [t1Pullback_range]
      exact ⟨t.C.mkQ a, by
        simpa [q, t1AQuotientToAmbient_apply_mk]⟩
    obtain ⟨h, hh⟩ := hXR hqX
    change Submodule.mkQ C (L h.val) = q at hh
    have hc : L h.val - a.val ∈ C :=
      (Submodule.Quotient.eq C).mp hh
    obtain ⟨w, hw⟩ := hsel.1 hc
    have hwH : w ∈ H := by
      apply hsel.2 w
      rw [hw]
      exact hc
    let h0 : H := ⟨h.val - w, H.sub_mem h.property hwH⟩
    have hvalue : L h0.val = a.val := by
      change L (h.val - w) = a.val
      rw [map_sub, hw]
      exact sub_sub_cancel (L h.val) a.val
    exact ⟨h0, hvalue⟩
  have hOrdRange : A ≤ LinearMap.range L := by
    intro a ha
    obtain ⟨h, hh⟩ := hpre ⟨a, ha⟩
    exact ⟨h.val, hh⟩
  have hOrdKer : LinearMap.ker L ≤ B := by
    intro w hw
    have hwH : w ∈ H := by
      apply hsel.2 w
      rw [hw]
      exact C.zero_mem
    let h : H := ⟨w, hwH⟩
    have hRzero : R h = 0 := by
      change Submodule.mkQ C (L w) = 0
      rw [hw]
      simp
    have hqXzero : R h ∈ LinearMap.range X := by
      rw [hRzero]
      exact ⟨0, by simp⟩
    have hXzero : X h = R h :=
      t1RankPrecedes_agreement_on_preimage X R hRank h
        hqXzero
    have hker : h ∈ LinearMap.ker X := by
      change X h = 0
      rw [hXzero, hRzero]
    rw [t1Pullback_ker] at hker
    change w ∈ B at hker
    exact hker
  let hY : DR6OrdinarySelected A B Y := ⟨hOrdRange, hOrdKer⟩
  refine ⟨hY, ?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨h, hh⟩ := hpre a
  let q := Submodule.mkQ C a.val
  have hqX : q ∈ LinearMap.range X := by
    rw [t1Pullback_range]
    exact ⟨t.C.mkQ a, by
      simpa [q, t1AQuotientToAmbient_apply_mk]⟩
  have hR : R h = q := by
    change Submodule.mkQ C (L h.val) = q
    rw [hh]
  have hqX' : R h ∈ LinearMap.range X := by
    rw [hR]
    exact hqX
  have hX : X h = q :=
      (t1RankPrecedes_agreement_on_preimage X R hRank h
      hqX').trans hR
  have hiff := (t1TripleToMap_pullback_iff t a h).2 hX
  have ha : L h.val ∈ A := by rw [hh]; exact a.property
  have hae : (⟨L h.val, ha⟩ : A) = a := by
    apply Subtype.ext
    exact hh
  calc
    t1TripleToMap t a = Submodule.mkQ B h.val := hiff
    _ = t1SelectedTheta A B Y hY ⟨L h.val, ha⟩ :=
      (t1SelectedTheta_on_preimage A B Y hY h.val ha).symm
    _ = t1SelectedTheta A B Y hY a := congrArg _ hae

/-- For a fixed frequency, the active index triple is forced to be the
canonical triple of its ordinary selector. This is the unconditional reverse
uniqueness direction, with ordinary selection derived from activity. -/
theorem t1ActiveTriple_unique {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (Y : BinaryMatrix n d) (t : T1IndexTriple A B)
    (ht : t1ActiveTriple A B Y t) :
    ∃ hY : DR6OrdinarySelected A B Y,
      t = t1SelectedTriple A B Y hY := by
  obtain ⟨hY, hmap⟩ := t1ActiveTriple_forces_ordinary A B Y t ht
  exact ⟨hY, t1SelectedTriple_unique A B Y hY t hmap⟩

/-- Ordinary-selected frequencies and active hybrid indices form equivalent
finite index types. Each selected frequency supplies its canonical triple;
activity recovers both the ordinary selector and the same triple. -/
noncomputable def t1OrdinaryActiveEquiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    {Y : BinaryMatrix n d // DR6OrdinarySelected A B Y} ≃
      {p : BinaryMatrix n d × T1IndexTriple A B //
        t1ActiveTriple A B p.1 p.2} where
  toFun y :=
    ⟨(y.val, t1SelectedTriple A B y.val y.property),
      t1SelectedTriple_active A B y.val y.property⟩
  invFun p :=
    ⟨p.val.1,
      Classical.choose (t1ActiveTriple_forces_ordinary
        A B p.val.1 p.val.2 p.property)⟩
  left_inv y := by
    apply Subtype.ext
    rfl
  right_inv p := by
    obtain ⟨hY, ht⟩ := t1ActiveTriple_unique
      A B p.val.1 p.val.2 p.property
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg (t1SelectedTriple A B p.val.1)
        (Subsingleton.elim _ _)).trans ht.symm

/-- Reindex any finite T1 summand along the exact ordinary/hybrid index
bijection. No selector injectivity or frequency orthogonality is assumed. -/
theorem t1OrdinaryActive_sum_equiv {n d : Nat} {R : Type}
    [AddCommMonoid R] (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : {Y : BinaryMatrix n d // DR6OrdinarySelected A B Y} → R) :
    (∑ y : {Y : BinaryMatrix n d // DR6OrdinarySelected A B Y}, g y) =
      ∑ p : {p : BinaryMatrix n d × T1IndexTriple A B //
        t1ActiveTriple A B p.1 p.2},
        g ((t1OrdinaryActiveEquiv A B).symm p) := by
  classical
  apply Fintype.sum_equiv (t1OrdinaryActiveEquiv A B)
  intro y
  simp

/-- The range of the actual quotient embedding A/C -> V/C is the image of
A under the ambient quotient map. -/
theorem t1AQuotientToAmbient_range {d : Nat}
    {A : Submodule F (V d)} (C : Submodule F A) :
    LinearMap.range (t1AQuotientToAmbient C) =
      A.map (Submodule.mkQ (t1AmbientC C)) := by
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective C q
    refine ⟨a.val, a.property, ?_⟩
    calc
      Submodule.mkQ (t1AmbientC C) a.val =
          t1AQuotientToAmbient C (Submodule.Quotient.mk a) :=
        (t1AQuotientToAmbient_apply_mk C a).symm
      _ = t1AQuotientToAmbient C q :=
        congrArg (t1AQuotientToAmbient C) ha
      _ = z := hq
  · rintro ⟨a, ha, hz⟩
    let a' : A := ⟨a, ha⟩
    refine ⟨C.mkQ a', ?_⟩
    calc
      t1AQuotientToAmbient C (C.mkQ a') =
          Submodule.mkQ (t1AmbientC C) a' :=
        t1AQuotientToAmbient_apply_mk C a'
      _ = z := hz

/-- The quotient of V/C by the actual X image is identified with V/A via
the quotient-of-a-quotient equivalence and the proved image equality. -/
noncomputable def t1OutputDomainEquiv {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    ((V d ⧸ t1AmbientC t.C) ⧸ LinearMap.range (t1PullbackMap t)) ≃ₗ[F]
      (V d ⧸ A) := by
  let C := t1AmbientC t.C
  let X := t1PullbackMap t
  have hCA : C ≤ A := t1AmbientC_le_A t.C
  have hRange : LinearMap.range X = A.map (Submodule.mkQ C) := by
    rw [t1Pullback_range, t1AQuotientToAmbient_range]
  exact (Submodule.quotEquivOfEq (LinearMap.range X)
      (A.map (Submodule.mkQ C)) hRange).trans
    (BinaryMatrixA1NestedCarrier.nestedDomainEquiv C A hCA)

/-- The kernel of the actual pullback, as a subspace of H, is linearly
identified with the original B by the H subtype. -/
noncomputable def t1OutputKernelEquiv {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    LinearMap.ker (t1PullbackMap t) ≃ₗ[F] B := by
  let H := t1AmbientH t.K
  let P := B.comap H.subtype
  have hBH : B ≤ H := t1AmbientH_containsB B t.K
  have hker : LinearMap.ker (t1PullbackMap t) = P := t1Pullback_ker t
  have hmap : P.map H.subtype = B := by
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_subtype]
      exact hBH)
  exact (LinearEquiv.ofEq _ _ hker).trans
    ((Submodule.equivMapOfInjective H.subtype H.injective_subtype P).trans
      (LinearEquiv.ofEq _ _ hmap))

/-- Actual output-carrier equivalence for the T1 triple. It identifies
Hom(V/A,B) with Hom((V/C)/range(Xtilde),ker(Xtilde)) using the two quotient
and subtype equivalences above. -/
noncomputable def t1OutputEquiv {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) :
    ((V d ⧸ A) →ₗ[F] B) ≃ₗ[F]
      (((V d ⧸ t1AmbientC t.C) ⧸
        LinearMap.range (t1PullbackMap t)) →ₗ[F]
        LinearMap.ker (t1PullbackMap t)) :=
  LinearEquiv.arrowCongr (t1OutputDomainEquiv t).symm
    (t1OutputKernelEquiv t).symm

/-- The output equivalence commutes with the actual affine embedding into
Hom(V,H): quotient representatives and B-subtype values agree pointwise. -/
theorem t1OutputEquiv_physicalSquare {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (M : (V d ⧸ A) →ₗ[F] B) :
    (((t1AmbientH t.K).subtype.comp
        ((LinearMap.ker (t1PullbackMap t)).subtype.comp
          ((t1OutputEquiv t M).comp
            (LinearMap.range (t1PullbackMap t)).mkQ))).comp
      (Submodule.mkQ (t1AmbientC t.C))) =
      B.subtype.comp (M.comp (Submodule.mkQ A)) := by
  let C := t1AmbientC t.C
  let X := t1PullbackMap t
  let eD := t1OutputDomainEquiv t
  let eK := t1OutputKernelEquiv t
  have hdomain (v : V d) :
      eD ((LinearMap.range X).mkQ (C.mkQ v)) = Submodule.mkQ A v := by
    simp [eD, t1OutputDomainEquiv,
      BinaryMatrixA1NestedCarrier.nestedDomainEquiv,
      t1AQuotientToAmbient_range, t1Pullback_range,
      Submodule.quotEquivOfEq_mk]
    exact Submodule.quotientQuotientEquivQuotientAux_mk_mk
      C A (t1AmbientC_le_A t.C) v
  have hkernel (b : B) :
      ((eK.symm b : LinearMap.ker X) : t1AmbientH t.K).val =
        B.subtype b := by
    unfold eK t1OutputKernelEquiv
    simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
    let H := t1AmbientH t.K
    let P := B.comap H.subtype
    have hval (x : P) : ((x : H) : W n) = H.subtype (x : H) := rfl
    rw [hval]
    rw [Submodule.map_equivMapOfInjective_symm_apply]
    exact LinearEquiv.coe_ofEq_apply _ _
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply]
  change ((eK.symm
      (M (eD ((LinearMap.range X).mkQ (C.mkQ v))) : B) :
        LinearMap.ker X) : t1AmbientH t.K).val =
      B.subtype (M (Submodule.mkQ A v))
  rw [hdomain v]
  exact hkernel _

/-- The arbitrary-base phase splits through the actual quotient/subtype
carrier; this is the cyclic trace identity used for the T1 phase. -/
theorem t1CarrierPhase_general {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (Y : W n →ₗ[F] V d) (T : V d →ₗ[F] W n)
    (M : (V d ⧸ C) →ₗ[F] H) :
    BinaryMatrixA1Phase.traceCharacter Y
      (T + H.subtype.comp (M.comp C.mkQ)) =
    BinaryMatrixA1Phase.traceCharacter Y T *
      BinaryMatrixA1Phase.traceCharacter
        (C.mkQ.comp (Y.comp H.subtype)) M :=
  BinaryMatrixA1Phase.traceCharacter_carrier_base_general C H Y T M
/-- The phase in an arbitrary T1 triple is the same ambient chi_Y(T),
followed by the typed output-frequency character on the physical output map. -/
theorem t1OutputPhase {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B) (Y : BinaryMatrix n d)
    (T : V d →ₗ[F] W n) (M : (V d ⧸ A) →ₗ[F] B) :
    BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
      (T + B.subtype.comp (M.comp (Submodule.mkQ A))) =
    BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
      BinaryMatrixA1Phase.traceCharacter
        ((t1AmbientC t.C).mkQ.comp
          (Y.transpose.toLin'.comp (t1AmbientH t.K).subtype))
        ((LinearMap.ker (t1PullbackMap t)).subtype.comp
          ((t1OutputEquiv t M).comp
            ((LinearMap.range (t1PullbackMap t)).mkQ))) := by
  let C := t1AmbientC t.C
  let H := t1AmbientH t.K
  let X := t1PullbackMap t
  let R := LinearMap.range X
  let K := LinearMap.ker X
  let N := t1OutputEquiv t M
  let Mraw : (V d ⧸ C) →ₗ[F] H :=
    K.subtype.comp (N.comp R.mkQ)
  have hsquare : H.subtype.comp (Mraw.comp C.mkQ) =
      B.subtype.comp (M.comp (Submodule.mkQ A)) := by
    simpa [Mraw, C, H, X, R, K, LinearMap.comp_assoc] using
      t1OutputEquiv_physicalSquare t M
  calc
    BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
        (T + B.subtype.comp (M.comp (Submodule.mkQ A))) =
      BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
        (T + H.subtype.comp (Mraw.comp C.mkQ)) := by
      congr 1
      rw [← hsquare]
    _ = BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
        BinaryMatrixA1Phase.traceCharacter
          (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) Mraw :=
      t1CarrierPhase_general C H Y.transpose.toLin' T Mraw

/-- The independently typed W6 Fourier operator for an arbitrary T1 triple
is exactly the existing actual ambient-matrix derivative after the output
carrier equivalence. -/
theorem t1TypedW6_eq_actual {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedW6FourierDerivative (t1AmbientC t.C) (t1AmbientH t.K)
      (t1PullbackMap t)
      (filteredCarrierFunction (t1AmbientC t.C)
        (t1AmbientH t.K) T f)
      (t1OutputEquiv t M) =
    actualW6Derivative
      (carrierFrequencyEquiv (t1AmbientC t.C)
        (t1AmbientH t.K) (t1PullbackMap t)) 0
      (fun K => filteredCarrierFunction (t1AmbientC t.C)
        (t1AmbientH t.K) T f
          ((carrierMatrixEquiv (t1AmbientC t.C)
            (t1AmbientH t.K)).symm K))
      ((typedW6OutputCoordinateEquiv (t1AmbientC t.C)
        (t1AmbientH t.K) (t1PullbackMap t)) (t1OutputEquiv t M)) := by
  exact typedW6FourierDerivative_eq_actual
    (t1AmbientC t.C) (t1AmbientH t.K) (t1PullbackMap t)
    (filteredCarrierFunction (t1AmbientC t.C) (t1AmbientH t.K) T f)
    (t1OutputEquiv t M)
/-- Full collision-preserving Fourier coefficient of the actual filtered
carrier input. Every ambient hybrid frequency in the fiber of Z contributes;
no injectivity of restriction Y -> q_C Y|H is asserted. -/
theorem t1FilteredCarrierFunction_fourierCoeff {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (Z : H →ₗ[F] (V d ⧸ C)) :
    complexCarrierFourierCoeff C H
      (filteredCarrierFunction C H T f) Z =
    ∑ Y : BinaryMatrix n d,
      if BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin' then
        if Z = C.mkQ.comp (Y.transpose.toLin'.comp H.subtype) then
          complexFourierCoeff f Y *
            (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex)
        else 0
      else 0 := by
  classical
  let qY := fun Y : BinaryMatrix n d =>
    C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)
  let cY := fun Y : BinaryMatrix n d =>
    complexFourierCoeff f Y *
      (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex)
  have hsignal : filteredCarrierFunction C H T f =
      fun N => ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)),
        if BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin' then
          cY Y * (BinaryMatrixA1Phase.traceCharacter (qY Y) N : Complex)
        else 0 := by
    funext N
    unfold filteredCarrierFunction complexAmbientAffineRestrict
      complexAmbientHybridFilter
    apply Finset.sum_congr rfl
    intro Y hY
    by_cases hsel :
        BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin'
    · simp only [if_pos hsel]
      have hphase := t1CarrierPhase_general C H
        Y.transpose.toLin' T N
      have hchar :
          character Y (LinearMap.toMatrix'
            (T + H.subtype.comp (N.comp C.mkQ))) =
        BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
          BinaryMatrixA1Phase.traceCharacter (qY Y) N := by
        calc
          character Y (LinearMap.toMatrix'
              (T + H.subtype.comp (N.comp C.mkQ))) =
            BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
              ((LinearMap.toMatrix'
                (T + H.subtype.comp (N.comp C.mkQ))).toLin') :=
            (BinaryMatrixA1CharacterBridge.traceCharacter_eq_matrix_character
              Y (LinearMap.toMatrix'
                (T + H.subtype.comp (N.comp C.mkQ)))).symm
          _ = BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
                (T + H.subtype.comp (N.comp C.mkQ)) := by
            simp only [Matrix.toLin'_toMatrix']
          _ = _ := hphase
      rw [hchar]
      simp only [Complex.ofReal_mul]
      ring
    · simp [hsel]
  rw [hsignal]
  rw [ActualBinaryMatrixHC46A18DerivativeRankProjection.complexCarrierFourierCoeff_finset_sum]
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases hsel :
      BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin'
  · simp only [if_pos hsel]
    simp [qY, cY,
      ActualBinaryMatrixHC46A18DerivativeRankProjection.complexCarrierFourierCoeff_smul,
      ActualBinaryMatrixHC46A18DerivativeRankProjection.complexCarrierFourierCoeff_character]
  · simp [hsel,
      PvNP.RealizableHardness.BinaryMatrixA1Complex.complexCarrierFourierCoeff]

/-- Substituting the full coefficient expansion into the independent typed W6
sum keeps the complete ambient-frequency fiber for each typed parent
frequency. The later T1 regrouping uses these explicit equalities rather than
assuming the restriction map on frequencies is injective. -/
theorem t1TypedW6_fullParentExpansion {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X : H →ₗ[F] (V d ⧸ C))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (N : ((V d ⧸ C) ⧸ LinearMap.range X) →ₗ[F] LinearMap.ker X) :
    typedW6FourierDerivative C H X
      (filteredCarrierFunction C H T f) N =
    ∑ Z : H →ₗ[F] (V d ⧸ C),
      if typedW6Precedes C H X Z then
        (∑ Y : BinaryMatrix n d,
          if BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin' then
            if Z = C.mkQ.comp (Y.transpose.toLin'.comp H.subtype) then
              complexFourierCoeff f Y *
                (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex)
            else 0
          else 0) *
          (BinaryMatrixA1Phase.traceCharacter Z
            ((LinearMap.ker X).subtype.comp
              (N.comp (LinearMap.range X).mkQ)) : Complex)
      else 0 := by
  classical
  simp_rw [typedW6FourierDerivative,
    t1FilteredCarrierFunction_fourierCoeff]

/-- After commuting the all-ambient-Y coefficient sum with the full typed
parent-frequency sum, each Y contributes at its actual restricted parent
frequency. Other ambient Y values in the same fiber remain separate summands. -/
theorem t1TypedW6_collapse_parentFiber {n d : Nat}
    (C : Submodule F (V d)) (H : Submodule F (W n))
    (X : H →ₗ[F] (V d ⧸ C))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (N : ((V d ⧸ C) ⧸ LinearMap.range X) →ₗ[F] LinearMap.ker X) :
    typedW6FourierDerivative C H X
      (filteredCarrierFunction C H T f) N =
    ∑ Y : BinaryMatrix n d,
      if BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin' ∧
          typedW6Precedes C H X
            (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) then
        complexFourierCoeff f Y *
          (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex) *
          (BinaryMatrixA1Phase.traceCharacter
            (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype))
            ((LinearMap.ker X).subtype.comp
              (N.comp (LinearMap.range X).mkQ)) : Complex)
      else 0 := by
  classical
  rw [t1TypedW6_fullParentExpansion]
  have hdistribute (Z : H →ₗ[F] (V d ⧸ C)) :
      (if typedW6Precedes C H X Z then
        (∑ Y : BinaryMatrix n d,
          if BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin' then
            if Z = C.mkQ.comp (Y.transpose.toLin'.comp H.subtype) then
              complexFourierCoeff f Y *
                (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex)
            else 0
          else 0) *
          (BinaryMatrixA1Phase.traceCharacter Z
            ((LinearMap.ker X).subtype.comp
              (N.comp (LinearMap.range X).mkQ)) : Complex)
      else 0) =
      ∑ Y : BinaryMatrix n d,
        if typedW6Precedes C H X Z ∧
            BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin' then
          (if Z = C.mkQ.comp (Y.transpose.toLin'.comp H.subtype) then
            complexFourierCoeff f Y *
              (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex)
          else 0) *
          (BinaryMatrixA1Phase.traceCharacter Z
            ((LinearMap.ker X).subtype.comp
              (N.comp (LinearMap.range X).mkQ)) : Complex)
        else 0 := by
    by_cases hpred : typedW6Precedes C H X Z
    · simp only [if_pos hpred]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Y _
      by_cases hsel :
          BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin'
      · simp [hsel, hpred]
      · simp [hsel]
    · simp [hpred]
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases hsel :
      BinaryMatrixNestedSelectorA1.Selected C H Y.transpose.toLin'
  · simp only [hsel, and_true, true_and]
    let qY := C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)
    rw [Finset.sum_eq_single qY]
    · by_cases hpred : typedW6Precedes C H X qY
      · simp [qY, hpred]
      · simp [qY, hpred]
    · intro Z hZ hne
      by_cases hpredZ : typedW6Precedes C H X Z
      · rw [if_pos hpredZ]
        rw [if_neg hne]
        simp
      · rw [if_neg hpredZ]
    · simp
  · simp [hsel]

/-- The full pointwise T1 decomposition on the actual affine carrier. The
ordinary selected-frequency sum is reindexed by the exact ordinary/active
equivalence; all ambient frequencies in every restricted-frequency fiber
remain present until that bijection is applied. -/
theorem t1OrdinaryProjection_affineExpansion {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    complexAmbientAffineRestrict A B T
      (DR6ComplexOrdinaryFilter A B f) M =
    ∑ Y : BinaryMatrix n d,
      if DR6OrdinarySelected A B Y then
        complexFourierCoeff f Y *
          ((BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
            BinaryMatrixA1Phase.traceCharacter
              (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M : ℝ) : Complex)
      else 0 := by
  classical
  unfold complexAmbientAffineRestrict DR6ComplexOrdinaryFilter
  simp_rw [dr6_complexSelector_iff_actualOrdinary]
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases hsel : DR6OrdinarySelected A B Y
  · simp only [if_pos hsel]
    have hchar :
        character Y (LinearMap.toMatrix'
          (T + B.subtype.comp (M.comp A.mkQ))) =
        BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
          BinaryMatrixA1Phase.traceCharacter
            (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M := by
      calc
        character Y (LinearMap.toMatrix'
            (T + B.subtype.comp (M.comp A.mkQ))) =
            BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
              ((LinearMap.toMatrix'
                (T + B.subtype.comp (M.comp A.mkQ))).toLin') :=
          (BinaryMatrixA1CharacterBridge.traceCharacter_eq_matrix_character
            Y (LinearMap.toMatrix'
              (T + B.subtype.comp (M.comp A.mkQ)))).symm
        _ = BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin'
              (T + B.subtype.comp (M.comp A.mkQ)) := by
          simp only [Matrix.toLin'_toMatrix']
        _ = _ := t1CarrierPhase_general A B Y.transpose.toLin' T M
    rw [hchar]
  · simp [hsel]

theorem t1PointwiseFull_fourierIdentity {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → Complex)
    (M : (V d ⧸ A) →ₗ[F] B) :
    complexAmbientAffineRestrict A B T
      (DR6ComplexOrdinaryFilter A B f) M =
      ∑ t : T1IndexTriple A B,
        typedW6FourierDerivative (t1AmbientC t.C) (t1AmbientH t.K)
          (t1PullbackMap t)
          (filteredCarrierFunction (t1AmbientC t.C)
            (t1AmbientH t.K) T f)
          (t1OutputEquiv t M) := by
  classical
  rw [t1OrdinaryProjection_affineExpansion]
  simp_rw [t1TypedW6_collapse_parentFiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y hY
  let ambientTerm := complexFourierCoeff f Y *
    ((BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
      BinaryMatrixA1Phase.traceCharacter
        (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M : ℝ) : Complex)
  have hactive_iff (t : T1IndexTriple A B) :
      (BinaryMatrixNestedSelectorA1.Selected (t1AmbientC t.C)
          (t1AmbientH t.K) Y.transpose.toLin' ∧
        typedW6Precedes (t1AmbientC t.C) (t1AmbientH t.K)
          (t1PullbackMap t)
          ((t1AmbientC t.C).mkQ.comp
            (Y.transpose.toLin'.comp (t1AmbientH t.K).subtype))) ↔
        t1ActiveTriple A B Y t := by
    unfold t1ActiveTriple typedW6Precedes t1RankPrecedes
      t1OriginalRestriction
    rfl
  by_cases hordinary : DR6OrdinarySelected A B Y
  · have hactive :
        t1ActiveTriple A B Y (t1SelectedTriple A B Y hordinary) :=
      t1SelectedTriple_active A B Y hordinary
    have hterm : ∀ t : T1IndexTriple A B,
        t1ActiveTriple A B Y t →
          complexFourierCoeff f Y *
            (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex) *
            (BinaryMatrixA1Phase.traceCharacter
              ((t1AmbientC t.C).mkQ.comp
                (Y.transpose.toLin'.comp (t1AmbientH t.K).subtype))
              ((LinearMap.ker (t1PullbackMap t)).subtype.comp
                ((t1OutputEquiv t M).comp
                  (LinearMap.range (t1PullbackMap t)).mkQ)) : Complex) =
          ambientTerm := by
      intro t ht
      let C := t1AmbientC t.C
      let H := t1AmbientH t.K
      let X := t1PullbackMap t
      let R := LinearMap.range X
      let K := LinearMap.ker X
      let Mraw := K.subtype.comp
        ((t1OutputEquiv t M).comp R.mkQ)
      have hphaseT := t1OutputPhase t Y T M
      have hphaseA := t1CarrierPhase_general A B
        Y.transpose.toLin' T M
      have hphase :
          BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
              BinaryMatrixA1Phase.traceCharacter
                (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) Mraw =
            BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
              BinaryMatrixA1Phase.traceCharacter
                (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M :=
        hphaseT.symm.trans hphaseA
      change complexFourierCoeff f Y *
          (BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex) *
          (BinaryMatrixA1Phase.traceCharacter
            (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) Mraw : Complex) =
        complexFourierCoeff f Y *
          ((BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
            BinaryMatrixA1Phase.traceCharacter
              (A.mkQ.comp (Y.transpose.toLin'.comp B.subtype)) M : ℝ) : Complex)
      calc
        _ = complexFourierCoeff f Y *
            ((BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T : Complex) *
              (BinaryMatrixA1Phase.traceCharacter
                (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) Mraw : Complex)) := by
              ring
        _ = complexFourierCoeff f Y *
            (((BinaryMatrixA1Phase.traceCharacter Y.transpose.toLin' T *
              BinaryMatrixA1Phase.traceCharacter
                (C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)) Mraw) : ℝ) : Complex) := by
              rw [← Complex.ofReal_mul]
        _ = _ := by rw [hphase]
    rw [Finset.sum_eq_single (t1SelectedTriple A B Y hordinary)]
    · have hguard := (hactive_iff
          (t1SelectedTriple A B Y hordinary)).2 hactive
      rw [if_pos hordinary, if_pos hguard]
      rw [hterm _ hactive]
    · intro t ht hne
      by_cases hact : t1ActiveTriple A B Y t
      · obtain ⟨hY', ht'⟩ := t1ActiveTriple_unique A B Y t hact
        have hproof : hY' = hordinary := Subsingleton.elim _ _
        have hteq : t = t1SelectedTriple A B Y hordinary := by
          simpa [hproof] using ht'
        exact False.elim (hne hteq)
      · have hguard : ¬ (BinaryMatrixNestedSelectorA1.Selected
            (t1AmbientC t.C) (t1AmbientH t.K) Y.transpose.toLin' ∧
          typedW6Precedes (t1AmbientC t.C) (t1AmbientH t.K)
            (t1PullbackMap t)
            ((t1AmbientC t.C).mkQ.comp
              (Y.transpose.toLin'.comp (t1AmbientH t.K).subtype))) := by
          intro ht
          exact hact ((hactive_iff t).1 ht)
        rw [if_neg hguard]
    · simp [t1ActiveTriple, hactive]
  · have hnoactive : ∀ t : T1IndexTriple A B,
        ¬ t1ActiveTriple A B Y t := by
      intro t ht
      obtain ⟨hY, _⟩ := t1ActiveTriple_forces_ordinary A B Y t ht
      exact hordinary hY
    rw [if_neg hordinary]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    have hguard : ¬ (BinaryMatrixNestedSelectorA1.Selected
          (t1AmbientC t.C) (t1AmbientH t.K) Y.transpose.toLin' ∧
        typedW6Precedes (t1AmbientC t.C) (t1AmbientH t.K)
          (t1PullbackMap t)
          ((t1AmbientC t.C).mkQ.comp
            (Y.transpose.toLin'.comp (t1AmbientH t.K).subtype))) := by
      intro ht
      exact hnoactive t ((hactive_iff t).1 ht)
    rw [if_neg hguard]
end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A7T1Transfer
