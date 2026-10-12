import PvNP.RealizableHardness.ActualBinaryMatrixHC46A9ActualFiber
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The actual ambient fixed-final A9 predecessor fiber.

The carrier below stores subspaces in the original ambient modules and the
fixed-final equation is quotient-after-restriction.  Its section/extension
normal form is the canonical factorization through `range Y`; no graph
coordinates, complements, or choices of bases occur in the carrier.
-/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A7PredecessorCount

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

abbrev F := ZMod 2

/-- Actual initial codomain subspaces, represented inside the final `A`. -/
abbrev A9AmbientA0 (V : Type*) [AddCommGroup V] [Module F V]
    (A : Submodule F V) (i : Nat) :=
  {A0 : Submodule F V // A0 ≤ A ∧ Module.finrank F A0 = i}

/-- Actual initial domain subspaces in the original `W`, with the manuscript
codimension condition recorded as a quotient dimension. -/
abbrev A9AmbientB0 (W : Type*) [AddCommGroup W] [Module F W]
    (B : Submodule F W) (j : Nat) :=
  {B0 : Submodule F W // B ≤ B0 ∧ Module.finrank F (W ⧸ B0) = j}

noncomputable instance a9AmbientA0Fintype
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (A : Submodule F V) (i : Nat) : Fintype (A9AmbientA0 V A i) :=
  Fintype.ofFinite _

noncomputable instance a9AmbientB0Fintype
    {W : Type*} [AddCommGroup W] [Module F W] [Fintype W]
    (B : Submodule F W) (j : Nat) : Fintype (A9AmbientB0 W B j) :=
  Fintype.ofFinite _

noncomputable instance a9AmbientQuotientFintype
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (A : Submodule F V) : Fintype (V ⧸ A) := Fintype.ofFinite _

noncomputable instance a9AmbientLinearMapFintype
    {P Q : Type*} [AddCommGroup P] [Module F P] [Fintype P]
    [AddCommGroup Q] [Module F Q] [Fintype Q] : Fintype (P →ₗ[F] Q) := by
  classical
  letI : Finite (P →ₗ[F] Q) :=
    Finite.of_injective (fun f : P →ₗ[F] Q => (f : P → Q))
      (fun f g h => LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

/-- Actual subspaces `A0 <= A` are the same Grassmann carrier as
subspaces of `A`; the equivalence is induced by the actual subtype map. -/
noncomputable def a9AmbientA0Equiv
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [Fintype V] (A : Submodule F V) (i : Nat) :
    A9AmbientA0 V A i ≃ W6Grass A i where
  toFun A0 :=
    ⟨A0.1.comap A.subtype, by
      rw [(Submodule.comapSubtypeEquivOfLe A0.2.1).finrank_eq]
      exact A0.2.2⟩
  invFun U :=
    ⟨U.1.map A.subtype, Submodule.map_subtype_le A U.1, by
      rw [Submodule.finrank_map_subtype_eq, U.2]⟩
  left_inv A0 := by
    apply Subtype.ext
    apply Submodule.ext
    intro v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      exact ⟨⟨v, A0.2.1 hv⟩, hv, rfl⟩
  right_inv U := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_self (by simp)

/-- The canonical map `(V ⧸ A0) -> (V ⧸ A)`. -/
@[reducible]
def a9AmbientQuotientMap
    {V : Type*} [AddCommGroup V] [Module F V]
    (A : Submodule F V) {i : Nat} (A0 : A9AmbientA0 V A i) :
    (V ⧸ A0.1) →ₗ[F] (V ⧸ A) :=
  A0.1.liftQ A.mkQ (by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero A).2 (A0.2.1 hv))

/-- The canonical inclusion of the actual final domain `B` into an allowed
actual initial domain `B0`. -/
@[reducible]
def a9AmbientBIncl
    {W : Type*} [AddCommGroup W] [Module F W]
    (B : Submodule F W) {j : Nat} (B0 : A9AmbientB0 W B j) :
    B →ₗ[F] B0.1 :=
  (B.comap B0.1.subtype).subtype.comp
    (Submodule.comapSubtypeEquivOfLe B0.2.1).symm.toLinearMap

theorem a9AmbientBIncl_toAmbient
    {W : Type*} [AddCommGroup W] [Module F W]
    (B : Submodule F W) {j : Nat} (B0 : A9AmbientB0 W B j) :
    B0.1.subtype.comp (a9AmbientBIncl B B0) = B.subtype := by
  ext b
  rfl

/-- The fixed-final map obtained from an ambient predecessor. -/
@[reducible]
def a9AmbientFinalMap
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (A : Submodule F V) (B : Submodule F W) {i j : Nat}
    (A0 : A9AmbientA0 V A i) (B0 : A9AmbientB0 W B j)
    (X : B0.1 →ₗ[F] (V ⧸ A0.1)) : B →ₗ[F] (V ⧸ A) :=
  (a9AmbientQuotientMap A A0).comp (X.comp (a9AmbientBIncl B B0))

/-- One actual predecessor triple over the fixed final pair `(A,B)` and
frequency `Y`. -/
@[ext]
structure A9AmbientInitialDatum
    (V W : Type*) [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    (i j : Nat) where
  A0 : A9AmbientA0 V A i
  B0 : A9AmbientB0 W B j
  X : B0.1 →ₗ[F] (V ⧸ A0.1)
  induces : a9AmbientFinalMap A B A0 B0 X = Y

/-- The actual ambient fixed-final fiber.  The input `Y` remains a parameter,
and every member retains the equation `q_(A0,A) o X o inclusion_(B,B0)=Y`. -/
abbrev A9AmbientFixedFinalFiber
    (V W : Type*) [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    (i j k : Nat) :=
  {x : A9AmbientInitialDatum V W A B Y i j //
    Module.finrank F (LinearMap.range x.X) = k}

/-- The section-lift carrier over `im Y`.  This is a fiber of the actual
quotient map, not a graph map into a chosen complement. -/
@[reducible]
def A9AmbientSectionLift
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {i : Nat} (A0 : A9AmbientA0 V A i) :=
  {ell : LinearMap.range Y →ₗ[F] (V ⧸ A0.1) //
    (a9AmbientQuotientMap A A0).comp ell = (LinearMap.range Y).subtype}

/-- The extension carrier over `im Y`, with the prescribed restriction to
the actual final domain `B`. -/
@[reducible]
def A9AmbientExtension
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {j : Nat} (B0 : A9AmbientB0 W B j) :=
  {psi : B0.1 →ₗ[F] LinearMap.range Y //
    psi.comp (a9AmbientBIncl B B0) = Y.rangeRestrict}

/-- The canonical dependent section/extension carrier. -/
@[reducible]
def A9AmbientSectionExtensionCarrier
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    (i j : Nat) :=
  Σ A0 : A9AmbientA0 V A i,
    Σ B0 : A9AmbientB0 W B j,
      A9AmbientSectionLift A B Y A0 × A9AmbientExtension A B Y B0


noncomputable instance a9AmbientInitialDatumFintype
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    (i j : Nat) : Fintype (A9AmbientInitialDatum V W A B Y i j) := by
  let f : A9AmbientInitialDatum V W A B Y i j →
      (Σ A0 : A9AmbientA0 V A i, Σ B0 : A9AmbientB0 W B j,
        B0.1 →ₗ[F] (V ⧸ A0.1)) := fun x => ⟨x.A0, x.B0, x.X⟩
  letI := Finite.of_injective f (by
    intro x y h
    cases x with | mk A0 B0 X hx =>
      cases y with | mk A0' B0' X' hy =>
        dsimp [f] at h
        have hA := congrArg Sigma.fst h
        cases hA
        have hrest : (⟨B0, X⟩ : Σ B0 : A9AmbientB0 W B j,
            B0.1 →ₗ[F] (V ⧸ A0.1)) = ⟨B0', X'⟩ :=
          eq_of_heq (Sigma.mk.inj h).2
        have hB := congrArg Sigma.fst hrest
        cases hB
        have hX : X = X' := eq_of_heq (Sigma.mk.inj hrest).2
        cases hX
        rfl)
  exact Fintype.ofFinite _

noncomputable instance a9AmbientFixedFinalFiberFintype
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    (i j k : Nat) : Fintype (A9AmbientFixedFinalFiber V W A B Y i j k) :=
  Fintype.ofFinite _

noncomputable instance a9AmbientSectionLiftFintype
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {i : Nat} (A0 : A9AmbientA0 V A i) :
    Fintype (A9AmbientSectionLift A B Y A0) := by
  unfold A9AmbientSectionLift
  exact Fintype.ofFinite _

noncomputable instance a9AmbientExtensionFintype
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {j : Nat} (B0 : A9AmbientB0 W B j) :
    Fintype (A9AmbientExtension A B Y B0) := by
  unfold A9AmbientExtension
  exact Fintype.ofFinite _

noncomputable instance a9AmbientCarrierFintype
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    (i j : Nat) : Fintype (A9AmbientSectionExtensionCarrier A B Y i j) := by
  unfold A9AmbientSectionExtensionCarrier
  exact Fintype.ofFinite _

/-- Translate the affine section fiber to maps into the quotient kernel.
The base lift is used only to count the fiber; the carrier and its pointwise
meaning remain independent of that temporary choice. -/
noncomputable def a9AmbientSectionTranslationEquiv
    {C E : Type*} [AddCommGroup C] [Module F C]
    [AddCommGroup E] [Module F E]
    (q : C →ₗ[F] E) (S : Submodule F E)
    (ell0 : S →ₗ[F] C) (hell0 : q.comp ell0 = S.subtype) :
    {ell : S →ₗ[F] C // q.comp ell = S.subtype} ≃
      (S →ₗ[F] LinearMap.ker q) where
  toFun ell :=
    (ell.1 - ell0).codRestrict (LinearMap.ker q) (by
      intro s
      apply LinearMap.mem_ker.mpr
      have h := congrFun (congrArg DFunLike.coe ell.2) s
      have h0 := congrFun (congrArg DFunLike.coe hell0) s
      simp only [LinearMap.comp_apply] at h h0
      simp [h, h0])
  invFun g := ⟨ell0 + (LinearMap.ker q).subtype.comp g, by
    ext s
    have h0 := congrFun (congrArg DFunLike.coe hell0) s
    simp only [LinearMap.comp_apply] at h0
    simp [LinearMap.comp_apply, h0]⟩
  left_inv := by
    intro ell
    apply Subtype.ext
    ext s
    change ell0 s + (ell.1 s - ell0 s) = ell.1 s
    abel
  right_inv := by
    intro g
    ext s
    change (ell0 s + (g s : C)) - ell0 s = (g s : C)
    abel

/-- Translate an extension fiber to linear maps out of the actual quotient
`B0/(B0.comap subtype B)`. -/
noncomputable def a9AmbientExtensionTranslationEquiv
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {j : Nat} (B0 : A9AmbientB0 W B j)
    (psi0 : B0.1 →ₗ[F] LinearMap.range Y)
    (hpsi0 : psi0.comp (a9AmbientBIncl B B0) = Y.rangeRestrict) :
    A9AmbientExtension A B Y B0 ≃
      ((B0.1 ⧸ B.comap B0.1.subtype) →ₗ[F] LinearMap.range Y) := by
  let P := B.comap B0.1.subtype
  let delta (psi : A9AmbientExtension A B Y B0) := psi.1 - psi0
  have hvanish (psi : A9AmbientExtension A B Y B0) :
      P ≤ LinearMap.ker (delta psi) := by
    intro z hz
    apply LinearMap.mem_ker.mpr
    let e := Submodule.comapSubtypeEquivOfLe B0.2.1
    let b : B := e ⟨z, hz⟩
    have hinc : a9AmbientBIncl B B0 b = z := by
      apply Subtype.ext
      rfl
    have hrestriction := congrFun (congrArg DFunLike.coe psi.2) b
    have hbase := congrFun (congrArg DFunLike.coe hpsi0) b
    change psi.1 (a9AmbientBIncl B B0 b) = Y.rangeRestrict b at hrestriction
    change psi0 (a9AmbientBIncl B B0 b) = Y.rangeRestrict b at hbase
    change psi.1 z - psi0 z = 0
    rw [← hinc, hrestriction, hbase]
    simp
  refine
    { toFun := fun psi => P.liftQ (delta psi) (hvanish psi)
      invFun := fun g => ⟨psi0 + g.comp P.mkQ, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply LinearMap.ext
    intro b
    have hmem : a9AmbientBIncl B B0 b ∈ P := by
      change B0.1.subtype (a9AmbientBIncl B B0 b) ∈ B
      exact b.2
    have hzero : P.mkQ (a9AmbientBIncl B B0 b) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero P).mpr hmem
    have hbase := congrFun (congrArg DFunLike.coe hpsi0) b
    change psi0 (a9AmbientBIncl B B0 b) = Y.rangeRestrict b at hbase
    change psi0 (a9AmbientBIncl B B0 b) +
      g (P.mkQ (a9AmbientBIncl B B0 b)) = Y.rangeRestrict b
    rw [hbase, hzero, map_zero, add_zero]
  · intro psi
    apply Subtype.ext
    apply LinearMap.ext
    intro b0
    have h := congrArg (fun f : B0.1 →ₗ[F] LinearMap.range Y => f b0) (P.liftQ_mkQ (delta psi) (hvanish psi))
    simp only [LinearMap.comp_apply] at h
    change psi0 b0 + (P.liftQ (delta psi) (hvanish psi)) (P.mkQ b0) = psi.1 b0
    rw [h]
    change psi0 b0 + (psi.1 b0 - psi0 b0) = psi.1 b0
    abel
  · intro g
    apply LinearMap.ext
    intro q
    obtain ⟨b0, rfl⟩ := P.mkQ_surjective q
    change (psi0 b0 + g (P.mkQ b0)) - psi0 b0 = g (P.mkQ b0)
    abel

/-- The actual A8 image lift `A1`, whose quotient by `A0` is `range X`. -/
def a9AmbientImageLift
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j : Nat} (x : A9AmbientInitialDatum V W A B Y i j) :
    Submodule F V := (LinearMap.range x.X).comap x.A0.1.mkQ

/-- The A8 kernel `B1` embedded in the original `W`. -/
def a9AmbientKernelInW
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j : Nat} (x : A9AmbientInitialDatum V W A B Y i j) :
    Submodule F W := (LinearMap.ker x.X).map x.B0.1.subtype

/-- The A8 selector side conditions on an actual ambient predecessor. -/
def a9AmbientA8SideConditions
    {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j : Nat} (x : A9AmbientInitialDatum V W A B Y i j) : Prop :=
  A ⊓ a9AmbientImageLift x = x.A0.1 ∧
    B ⊔ a9AmbientKernelInW x = x.B0.1

/-- Restricting `X` to `B` cannot have rank above the ambient map, and the
fixed-final law plus equality of final ranks forces equality. -/
theorem a9Ambient_restriction_rank
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientInitialDatum V W A B Y i j)
    (hX : Module.finrank F (LinearMap.range x.X) = k) :
    Module.finrank F
      (LinearMap.range (x.X.comp (a9AmbientBIncl B x.B0))) = k := by
  let g := x.X.comp (a9AmbientBIncl B x.B0)
  let q := a9AmbientQuotientMap A x.A0
  have hqg : q.comp g = Y := by
    simpa [q, g, a9AmbientFinalMap] using x.induces
  have hYle : Module.finrank F (LinearMap.range Y) ≤
      Module.finrank F (LinearMap.range g) := by
    let rG := g.rangeRestrict
    let qR := q.domRestrict (LinearMap.range g)
    have hcomp : qR.comp rG = q.comp g := by
      ext b
      rfl
    have hle : Module.finrank F (LinearMap.range (q.comp g)) ≤
        Module.finrank F (LinearMap.range g) := by
      rw [← hcomp, LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_rangeRestrict g)]
      exact qR.finrank_range_le
    exact (congrArg (fun f : B →ₗ[F] (V ⧸ A) =>
      Module.finrank F (LinearMap.range f)) hqg).symm.trans_le hle
  have hgX : LinearMap.range g ≤ LinearMap.range x.X := by
    intro z hz
    rcases LinearMap.mem_range.mp hz with ⟨b, rfl⟩
    exact LinearMap.mem_range.mpr ⟨a9AmbientBIncl B x.B0 b, rfl⟩
  have hhi := Submodule.finrank_mono hgX
  rw [hY] at hYle
  rw [hX] at hhi
  exact le_antisymm hhi hYle

/-- The restriction to `B` has the same actual image as `X` in the fixed
ambient fiber. -/
theorem a9Ambient_restriction_range
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientInitialDatum V W A B Y i j)
    (hX : Module.finrank F (LinearMap.range x.X) = k) :
    LinearMap.range (x.X.comp (a9AmbientBIncl B x.B0)) = LinearMap.range x.X := by
  apply Submodule.eq_of_le_of_finrank_eq
    (show LinearMap.range (x.X.comp (a9AmbientBIncl B x.B0)) ≤
      LinearMap.range x.X from LinearMap.range_comp_le_range _ _)
  rw [a9Ambient_restriction_rank hY x hX, hX]

/-- The quotient-after-`X` map has image exactly `im Y`. -/
theorem a9Ambient_quotient_range
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientInitialDatum V W A B Y i j)
    (hX : Module.finrank F (LinearMap.range x.X) = k) :
    LinearMap.range ((a9AmbientQuotientMap A x.A0).comp x.X) =
      LinearMap.range Y := by
  let qX := (a9AmbientQuotientMap A x.A0).comp x.X
  have hYle : LinearMap.range Y ≤ LinearMap.range qX := by
    intro z hz
    rcases LinearMap.mem_range.mp hz with ⟨b, rfl⟩
    refine LinearMap.mem_range.mpr ⟨a9AmbientBIncl B x.B0 b, ?_⟩
    have heq := x.induces
    exact congrFun (congrArg DFunLike.coe heq) b
  have hqXle : Module.finrank F (LinearMap.range qX) ≤ k := by
    let rX := x.X.rangeRestrict
    let qR := (a9AmbientQuotientMap A x.A0).domRestrict (LinearMap.range x.X)
    have hcomp : qR.comp rX = qX := by
      ext b
      rfl
    rw [← hcomp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_rangeRestrict x.X)]
    exact qR.finrank_range_le.trans (by simpa [hX])
  have hlo := Submodule.finrank_mono hYle
  rw [hY] at hlo
  have hEq : Module.finrank F (LinearMap.range qX) = k := le_antisymm hqXle hlo
  exact (Submodule.eq_of_le_of_finrank_eq hYle (by rw [hEq, hY])).symm

/-- The canonical section factor of an actual predecessor is the unique map
on `im Y` whose quotient is its subtype inclusion and which reconstructs the
restriction of `X` to `B`. -/
theorem a9Ambient_section_existsUnique
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientInitialDatum V W A B Y i j)
    (hX : Module.finrank F (LinearMap.range x.X) = k) :
    ∃! ell : LinearMap.range Y →ₗ[F] (V ⧸ x.A0.1),
      (a9AmbientQuotientMap A x.A0).comp ell = (LinearMap.range Y).subtype ∧
      ell.comp Y.rangeRestrict = x.X.comp (a9AmbientBIncl B x.B0) := by
  let g := x.X.comp (a9AmbientBIncl B x.B0)
  let y := Y.rangeRestrict
  have hy : Function.Surjective y := LinearMap.surjective_rangeRestrict Y
  have hqg : (a9AmbientQuotientMap A x.A0).comp g = Y := by
    simpa [g, a9AmbientFinalMap] using x.induces
  have hgrange := a9Ambient_restriction_range hY x hX
  have hqR :
      LinearMap.range ((a9AmbientQuotientMap A x.A0).domRestrict
        (LinearMap.range g)) = LinearMap.range Y := by
    let qR := (a9AmbientQuotientMap A x.A0).domRestrict (LinearMap.range g)
    have hcomp : qR.comp g.rangeRestrict = (a9AmbientQuotientMap A x.A0).comp g := by
      ext b
      rfl
    change LinearMap.range qR = LinearMap.range Y
    calc
      LinearMap.range qR = LinearMap.range (qR.comp g.rangeRestrict) :=
        (LinearMap.range_comp_of_range_eq_top _
          (LinearMap.range_rangeRestrict g)).symm
      _ = LinearMap.range Y := congrArg LinearMap.range (hcomp.trans hqg)
  have hqRrank : Module.finrank F
      (LinearMap.range ((a9AmbientQuotientMap A x.A0).domRestrict
        (LinearMap.range g))) = k := by
    rw [hqR, hY]
  have hgRank : Module.finrank F (LinearMap.range g) = k :=
    a9Ambient_restriction_rank hY x hX
  have hqRker : LinearMap.ker
      ((a9AmbientQuotientMap A x.A0).domRestrict
        (LinearMap.range g)) = ⊥ := by
    apply (Submodule.finrank_eq_zero).mp
    have hnull :=
      ((a9AmbientQuotientMap A x.A0).domRestrict
        (LinearMap.range g)).finrank_range_add_finrank_ker
    rw [hqRrank, hgRank] at hnull
    omega
  have hker : LinearMap.ker y ≤ LinearMap.ker g := by
    intro b hb
    apply LinearMap.mem_ker.mpr
    have hyb : Y b = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hb)
    have hgb : g b ∈ LinearMap.range g := LinearMap.mem_range_self g b
    have hqzero : (a9AmbientQuotientMap A x.A0) (g b) = 0 := by
      have h := congrFun (congrArg DFunLike.coe hqg) b
      exact h.trans hyb
    have hmem : (⟨g b, hgb⟩ : LinearMap.range g) ∈
        LinearMap.ker ((a9AmbientQuotientMap A x.A0).domRestrict
          (LinearMap.range g)) := by
      exact LinearMap.mem_ker.mpr hqzero
    have hmem0 : (⟨g b, hgb⟩ : LinearMap.range g) ∈
        (⊥ : Submodule F (LinearMap.range g)) := by
      rw [← hqRker]
      exact hmem
    simpa using hmem0
  let e := y.quotKerEquivOfSurjective hy
  let gbar := (LinearMap.ker y).liftQ g hker
  let ell := gbar.comp e.symm.toLinearMap
  have hfactor : ell.comp y = g := by
    ext b
    have he : e.symm (y b) = (LinearMap.ker y).mkQ b :=
      LinearMap.quotKerEquivOfSurjective_symm_apply y hy b
    change gbar (e.symm (y b)) = g b
    rw [he]
    rfl
  have hsection : (a9AmbientQuotientMap A x.A0).comp ell =
      (LinearMap.range Y).subtype := by
    ext s
    obtain ⟨b, rfl⟩ := hy s
    change (a9AmbientQuotientMap A x.A0) (ell (y b)) = Y b
    rw [show ell (y b) = g b from congrArg (fun f : B →ₗ[F] (V ⧸ x.A0.1) => f b) hfactor]
    exact congrFun (congrArg DFunLike.coe hqg) b
  refine ⟨ell, ⟨hsection, hfactor⟩, ?_⟩
  intro ell' h'
  apply LinearMap.ext
  intro s
  obtain ⟨b, rfl⟩ := hy s
  exact (congrFun (congrArg DFunLike.coe h'.2) b).trans
    (congrFun (congrArg DFunLike.coe hfactor) b).symm

/-- The extension factor of an actual predecessor is quotient-after-`X`,
with codomain restricted to `im Y`. -/
@[reducible]
noncomputable def a9AmbientForwardExtension
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientInitialDatum V W A B Y i j)
    (hX : Module.finrank F (LinearMap.range x.X) = k) :
    A9AmbientExtension A B Y x.B0 := by
  let qX := (a9AmbientQuotientMap A x.A0).comp x.X
  have hrange := a9Ambient_quotient_range hY x hX
  refine ⟨qX.codRestrict (LinearMap.range Y) (by
    intro b
    exact hrange ▸ LinearMap.mem_range_self qX b), ?_⟩
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  change qX (a9AmbientBIncl B x.B0 b) = Y b
  have heq := x.induces
  exact congrFun (congrArg DFunLike.coe heq) b


/-- Both canonical factors reconstruct the original actual ambient map. -/
theorem a9Ambient_forward_factorization
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientInitialDatum V W A B Y i j)
    (hX : Module.finrank F (LinearMap.range x.X) = k) :
    (Classical.choose (a9Ambient_section_existsUnique hY x hX)).comp
        (a9AmbientForwardExtension hY x hX).1 = x.X := by
  let ell := Classical.choose (a9Ambient_section_existsUnique hY x hX)
  let psi := (a9AmbientForwardExtension hY x hX).1
  have hell := (Classical.choose_spec (a9Ambient_section_existsUnique hY x hX)).1.2
  have hpsi := (a9AmbientForwardExtension hY x hX).2
  let q := a9AmbientQuotientMap A x.A0
  let g := x.X.comp (a9AmbientBIncl B x.B0)
  have hqg : q.comp g = Y := by
    simpa [g, q, a9AmbientFinalMap] using x.induces
  apply LinearMap.ext
  intro b0
  have hb : x.X b0 ∈ LinearMap.range
      g := by
    rw [a9Ambient_restriction_range hY x hX]
    exact LinearMap.mem_range_self x.X b0
  rcases LinearMap.mem_range.mp hb with ⟨b, hbg⟩
  have hval : (psi b0).val = Y b := by
    change ((a9AmbientQuotientMap A x.A0).comp x.X) b0 = Y b
    calc
      (q.comp x.X) b0 = (q.comp g) b := by
        exact congrArg q (hbg.symm)
      _ = Y b := congrFun (congrArg DFunLike.coe hqg) b
  have hys : Y.rangeRestrict b = psi b0 := Subtype.ext hval.symm
  calc
    ell (psi b0) = ell (Y.rangeRestrict b) := by rw [hys]
    _ = x.X (a9AmbientBIncl B x.B0 b) := by
      exact congrFun (congrArg DFunLike.coe hell) b
    _ = x.X b0 := hbg

/-- One section/extension carrier element determines an actual rank-k
predecessor and preserves the fixed-final equation. -/
@[reducible]
noncomputable def a9AmbientInverse
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (c : A9AmbientSectionExtensionCarrier A B Y i j) :
    A9AmbientFixedFinalFiber V W A B Y i j k := by
  let A0 := c.1
  let B0 := c.2.1
  let ell := c.2.2.1.1
  let psi := c.2.2.2.1
  let X := ell.comp psi
  have hfinal : a9AmbientFinalMap A B A0 B0 X = Y := by
    ext b
    change (a9AmbientQuotientMap A A0) (ell (psi (a9AmbientBIncl B B0 b))) = Y b
    have hsec := c.2.2.1.2
    have hext := c.2.2.2.2
    calc
      (a9AmbientQuotientMap A A0) (ell (psi (a9AmbientBIncl B B0 b))) =
          (LinearMap.range Y).subtype (psi (a9AmbientBIncl B B0 b)) :=
        congrFun (congrArg DFunLike.coe hsec) _
      _ = Y b := congrArg Subtype.val (congrFun (congrArg DFunLike.coe hext) b)
  have hell_inj : Function.Injective ell := by
    intro s t h
    have hh := congrArg (a9AmbientQuotientMap A A0) h
    have ht := c.2.2.1.2
    have hst := congrFun (congrArg DFunLike.coe ht) s
    have htt := congrFun (congrArg DFunLike.coe ht) t
    apply Subtype.ext
    exact hst.symm.trans (hh.trans htt)
  have hpsi_surj : Function.Surjective psi := by
    intro s
    obtain ⟨b, hb⟩ := LinearMap.surjective_rangeRestrict Y s
    exact ⟨a9AmbientBIncl B B0 b, by
      have h := congrFun (congrArg DFunLike.coe c.2.2.2.2) b
      exact h.trans hb⟩
  have hXrank : Module.finrank F (LinearMap.range X) = k := by
    have hrange : LinearMap.range X = LinearMap.range ell := by
      apply le_antisymm
      · exact LinearMap.range_comp_le_range _ _
      · intro z hz
        rcases LinearMap.mem_range.mp hz with ⟨s, rfl⟩
        obtain ⟨b0, hb0⟩ := hpsi_surj s
        exact LinearMap.mem_range.mpr
          ⟨b0, by simpa [X] using congrArg ell hb0⟩
    rw [hrange]
    rw [LinearMap.finrank_range_of_inj hell_inj]
    exact hY
  exact ⟨⟨A0, B0, X, hfinal⟩, hXrank⟩


/-- Forward map to the canonical section/extension carrier. -/
@[reducible]
noncomputable def a9AmbientForward
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientFixedFinalFiber V W A B Y i j k) :
    A9AmbientSectionExtensionCarrier A B Y i j := by
  let ell := Classical.choose (a9Ambient_section_existsUnique hY x.1 x.2)
  let hell := Classical.choose_spec (a9Ambient_section_existsUnique hY x.1 x.2)
  let psi := a9AmbientForwardExtension hY x.1 x.2
  exact ⟨x.1.A0, x.1.B0,
    ⟨⟨ell, hell.1.1⟩, psi⟩⟩


/-- The inverse carrier map uses exactly the prescribed section after
extension, with no additional map coordinates. -/
theorem a9AmbientInverse_map
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (c : A9AmbientSectionExtensionCarrier A B Y i j) :
    (a9AmbientInverse hY c).1.X = c.2.2.1.1.comp c.2.2.2.1 := rfl

/-- The inverse carrier map followed by the forward map recovers both
canonical affine factors. -/
theorem a9Ambient_forward_inverse_carrier
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (c : A9AmbientSectionExtensionCarrier A B Y i j) :
    a9AmbientForward hY (a9AmbientInverse hY c) = c := by
  rcases c with ⟨A0, B0, ⟨ell, hell⟩, ⟨psi, hpsi⟩⟩
  let x := a9AmbientInverse hY
    ⟨A0, B0, ⟨ell, hell⟩, ⟨psi, hpsi⟩⟩
  have hfactor : ell.comp Y.rangeRestrict =
      x.1.X.comp (a9AmbientBIncl B B0) := by
    ext b
    change ell (Y.rangeRestrict b) = ell (psi (a9AmbientBIncl B B0 b))
    exact congrArg ell (congrArg (fun f : B →ₗ[F] LinearMap.range Y => f b) hpsi).symm
  have hsectionUnique := a9Ambient_section_existsUnique hY x.1 x.2
  have hEll : ell = Classical.choose hsectionUnique := by
    exact (Classical.choose_spec hsectionUnique).2 ell ⟨hell, hfactor⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Prod.ext
  · apply Subtype.ext
    apply LinearMap.ext
    intro s
    change (Classical.choose hsectionUnique) s = ell s
    exact congrArg (fun f : LinearMap.range Y →ₗ[F] (V ⧸ A0.1) => f s) hEll.symm
  · apply Subtype.ext
    apply LinearMap.ext
    intro b0
    change ((a9AmbientForwardExtension hY x.1 x.2).1 b0) = psi b0
    have hqell : (a9AmbientQuotientMap A A0).comp ell =
        (LinearMap.range Y).subtype := hell
    apply Subtype.ext
    change (a9AmbientQuotientMap A A0) (ell (psi b0)) =
      (psi b0).val
    exact congrArg (fun f : LinearMap.range Y →ₗ[F] (V ⧸ A) => f (psi b0)) hqell

/-- Forward and inverse maps form the actual ambient A9 equivalence. -/
noncomputable def a9AmbientFiberEquiv
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k) :
    A9AmbientFixedFinalFiber V W A B Y i j k ≃
      A9AmbientSectionExtensionCarrier A B Y i j where
  toFun := a9AmbientForward hY
  invFun := a9AmbientInverse hY
  left_inv := by
    intro x
    apply Subtype.ext
    rcases x with ⟨⟨A0, B0, X, hinduces⟩, hX⟩
    apply A9AmbientInitialDatum.ext
    · rfl
    · rfl
    · apply heq_of_eq
      exact a9Ambient_forward_factorization hY
        ⟨A0, B0, X, hinduces⟩ hX
  right_inv := a9Ambient_forward_inverse_carrier hY

/-- The actual fixed-final equation is retained by the inverse map, while the
section and extension factors reconstruct its original `X`. -/
theorem a9AmbientInverse_factorization
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (c : A9AmbientSectionExtensionCarrier A B Y i j) :
    a9AmbientFinalMap A B (a9AmbientInverse hY c).1.A0
        (a9AmbientInverse hY c).1.B0
        (a9AmbientInverse hY c).1.X = Y := by
  exact (a9AmbientInverse hY c).1.induces

/-- Every section/extension carrier has the inverse map as its first inverse
law. -/
theorem a9Ambient_left_inverse_law
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientFixedFinalFiber V W A B Y i j k) :
    a9AmbientInverse hY (a9AmbientForward hY x) = x := by
  exact (a9AmbientFiberEquiv hY).left_inv x

/-- Every section/extension carrier is recovered after inverse then forward.
The extensional content is stated separately for direct A9 auditing. -/
theorem a9Ambient_right_inverse_law
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (c : A9AmbientSectionExtensionCarrier A B Y i j) :
    a9AmbientForward hY (a9AmbientInverse hY c) = c :=
  (a9AmbientFiberEquiv hY).right_inv c

/-- On a datum satisfying the fixed-final equation, the A8 side conditions
are equivalent to preservation of rank by quotient-after-restriction. -/
theorem a9Ambient_B_side_iff_restriction_range
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j : Nat} (x : A9AmbientInitialDatum V W A B Y i j) :
    B ⊔ a9AmbientKernelInW x = x.B0.1 ↔
      LinearMap.range (x.X.comp (a9AmbientBIncl B x.B0)) =
        LinearMap.range x.X := by
  classical
  let g := x.X.comp (a9AmbientBIncl B x.B0)
  constructor
  · intro hB
    apply le_antisymm (LinearMap.range_comp_le_range _ _)
    intro z hz
    rcases LinearMap.mem_range.mp hz with ⟨w, rfl⟩
    have hw : (x.B0.1.subtype w) ∈ B ⊔ a9AmbientKernelInW x := by
      rw [hB]
      exact w.property
    rcases Submodule.mem_sup.mp hw with ⟨b, hb, z, hz, hsum⟩
    rcases hz with ⟨u, hu, rfl⟩
    let b0 : x.B0.1 := ⟨b, x.B0.2.1 hb⟩
    let bu : x.B0.1 := u
    have hdecomp : b0 + bu = w := by
      apply Subtype.ext
      exact hsum
    have hvalue : x.X w = g ⟨b, hb⟩ := by
      change x.X w = x.X (a9AmbientBIncl B x.B0 ⟨b, hb⟩)
      rw [← hdecomp, map_add, LinearMap.mem_ker.mp hu]
      change x.X b0 + 0 = x.X b0
      exact add_zero _
    exact LinearMap.mem_range.mpr ⟨⟨b, hb⟩, hvalue.symm⟩
  · intro hrange
    apply le_antisymm
    · exact sup_le x.B0.2.1 (Submodule.map_subtype_le x.B0.1 (LinearMap.ker x.X))
    · intro w hw
      have hx : x.X ⟨w, hw⟩ ∈ LinearMap.range x.X :=
        LinearMap.mem_range_self x.X ⟨w, hw⟩
      rw [← hrange] at hx
      rcases LinearMap.mem_range.mp hx with ⟨b, hb⟩
      let d : x.B0.1 := ⟨w, hw⟩ - a9AmbientBIncl B x.B0 b
      have hdker : d ∈ LinearMap.ker x.X := by
        apply LinearMap.mem_ker.mpr
        have heq : x.X ⟨w, hw⟩ = x.X (a9AmbientBIncl B x.B0 b) := by
          simpa [g] using hb.symm
        simpa [d, map_sub, heq]
      have hsplit : (w : W) =
          B.subtype b + x.B0.1.subtype d := by
        change w = (b : W) + (w - (b : W))
        abel
      apply Submodule.mem_sup.mpr
      refine ⟨B.subtype b, b.property, x.B0.1.subtype d,
        ⟨d, hdker, rfl⟩, hsplit.symm⟩

/-- The first A8 equality says exactly that the quotient map is injective on
the actual lifted image `range X`. -/
theorem a9Ambient_A_side_iff_quotient_injective
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j : Nat} (x : A9AmbientInitialDatum V W A B Y i j) :
    A ⊓ a9AmbientImageLift x = x.A0.1 ↔
      Function.Injective
        ((a9AmbientQuotientMap A x.A0).domRestrict (LinearMap.range x.X)) := by
  classical
  let q := a9AmbientQuotientMap A x.A0
  have hkerq : LinearMap.ker q = A.map x.A0.1.mkQ := by
    ext z
    obtain ⟨v, rfl⟩ := x.A0.1.mkQ_surjective z
    change A.mkQ v = 0 ↔ ∃ w, w ∈ A ∧ x.A0.1.mkQ w = x.A0.1.mkQ v
    constructor
    · intro hv
      exact ⟨v, (Submodule.Quotient.mk_eq_zero A).mp hv, rfl⟩
    · rintro ⟨w, hw, heq⟩
      have h := congrArg q heq
      change A.mkQ w = A.mkQ v at h
      exact h.symm.trans ((Submodule.Quotient.mk_eq_zero A).mpr hw)
  constructor
  · intro hA
    intro u v huv
    apply Subtype.ext
    have hd : (u : V ⧸ x.A0.1) - v ∈ LinearMap.range x.X :=
      Submodule.sub_mem _ u.2 v.2
    have hqzero : q ((u : V ⧸ x.A0.1) - v) = 0 := by
      change q (u : V ⧸ x.A0.1) = q (v : V ⧸ x.A0.1) at huv
      simp [map_sub, huv]
    have hker : ((u : V ⧸ x.A0.1) - v) ∈ A.map x.A0.1.mkQ := by
      rw [← hkerq, LinearMap.mem_ker]
      exact hqzero
    rcases hker with ⟨a, ha, hqa⟩
    have haLift : a ∈ a9AmbientImageLift x := by
      change x.A0.1.mkQ a ∈ LinearMap.range x.X
      rw [hqa]
      exact hd
    have haA0 : a ∈ x.A0.1 := by
      have : a ∈ A ⊓ a9AmbientImageLift x := ⟨ha, haLift⟩
      rw [hA] at this
      exact this
    have hqa0 : x.A0.1.mkQ a = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 haA0
    have hdiff : (u : V ⧸ x.A0.1) - v = 0 := hqa.symm.trans hqa0
    exact sub_eq_zero.mp hdiff
  · intro hqinj
    apply le_antisymm
    · intro v hv
      have hqv : q (x.A0.1.mkQ v) = 0 := by
        exact (Submodule.Quotient.mk_eq_zero A).mpr hv.1
      have hvRange : x.A0.1.mkQ v ∈ LinearMap.range x.X := by
        exact hv.2
      have hzero := @hqinj ⟨x.A0.1.mkQ v, hvRange⟩ 0 (by simpa using hqv)
      have hvA0 : x.A0.1.mkQ v = 0 := congrArg Subtype.val hzero
      exact (Submodule.Quotient.mk_eq_zero _).mp hvA0
    · exact le_inf x.A0.2.1 (by
        intro v hv
        change x.A0.1.mkQ v ∈ LinearMap.range x.X
        have hzero : x.A0.1.mkQ v = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 hv
        rw [hzero]
        exact (LinearMap.range x.X).zero_mem)

/-- Rank preservation is equivalent to the two A8 incidence equalities. -/
theorem a9Ambient_A8_sideConditions_iff_rank_preservation
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j : Nat} (x : A9AmbientInitialDatum V W A B Y i j) :
    a9AmbientA8SideConditions x ↔
      Module.finrank F (LinearMap.range Y) =
        Module.finrank F (LinearMap.range x.X) := by
  classical
  let q := a9AmbientQuotientMap A x.A0
  let g := x.X.comp (a9AmbientBIncl B x.B0)
  have hqg : q.comp g = Y := by
    simpa [q, g, a9AmbientFinalMap] using x.induces
  constructor
  · rintro ⟨hA, hB⟩
    have hRange := (a9Ambient_B_side_iff_restriction_range x).mp hB
    have hInj := (a9Ambient_A_side_iff_quotient_injective x).mp hA
    have hInjG : Function.Injective (q.domRestrict (LinearMap.range g)) := by
      change Function.Injective ((a9AmbientQuotientMap A x.A0).domRestrict
        (LinearMap.range (x.X.comp (a9AmbientBIncl B x.B0))))
      rw [hRange]
      exact hInj
    have hcomp :
        LinearMap.range (q.comp g) = LinearMap.range
          (q.domRestrict (LinearMap.range g)) := by
      rw [← LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_rangeRestrict g)]
      congr 1
    rw [hqg] at hcomp
    calc
      Module.finrank F (LinearMap.range Y) =
          Module.finrank F (LinearMap.range
            (q.domRestrict (LinearMap.range g))) :=
        congrArg (fun U : Submodule F (V ⧸ A) => Module.finrank F U) hcomp
      _ = Module.finrank F (LinearMap.range g) :=
        LinearMap.finrank_range_of_inj hInjG
      _ = Module.finrank F (LinearMap.range x.X) :=
        congrArg (fun U : Submodule F (V ⧸ x.A0.1) => Module.finrank F U) hRange
  · intro hrank
    have hYle : Module.finrank F (LinearMap.range Y) ≤
        Module.finrank F (LinearMap.range g) := by
      let rG := g.rangeRestrict
      let qR := q.domRestrict (LinearMap.range g)
      have hcomp : qR.comp rG = q.comp g := by
        ext b
        rfl
      have hle : Module.finrank F (LinearMap.range (q.comp g)) ≤
          Module.finrank F (LinearMap.range g) := by
        rw [← hcomp, LinearMap.range_comp_of_range_eq_top _
          (LinearMap.range_rangeRestrict g)]
        exact qR.finrank_range_le
      exact (congrArg (fun f : B →ₗ[F] (V ⧸ A) =>
        Module.finrank F (LinearMap.range f)) hqg).symm.trans_le hle
    have hgX : LinearMap.range g ≤ LinearMap.range x.X :=
      LinearMap.range_comp_le_range _ _
    have hdimG : Module.finrank F (LinearMap.range g) =
        Module.finrank F (LinearMap.range x.X) := by
      apply le_antisymm
      · exact Submodule.finrank_mono hgX
      · rw [← hrank]
        exact hYle
    have hRange := Submodule.eq_of_le_of_finrank_eq hgX hdimG
    have hqR :
        LinearMap.range (q.domRestrict (LinearMap.range x.X)) =
          LinearMap.range Y := by
      calc
        LinearMap.range (q.domRestrict (LinearMap.range x.X)) =
            LinearMap.range (q.domRestrict (LinearMap.range g)) := by rw [hRange]
        _ = LinearMap.range ((q.domRestrict (LinearMap.range g)).comp g.rangeRestrict) :=
          (LinearMap.range_comp_of_range_eq_top _
            (LinearMap.range_rangeRestrict g)).symm
        _ = LinearMap.range Y := congrArg LinearMap.range hqg
    have hqInj : Function.Injective
        (q.domRestrict (LinearMap.range x.X)) := by
      have hkerdim : Module.finrank F
          (LinearMap.ker (q.domRestrict (LinearMap.range x.X))) = 0 := by
        have hnull := (q.domRestrict (LinearMap.range x.X)).finrank_range_add_finrank_ker
        rw [hqR, hrank] at hnull
        omega
      exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hkerdim)
    exact ⟨(a9Ambient_A_side_iff_quotient_injective x).mpr hqInj,
      (a9Ambient_B_side_iff_restriction_range x).mpr hRange⟩

/-- The A8 conditions hold for every member of the actual fixed-final
fiber: equal rank of `X` and `Y` forces both selector equalities. -/
theorem a9Ambient_fiber_A8_sideConditions
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup W] [Module F W] [Module.Finite F W]
    {A : Submodule F V} {B : Submodule F W} {Y : B →ₗ[F] (V ⧸ A)}
    {i j k : Nat} (hY : Module.finrank F (LinearMap.range Y) = k)
    (x : A9AmbientFixedFinalFiber V W A B Y i j k) :
    a9AmbientA8SideConditions x.1 := by
  exact (a9Ambient_A8_sideConditions_iff_rank_preservation x.1).2
    (by rw [hY, x.2])

/-- Every affine section fiber has `2^(k(a-i))` elements.  Translation is
by one lift of the canonical inclusion; its difference factors uniquely
through the kernel of the canonical quotient. -/
theorem a9Ambient_section_fiber_card
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [Fintype V] [AddCommGroup W] [Module F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {i k a : Nat} (hA : Module.finrank F A = a)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (A0 : A9AmbientA0 V A i)
    (hi : i ≤ a) :
    Fintype.card (A9AmbientSectionLift A B Y A0) = 2 ^ (k * (a - i)) := by
  classical
  let q := a9AmbientQuotientMap A A0
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨v, rfl⟩ := A.mkQ_surjective z
    exact ⟨A0.1.mkQ v, rfl⟩
  let r := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqsurj)
  let ell0 : LinearMap.range Y →ₗ[F] (V ⧸ A0.1) :=
    r.choose.comp (LinearMap.range Y).subtype
  have hell0 : q.comp ell0 = (LinearMap.range Y).subtype := by
    ext s
    exact congrArg (fun f : (V ⧸ A) →ₗ[F] (V ⧸ A) => f (s : V ⧸ A)) r.choose_spec
  let K := LinearMap.ker q
  letI : Module.Free F (LinearMap.range Y) :=
    Module.Free.of_basis (Module.finBasis F (LinearMap.range Y))
  letI : Module.Free F K := Module.Free.of_basis (Module.finBasis F K)
  let e : A9AmbientSectionLift A B Y A0 ≃
      (LinearMap.range Y →ₗ[F] K) :=
    a9AmbientSectionTranslationEquiv q (LinearMap.range Y) ell0 hell0
  rw [Fintype.card_congr e]
  rw [Module.card_eq_pow_finrank (K := F)
    (V := LinearMap.range Y →ₗ[F] K), Module.finrank_linearMap, ZMod.card]
  have hK : Module.finrank F K = a - i := by
    change Module.finrank F (LinearMap.ker q) = a - i
    have hqrank := q.finrank_range_add_finrank_ker
    have hqrange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hqsurj
    rw [hqrange, finrank_top] at hqrank
    have hV0 := A0.1.finrank_quotient_add_finrank
    have hV := A.finrank_quotient_add_finrank
    rw [A0.2.2] at hV0
    rw [hA] at hV
    omega
  rw [hY, hK]

/-- Every affine extension fiber has `2^(k(b-j))` elements.  The kernel of
restriction is canonically the space of maps out of the actual quotient
`B0/B`. -/
theorem a9Ambient_extension_fiber_card
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [Fintype V] [AddCommGroup W] [Module F W] [Module.Finite F W]
    [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {j k b : Nat} (hB : Module.finrank F (W ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (B0 : A9AmbientB0 W B j)
    (hj : j ≤ b) :
    Fintype.card (A9AmbientExtension A B Y B0) = 2 ^ (k * (b - j)) := by
  classical
  let P := B.comap B0.1.subtype
  let einc := Submodule.comapSubtypeEquivOfLe B0.2.1
  let y := Y.rangeRestrict.comp einc.toLinearMap
  obtain ⟨psi0, hpsi0P⟩ := LinearMap.exists_extend y
  have hpsi0 : psi0.comp (a9AmbientBIncl B B0) = Y.rangeRestrict := by
    apply LinearMap.ext
    intro b
    change psi0 (a9AmbientBIncl B B0 b) = Y.rangeRestrict b
    have hinc : a9AmbientBIncl B B0 b = P.subtype (einc.symm b) := by
      simp [a9AmbientBIncl, P, einc]
    rw [hinc]
    have h := congrFun (congrArg DFunLike.coe hpsi0P) (einc.symm b)
    change psi0 (P.subtype (einc.symm b)) =
      Y.rangeRestrict (einc (einc.symm b)) at h
    simpa only [einc.apply_symm_apply] using h
  let Q := B0.1 ⧸ P
  letI : Module.Free F (LinearMap.range Y) :=
    Module.Free.of_basis (Module.finBasis F (LinearMap.range Y))
  letI : Module.Free F Q := Module.Free.of_basis (Module.finBasis F Q)
  let e : A9AmbientExtension A B Y B0 ≃ (Q →ₗ[F] LinearMap.range Y) :=
    a9AmbientExtensionTranslationEquiv A B Y B0 psi0 hpsi0
  rw [Fintype.card_congr e]
  rw [Module.card_eq_pow_finrank (K := F)
    (V := Q →ₗ[F] LinearMap.range Y), Module.finrank_linearMap, ZMod.card]
  have hQ : Module.finrank F Q = b - j := by
    change Module.finrank F (B0.1 ⧸ P) = b - j
    have hsum := P.finrank_quotient_add_finrank
    have hP : Module.finrank F P = Module.finrank F B := einc.finrank_eq
    have hB0 := B0.1.finrank_quotient_add_finrank
    have hW := B.finrank_quotient_add_finrank
    rw [B0.2.2] at hB0
    rw [hB] at hW
    rw [hP] at hsum
    omega
  rw [hQ, hY]
  rw [Nat.mul_comm]

/-- Actual nested `B0` choices are subspaces of `W/B` of dimension `b-j`;
the final equality uses Gaussian symmetry, while the carrier itself keeps
the actual `B0` and its original variance. -/
noncomputable def a9AmbientNestedB0Equiv
    {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W]
    [Fintype W] (B : Submodule F W) {b j : Nat}
    (hB : Module.finrank F (W ⧸ B) = b) (hj : j ≤ b) :
    A9AmbientB0 W B j ≃ W6Grass (W ⧸ B) (b - j) where
  toFun B0 := by
    let U := B0.1.map B.mkQ
    refine ⟨U, ?_⟩
    have hdim : Module.finrank F U = b - j := by
      have hmap : Module.finrank F U + Module.finrank F B =
          Module.finrank F B0.1 := by
        have h := (B.mkQ.domRestrict B0.1).finrank_range_add_finrank_ker
        have hker : LinearMap.ker (B.mkQ.domRestrict B0.1) =
            B.comap B0.1.subtype := by
          ext x
          simp
        rw [LinearMap.range_domRestrict, hker] at h
        rw [(Submodule.comapSubtypeEquivOfLe B0.2.1).finrank_eq] at h
        exact h
      have hB0dim := B0.1.finrank_quotient_add_finrank
      rw [B0.2.2] at hB0dim
      have hBdim := B.finrank_quotient_add_finrank
      rw [hB] at hBdim
      omega
    exact hdim
  invFun U := by
    let B0 := U.1.comap B.mkQ
    refine ⟨B0, ?_, ?_⟩
    · exact Submodule.le_comap_mkQ B U.1
    · have hdim : Module.finrank F B0 =
          Module.finrank F U.1 + Module.finrank F B := by
        have hmap : B0.map B.mkQ = U.1 :=
          Submodule.map_comap_eq_self (by simp)
        have h := (B.mkQ.domRestrict B0).finrank_range_add_finrank_ker
        have hker : LinearMap.ker (B.mkQ.domRestrict B0) =
            B.comap B0.subtype := by
          ext x
          simp
        rw [LinearMap.range_domRestrict, hker, hmap] at h
        rw [(Submodule.comapSubtypeEquivOfLe
          (Submodule.le_comap_mkQ B U.1)).finrank_eq] at h
        exact h.symm
      have hW := B0.finrank_quotient_add_finrank
      have hBdim := B.finrank_quotient_add_finrank
      rw [hB] at hBdim
      rw [U.2] at hdim
      omega
  left_inv B0 := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_self (by simpa using B0.2.1)
  right_inv U := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

/-- Gaussian symmetry for the cardinality of subspaces.  The annihilator is
used here only to prove equality of the two numerical Grassmann counts; it is
not used to identify `B0/B` with a dual space or to define an A9 map. -/
theorem a9Ambient_w6Gaussian_symm (b j : Nat) (hj : j ≤ b) :
    w6Gaussian b (b - j) = w6Gaussian b j := by
  classical
  let E := Fin b → F
  letI : Module.Finite F E := Module.Finite.pi
  letI : Module.Free F E := Module.Free.of_basis (Pi.basisFun F _)
  letI : Module.Free F (Module.Dual F E) :=
    Module.Free.of_basis (Module.finBasis F (Module.Dual F E))
  have hdim : Module.finrank F E = b := by simp [E, F]
  have hdual : Module.finrank F (Module.Dual F E) = b := by
    rw [Subspace.dual_finrank_eq, hdim]
  have hcard1 := w6_card_grass (E := E) j
  have hcard2 := w6_card_grass (E := Module.Dual F E) (b - j)
  rw [hdim] at hcard1
  rw [hdual] at hcard2
  have hannihilatorCount :
      Fintype.card (W6Grass E j) =
        Fintype.card (W6Grass (Module.Dual F E) (b - j)) := by
    classical
    let f : W6Grass E j → W6Grass (Module.Dual F E) (b - j) := fun U =>
      ⟨U.1.dualAnnihilator, by
        have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U.1
        change Module.finrank F U.1 + Module.finrank F U.1.dualAnnihilator =
          Module.finrank F E at h
        change Module.finrank F U.1.dualAnnihilator = b - j
        rw [U.2, hdim] at h
        omega⟩
    have hf : Function.Injective f := by
      intro U V h
      have hU := congrArg Subtype.val h
      exact Subtype.ext ((Subspace.dualAnnihilator_inj).mp hU)
    have hsurj : Function.Surjective f := by
      intro U
      have hdimU : Module.finrank F U.1 = b - j := U.2
      let P := U.1.dualCoannihilator
      have hP : Module.finrank F P = j := by
        have h := Subspace.finrank_add_finrank_dualCoannihilator_eq U.1
        change Module.finrank F U.1 + Module.finrank F P = Module.finrank F E at h
        rw [hdimU, hdim] at h
        omega
      refine ⟨⟨P, hP⟩, ?_⟩
      apply Subtype.ext
      exact Subspace.dualCoannihilator_dualAnnihilator_eq
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
  calc
    w6Gaussian b (b - j) =
        Fintype.card (W6Grass (Module.Dual F E) (b - j)) := hcard2.symm
    _ = Fintype.card (W6Grass E j) := hannihilatorCount.symm
    _ = w6Gaussian b j := hcard1

/-- Count the actual nested `B0` carrier by quotienting by fixed `B`, then
apply the scalar Gaussian symmetry `[{b \atop b-j}]_2=[{b \atop j}]_2`. -/
theorem a9Ambient_nested_B0_card
    {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W]
    [Module.Free F W] [Fintype W]
    (B : Submodule F W) {b j : Nat}
    (hB : Module.finrank F (W ⧸ B) = b) (hj : j ≤ b) :
    Fintype.card (A9AmbientB0 W B j) = w6Gaussian b j := by
  letI : Module.Free F (W ⧸ B) := Module.Free.of_basis (Module.finBasis F _)
  rw [Fintype.card_congr (a9AmbientNestedB0Equiv B hB hj),
    w6_card_grass, hB, a9Ambient_w6Gaussian_symm b j hj]

/-- Cardinality of a full finite linear-map space over `F_2`. -/
theorem a9Ambient_linearMap_card
    {P Q : Type*} [AddCommGroup P] [Module F P] [Module.Free F P]
    [Module.Finite F P] [Fintype P]
    [AddCommGroup Q] [Module F Q] [Module.Free F Q]
    [Module.Finite F Q] [Fintype Q] (m n : Nat)
    (hP : Module.finrank F P = m) (hQ : Module.finrank F Q = n) :
    Fintype.card (P →ₗ[F] Q) = 2 ^ (m * n) := by
  rw [Module.card_eq_pow_finrank (K := F) (V := P →ₗ[F] Q),
    Module.finrank_linearMap, ZMod.card, hP, hQ]

/-- Exact actual ambient fixed-final cardinality, including both affine
fibers and the actual nested `B0` count. -/
theorem a9_ambient_fiber_card
    {V W : Type*} [AddCommGroup V] [Module F V] [Module.Free F V]
    [Module.Finite F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Module.Free F W]
    [Module.Finite F W] [Fintype W]
    (A : Submodule F V) (B : Submodule F W) (Y : B →ₗ[F] (V ⧸ A))
    {i j k a b : Nat} (hA : Module.finrank F A = a)
    (hB : Module.finrank F (W ⧸ B) = b)
    (hY : Module.finrank F (LinearMap.range Y) = k)
    (hi : i ≤ a) (hj : j ≤ b) :
    Fintype.card (A9AmbientFixedFinalFiber V W A B Y i j k) =
      w6Gaussian a i * w6Gaussian b j *
        2 ^ (k * (a - i)) * 2 ^ (k * (b - j)) := by
  classical
  letI : Module.Free F A := Module.Free.of_basis (Module.finBasis F A)
  letI : Module.Free F (W ⧸ B) := Module.Free.of_basis (Module.finBasis F _)
  rw [Fintype.card_congr (a9AmbientFiberEquiv hY)]
  unfold A9AmbientSectionExtensionCarrier
  rw [Fintype.card_eq_nat_card]
  simp_rw [Nat.card_sigma, Nat.card_prod, ← Fintype.card_eq_nat_card]
  simp_rw [
    a9Ambient_section_fiber_card A B Y hA hY _ hi,
    a9Ambient_extension_fiber_card A B Y hB hY _ hj]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_congr (a9AmbientA0Equiv A i),
    a9Ambient_nested_B0_card B hB hj,
    w6_card_grass, hA]
  ring
  simp only [Nat.cast_id]

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber
