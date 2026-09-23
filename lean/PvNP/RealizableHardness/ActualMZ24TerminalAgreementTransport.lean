import PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
import PvNP.RealizableHardness.ActualMZ24ComplementRestriction
import PvNP.RealizableHardness.ActualFiniteLaw
import Mathlib.Tactic

/-! Exact same-table transport of decoded-pair agreement to a containing
terminal ambient.  This is B2a only: it makes no retained-bucket or
positive-residual extraction claim. -/

namespace PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat}

/-- Lift a Grassmann point in a submodule to the original ambient. -/
def liftQuery (E : Submodule (ZMod 2) V) (L : Grass E d) : Grass V d :=
  ⟨L.val.map E.subtype, by
    rw [Submodule.finrank_map_subtype_eq]
    exact L.property⟩

def liftQueryMap (E : Submodule (ZMod 2) V) (L : Grass E d) :
    L.val →ₗ[ZMod 2] (liftQuery E L).val :=
  (Submodule.equivMapOfInjective E.subtype E.injective_subtype L.val).toLinearMap

theorem liftQuery_map_apply (E : Submodule (ZMod 2) V) (L : Grass E d)
    (x : L.val) :
    ((liftQueryMap E L) x : V) = E.subtype x := rfl

theorem restrict_liftQuery (E : Submodule (ZMod 2) V) (L : Grass E d) :
    restrictToAmbient E (liftQuery E L).val (by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact y.property) = L.val := by
  apply Submodule.ext
  intro x
  change E.subtype x ∈ L.val.map E.subtype ↔ x ∈ L.val
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hval : E.subtype y = E.subtype x := hxy
    have : y = x := E.injective_subtype hval
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem lift_restrictGrass (E : Submodule (ZMod 2) V) (L : Grass V d)
    (hLE : L.val ≤ E) : liftQuery E (restrictGrass E L hLE) = L := by
  apply Subtype.ext
  exact restrictGrass_map_recovery E L hLE

def localGrass (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (hQE : Q.val ≤ E) : Grass E a :=
  restrictGrass E Q hQE

def localDecodedPair (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E) :
    DecodedPair (localGrass E Q hQE) d :=
  { W := restrictToAmbient E P.W hWE
    hQW := restrictToAmbient_mono E Q.val P.W hQE hWE P.hQW
    g := P.g.comp (Submodule.comapSubtypeEquivOfLe hWE).toLinearMap }

def restrictedTable
    (E : Submodule (ZMod 2) V)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val) :
    (L : Grass E d) → Module.Dual (ZMod 2) L.val :=
  fun L => (T (liftQuery E L)).comp (liftQueryMap E L)

theorem restrictedTable_apply
    (E : Submodule (ZMod 2) V)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (L : Grass E d) (x : L.val) :
    restrictedTable E T L x = T (liftQuery E L) (liftQueryMap E L x) := rfl

noncomputable def zoomRestrictionEquiv
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E) :
    Zoom Q P ≃ Zoom (localGrass E Q hQE)
      (localDecodedPair E Q P hQE hWE) := by
  classical
  let Qe := localGrass E Q hQE
  let Pe := localDecodedPair E Q P hQE hWE
  refine
    { toFun := fun z =>
        let hLE : z.1.val ≤ E := z.2.2.trans hWE
        ⟨restrictGrass E z.1 hLE,
          ⟨restrictToAmbient_mono E Q.val z.1.val hQE hLE z.2.1,
            restrictToAmbient_mono E z.1.val P.W hLE hWE z.2.2⟩⟩
      invFun := fun z =>
        ⟨liftQuery E z.1,
          ⟨by
            have hrec := restrictGrass_map_recovery E Q hQE
            change Q.val ≤ z.1.val.map E.subtype
            rw [← hrec]
            exact Submodule.map_mono z.2.1,
           by
            have hrec := restrictToAmbient_map_recovery E P.W hWE
            change z.1.val.map E.subtype ≤ P.W
            rw [← hrec]
            exact Submodule.map_mono z.2.2⟩⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact lift_restrictGrass E z.1 (z.2.2.trans hWE)
      right_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact restrict_liftQuery E z.1 }

theorem zoomRestrictionEquiv_apply_val
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E)
    (z : Zoom Q P) :
    (zoomRestrictionEquiv E Q P hQE hWE z).1 =
      restrictGrass E z.1 (z.2.2.trans hWE) := rfl

private theorem restrictedTable_eval_cast
    (E : Submodule (ZMod 2) V)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (L : Grass E d) (L₀ : Grass V d) (hL : liftQuery E L = L₀)
    (x : L.val) :
    restrictedTable E T L x = T L₀ (hL ▸ liftQueryMap E L x) := by
  cases hL
  rfl

private theorem liftQueryMap_cast_coe
    (E : Submodule (ZMod 2) V) (L : Grass E d) (L₀ : Grass V d)
    (hL : liftQuery E L = L₀) (x : L.val) :
    ((hL ▸ liftQueryMap E L x : L₀.val) : V) = E.subtype x := by
  cases hL
  rfl

theorem agreesOn_iff_restricted
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E)
    (z : Zoom Q P) :
    AgreesOn (T := T) z.1 z.2.2 ↔
      AgreesOn (T := restrictedTable E T)
        (zoomRestrictionEquiv E Q P hQE hWE z).1
        (zoomRestrictionEquiv E Q P hQE hWE z).2.2 := by
  let Lₑ := restrictGrass E z.1 (z.2.2.trans hWE)
  let Pe := localDecodedPair E Q P hQE hWE
  have hL : liftQuery E Lₑ = z.1 := lift_restrictGrass E z.1 (z.2.2.trans hWE)
  constructor
  · intro hz x
    let x₀ : z.1.val := ⟨E.subtype x, x.property⟩
    let xPe : Pe.W := ⟨x, (zoomRestrictionEquiv E Q P hQE hWE z).2.2 x.property⟩
    let y : P.W := ⟨x₀, z.2.2 x₀.property⟩
    have hCast : hL ▸ liftQueryMap E Lₑ x = x₀ := by
      apply Subtype.ext
      exact liftQueryMap_cast_coe E Lₑ z.1 hL x
    have hTable : restrictedTable E T Lₑ x = T z.1 x₀ := by
      rw [restrictedTable_eval_cast E T Lₑ z.1 hL x, hCast]
    have hPair : Pe.g xPe = P.g y := by
      change P.g ((Submodule.comapSubtypeEquivOfLe hWE).toLinearMap xPe) = P.g y
      congr 1
    have hx := hz x₀
    calc
      restrictedTable E T Lₑ x = T z.1 x₀ := hTable
      _ = P.g y := hx
      _ = Pe.g xPe := hPair.symm
  · intro hz x
    have hxE : x.1 ∈ E := (z.2.2.trans hWE) x.property
    let xₑ : Lₑ.val := ⟨⟨x.1, hxE⟩, x.property⟩
    let xPe : Pe.W := ⟨xₑ, (zoomRestrictionEquiv E Q P hQE hWE z).2.2 xₑ.property⟩
    let y : P.W := ⟨x, z.2.2 x.property⟩
    have hCast : hL ▸ liftQueryMap E Lₑ xₑ = x := by
      apply Subtype.ext
      calc
        ((hL ▸ liftQueryMap E Lₑ xₑ : z.1.val) : V) = E.subtype xₑ.1 :=
          liftQueryMap_cast_coe E Lₑ z.1 hL xₑ
        _ = x.1 := rfl
    have hTable : restrictedTable E T Lₑ xₑ = T z.1 x := by
      rw [restrictedTable_eval_cast E T Lₑ z.1 hL xₑ, hCast]
    have hPair : Pe.g xPe = P.g y := by
      change P.g ((Submodule.comapSubtypeEquivOfLe hWE).toLinearMap xPe) = P.g y
      congr 1
    have hx := hz xₑ
    calc
      T z.1 x = restrictedTable E T Lₑ xₑ := hTable.symm
      _ = Pe.g xPe := hx
      _ = P.g y := hPair

noncomputable def agreeingZoomRestrictionEquiv
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E) :
    AgreeingZoom T Q P ≃
      AgreeingZoom (restrictedTable E T) (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE) := by
  let e := zoomRestrictionEquiv E Q P hQE hWE
  exact
    { toFun := fun z => ⟨e z.1, (agreesOn_iff_restricted E Q T P hQE hWE z.1).mp z.2⟩
      invFun := fun z => ⟨e.symm z.1, (agreesOn_iff_restricted E Q T P hQE hWE
        (e.symm z.1)).mpr (by
          let localAgrees : Zoom (localGrass E Q hQE)
              (localDecodedPair E Q P hQE hWE) → Prop :=
            fun w => AgreesOn (T := restrictedTable E T) w.1 w.2.2
          have hp : localAgrees (e (e.symm z.1)) :=
            (e.apply_symm_apply z.1).symm ▸ z.2
          change localAgrees (e (e.symm z.1))
          exact hp)⟩
      left_inv := by intro z; apply Subtype.ext; exact e.symm_apply_apply z.1
      right_inv := by intro z; apply Subtype.ext; exact e.apply_symm_apply z.1 }

theorem agreement_restrict_eq
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E) :
    agreement T Q P =
      agreement (restrictedTable E T) (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE) := by
  classical
  let ez := zoomRestrictionEquiv E Q P hQE hWE
  let ea := agreeingZoomRestrictionEquiv E Q T P hQE hWE
  have hden : Fintype.card (Zoom Q P) =
      Fintype.card (Zoom (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE)) := Fintype.card_congr ez
  have hnum : Fintype.card (AgreeingZoom T Q P) =
      Fintype.card (AgreeingZoom (restrictedTable E T) (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE)) := Fintype.card_congr ea
  by_cases hz : Fintype.card (Zoom Q P) = 0
  · have hz' : Fintype.card (Zoom (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE)) = 0 := by omega
    rw [agreement_eq_zero_of_empty T Q P hz,
      agreement_eq_zero_of_empty (restrictedTable E T) (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE) hz']
  · have hz' : Fintype.card (Zoom (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE)) ≠ 0 := by omega
    rw [agreement_eq_fraction_of_nonempty T Q P hz,
      agreement_eq_fraction_of_nonempty (restrictedTable E T) (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE) hz']
    rw [hnum, hden]

noncomputable instance localZoom_nonempty
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E)
    [Nonempty (Zoom Q P)] :
    Nonempty (Zoom (localGrass E Q hQE)
      (localDecodedPair E Q P hQE hWE)) :=
  ⟨zoomRestrictionEquiv E Q P hQE hWE (Classical.choice ‹Nonempty (Zoom Q P)›)⟩

theorem uniformLaw_zoomRestriction
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E)
    [Nonempty (Zoom Q P)] :
    pushforward (zoomRestrictionEquiv E Q P hQE hWE)
      (uniformLaw (Zoom Q P)) =
      uniformLaw (Zoom (localGrass E Q hQE)
        (localDecodedPair E Q P hQE hWE)) := by
  exact pushforward_uniformLaw_equiv (zoomRestrictionEquiv E Q P hQE hWE)

theorem agreement_le_complement
    (E : Submodule (ZMod 2) V) (Q : Grass V a)
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : DecodedPair Q d) (hQE : Q.val ≤ E) (hWE : P.W ≤ E)
    (C : AdviceComplement (localGrass E Q hQE)) (had : a ≤ d)
    (hb : a + (d - a) = d) :
    agreement T Q P ≤
      agreement
        (complementTable (restrictedTable E T) C had hb)
        (bottomGrass C.A)
        (complementPair C (localDecodedPair E Q P hQE hWE)) := by
  rw [agreement_restrict_eq E Q T P hQE hWE]
  exact complement_agreement_le (restrictedTable E T) C
    (localDecodedPair E Q P hQE hWE) had hb

end
end PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
