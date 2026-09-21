import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import PvNP.RealizableHardness.ActualCliqueCollisionTransfer
import PvNP.RealizableHardness.GrassmannCounting

namespace PvNP.RealizableHardness.ActualQuestionCenterDomainDraw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

local instance rowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

structure QuestionCenter {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (J t : Nat) where
  U : Finset I.RowId
  goodU : GoodQuestion I.support U
  card_U : U.card = J
  K : Submodule (ZMod 2) (I.GlobalVar -> ZMod 2)
  K_le : K <= coordinateSpace I.support U
  finrank_K : Module.finrank (ZMod 2) K = t
  transverse : K ⊓ equationSpan I.support U = ⊥

abbrev Ambient {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :=
  I.GlobalVar -> ZMod 2

def questionEquationSpan {N m J t : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) : Submodule (ZMod 2) (Ambient I) :=
  equationSpan I.support q.U

def questionCoordinateSpace {N m J t : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) : Submodule (ZMod 2) (Ambient I) :=
  coordinateSpace I.support q.U

def centerEquationSpan {N m J t : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) : Submodule (ZMod 2) (Ambient I) :=
  q.K ⊔ questionEquationSpan q

def centerSpanInCoordinate {N m J t : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
    Submodule (ZMod 2) (questionCoordinateSpace q) :=
  (centerEquationSpan q).comap (questionCoordinateSpace q).subtype

abbrev CenterQuotient {N m J t : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :=
  questionCoordinateSpace q ⧸ centerSpanInCoordinate q

def DomainDraw {N m J t : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) :=
  {D : Submodule (ZMod 2) (Ambient I) //
    D <= questionCoordinateSpace q ∧
    q.K <= D ∧
    questionEquationSpan q <= D ∧
    Module.finrank (ZMod 2) D = J + 2*h}

instance domainDrawFinite
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) : Finite (DomainDraw q h) := by
  let : Finite (Submodule (ZMod 2) (Ambient I)) := by
    exact Finite.of_injective (fun Q => (Q : Set (Ambient I)))
      SetLike.coe_injective
  exact Finite.of_injective (fun D : DomainDraw q h => D.1)
    (fun _ _ h => Subtype.ext h)

noncomputable instance domainDrawFintype
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) : Fintype (DomainDraw q h) :=
  Fintype.ofFinite _

noncomputable def coordinateSpaceLinearEquiv
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
    questionCoordinateSpace q ≃ₗ[ZMod 2]
      ((x : ↥(questionSupport I.support q.U)) -> ZMod 2) := by
  let S := questionSupport I.support q.U
  let f : questionCoordinateSpace q →ₗ[ZMod 2] ((x : ↥S) -> ZMod 2) :=
    { toFun := fun v x => v.1 x.1
      map_add' := by intro x y; funext z; simp
      map_smul' := by intro a x; funext z; simp }
  let g : ((x : ↥S) -> ZMod 2) →ₗ[ZMod 2] questionCoordinateSpace q :=
    { toFun := fun v =>
        ⟨fun x => if hx : x ∈ S then v ⟨x, hx⟩ else 0, by
          intro x hx
          change (if h : x ∈ S then v ⟨x, h⟩ else 0) = 0
          have hxS : x ∉ S := by simpa [S] using hx
          split
          · rename_i h
            exact (hxS h).elim
          · rfl⟩
      map_add' := by
        intro x y; apply Subtype.ext; funext z
        by_cases hz : z ∈ S <;> simp [hz]
      map_smul' := by
        intro a x; apply Subtype.ext; funext z
        by_cases hz : z ∈ S <;> simp [hz] }
  exact
    { toFun := f
      invFun := g
      map_add' := f.map_add
      map_smul' := f.map_smul
      left_inv := by
        intro v; apply Subtype.ext; funext x
        by_cases hx : x ∈ S
        · simp [f, g, hx]
        · simp [f, g, hx, v.2 x hx]
      right_inv := by
        intro v; funext x; simp [f, g] }

theorem questionSupport_card
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  (questionSupport I.support q.U).card = 3 * J := by
  classical
  rw [questionSupport, Finset.card_biUnion]
  · simp_rw [I.support_card]
    simp [q.card_U, Nat.mul_comm]
  · intro e he f hf hne
    exact q.goodU.1 he hf hne

theorem coordinateSpace_finrank
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  Module.finrank (ZMod 2) (questionCoordinateSpace q) = 3 * J := by
  rw [LinearEquiv.finrank_eq (coordinateSpaceLinearEquiv q)]
  simp [questionSupport_card q]

theorem equationSpan_finrank
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  Module.finrank (ZMod 2) (questionEquationSpan q) = J := by
  change Module.finrank (ZMod 2) (equationSpan I.support q.U) = J
  calc
    _ = q.U.card := equationSpan_finrank_eq_card I.support I.support_card q.U q.goodU
    _ = J := q.card_U

theorem centerEquationSpan_le_coordinateSpace
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  centerEquationSpan q <= questionCoordinateSpace q := by
  apply sup_le q.K_le
  apply Submodule.span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  exact equationVector_mem_coordinateSpace I.support q.U e he

theorem centerEquationSpan_finrank
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  Module.finrank (ZMod 2) (centerEquationSpan q) = t + J := by
  unfold centerEquationSpan
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := Ambient I) q.K (questionEquationSpan q)
  have htrans : q.K ⊓ questionEquationSpan q = ⊥ := q.transverse
  rw [htrans] at h
  simp only [finrank_bot, add_zero, q.finrank_K, equationSpan_finrank q] at h
  omega

theorem centerSpanInCoordinate_finrank
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  Module.finrank (ZMod 2) (centerSpanInCoordinate q) = t + J := by
  unfold centerSpanInCoordinate
  rw [(Submodule.comapSubtypeEquivOfLe
    (centerEquationSpan_le_coordinateSpace q)).finrank_eq]
  exact centerEquationSpan_finrank q

theorem centerQuotient_finrank
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
  Module.finrank (ZMod 2) (CenterQuotient q) = 2 * J - t := by
  have h := (centerSpanInCoordinate q).finrank_quotient_add_finrank
  rw [centerSpanInCoordinate_finrank q, coordinateSpace_finrank q] at h
  have h' := h
  simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h'
  have hct : Module.finrank (ZMod 2) (CenterQuotient q) + t = 2 * J := by
    simpa [Nat.add_comm, Nat.succ_mul] using h'
  exact Nat.eq_sub_of_add_eq hct

private theorem quotient_map_dimension
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Q L : Submodule (ZMod 2) V) (hQL : Q ≤ L) :
    Module.finrank (ZMod 2) (L.map Q.mkQ) + Module.finrank (ZMod 2) Q =
      Module.finrank (ZMod 2) L := by
  have h := (Q.mkQ.domRestrict L).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (Q.mkQ.domRestrict L) = Q.comap L.subtype := by
    ext x
    simp
  rw [LinearMap.range_domRestrict, hk] at h
  rw [(Submodule.comapSubtypeEquivOfLe hQL).finrank_eq] at h
  exact h

private def containingQuotientEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {a d : Nat} (Q : Grass V a) (had : a ≤ d) :
    {L : Grass V d // Q.val ≤ L.val} ≃ Grass (V ⧸ Q.val) (d - a) where
  toFun L := ⟨L.val.val.map Q.val.mkQ, by
    have h := quotient_map_dimension Q.val L.val.val L.property
    rw [Q.property, L.val.property] at h
    omega⟩
  invFun R := ⟨⟨R.val.comap Q.val.mkQ, by
      have h := quotient_map_dimension Q.val (R.val.comap Q.val.mkQ)
        (Submodule.le_comap_mkQ Q.val R.val)
      have hm : (R.val.comap Q.val.mkQ).map Q.val.mkQ = R.val :=
        Submodule.map_comap_eq_self (by simp)
      rw [hm, R.property, Q.property] at h
      omega⟩, Submodule.le_comap_mkQ Q.val R.val⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Submodule.comap_map_mkQ] using
      (sup_eq_right.mpr L.property : Q.val ⊔ L.val.val = L.val.val)
  right_inv R := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

private def coordinateContainingEquiv
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) :
    DomainDraw q h ≃
      {L : Grass (questionCoordinateSpace q) (J + 2*h) //
        centerSpanInCoordinate q ≤ L.val} where
  toFun D := ⟨⟨D.1.comap (questionCoordinateSpace q).subtype, by
      rw [(Submodule.comapSubtypeEquivOfLe D.2.1).finrank_eq, D.2.2.2.2]⟩, by
      intro z hz
      have hcenter : centerEquationSpan q ≤ D.1 :=
        sup_le D.2.2.1 D.2.2.2.1
      exact hcenter (show (z : Ambient I) ∈ centerEquationSpan q from hz)⟩
  invFun L := ⟨L.val.val.map (questionCoordinateSpace q).subtype, by
      exact (questionCoordinateSpace q).map_subtype_le L.val.val,
      by
        intro x hx
        let z : questionCoordinateSpace q := ⟨x, q.K_le hx⟩
        have hz : z ∈ centerSpanInCoordinate q := by
          exact (show (z : Ambient I) ∈ centerEquationSpan q from
            (le_sup_left : q.K ≤ centerEquationSpan q) hx)
        have hzL : z ∈ L.val.val := L.property hz
        exact ⟨z, ⟨hzL, rfl⟩⟩,
      by
        intro x hx
        have hEqCoord : questionEquationSpan q ≤ questionCoordinateSpace q := by
          apply Submodule.span_le.mpr
          rintro _ ⟨e, he, rfl⟩
          exact equationVector_mem_coordinateSpace I.support q.U e he
        have hcoord : x ∈ questionCoordinateSpace q := hEqCoord hx
        let z : questionCoordinateSpace q := ⟨x, hcoord⟩
        have hz : z ∈ centerSpanInCoordinate q := by
          exact (show (z : Ambient I) ∈ centerEquationSpan q from
            (le_sup_right : questionEquationSpan q ≤ centerEquationSpan q) hx)
        have hzL : z ∈ L.val.val := L.property hz
        exact ⟨z, ⟨hzL, rfl⟩⟩,
      by
        rw [Submodule.finrank_map_subtype_eq, L.val.property]⟩
  left_inv D := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by
      intro x hx
      exact ⟨⟨x, D.2.1 hx⟩, rfl⟩)
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective
      (questionCoordinateSpace q).injective_subtype L.val.val

noncomputable def domainDrawEquiv
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
  DomainDraw q h ≃ Grass (CenterQuotient q) (2*h - t) := by
  letI : Finite (CenterQuotient q) :=
    Finite.of_surjective (centerSpanInCoordinate q).mkQ
      (centerSpanInCoordinate q).mkQ_surjective
  have hd : J + 2*h - (t + J) = 2*h - t := by omega
  exact (coordinateContainingEquiv q).trans
    ((containingQuotientEquiv
      (V := questionCoordinateSpace q) (a := t + J) (d := J + 2*h)
      ⟨centerSpanInCoordinate q, centerSpanInCoordinate_finrank q⟩
      (by omega)).trans (Equiv.cast (by rw [hd])))

private theorem grassNonempty_of_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {a : Nat} (ha : a ≤ Module.finrank (ZMod 2) V) :
  Nonempty (Grass V a) := by
  let b := Module.finBasis (ZMod 2) V
  let e : Fin a → Fin (Module.finrank (ZMod 2) V) :=
    fun i => ⟨i.1, lt_of_lt_of_le i.2 ha⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun x => x.val) hij)
  let v : Fin a → V := fun i => b (e i)
  let S : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range v)
  have hi : LinearIndependent (ZMod 2) v := b.linearIndependent.comp e he
  have hr : Module.finrank (ZMod 2) S = a := by
    unfold S
    simpa using finrank_span_eq_card hi
  exact ⟨⟨S, hr⟩⟩

theorem domainDraw_card
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
  Fintype.card (DomainDraw q h) = gaussian (2*J - t) (2*h - t) := by
  letI : Finite (CenterQuotient q) :=
    Finite.of_surjective (centerSpanInCoordinate q).mkQ
      (centerSpanInCoordinate q).mkQ_surjective
  rw [Fintype.card_congr (domainDrawEquiv q h ht hh), card_grass]
  rw [centerQuotient_finrank q]

theorem domainDraw_nonempty
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
  Nonempty (DomainDraw q h) := by
  letI : Finite (CenterQuotient q) :=
    Finite.of_surjective (centerSpanInCoordinate q).mkQ
      (centerSpanInCoordinate q).mkQ_surjective
  letI : Finite (Grass (CenterQuotient q) (2*h - t)) := inferInstance
  let R : Grass (CenterQuotient q) (2*h - t) :=
    Classical.choice (grassNonempty_of_le (V := CenterQuotient q) (by
      rw [centerQuotient_finrank q]
      apply Nat.sub_le_sub_right
      omega))
  exact ⟨(domainDrawEquiv q h ht hh).symm R⟩

private noncomputable def drawAmbientCenter
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    Submodule (ZMod 2) D.1 :=
  (centerEquationSpan q).comap D.1.subtype

private theorem drawAmbientCenter_le_top
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    drawAmbientCenter q D ≤ (⊤ : Submodule (ZMod 2) D.1) := le_top

private noncomputable def drawComplement
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    Submodule (ZMod 2) D.1 :=
  Classical.choose (Submodule.exists_isCompl (drawAmbientCenter q D))

private theorem drawComplement_spec
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    IsCompl (drawAmbientCenter q D) (drawComplement q D) :=
  Classical.choose_spec (Submodule.exists_isCompl (drawAmbientCenter q D))

private noncomputable def drawIncrement
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    Submodule (ZMod 2) (Ambient I) :=
  q.K ⊔ (drawComplement q D).map D.1.subtype

private theorem drawCenter_le_domain
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    centerEquationSpan q ≤ D.1 := by
  exact sup_le D.2.2.1 D.2.2.2.1

private theorem drawIncrement_le_domain
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    drawIncrement q D ≤ D.1 := by
  apply sup_le D.2.2.1
  exact D.1.map_subtype_le (drawComplement q D)

private theorem drawAmbientCenter_finrank
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    Module.finrank (ZMod 2) (drawAmbientCenter q D) = t + J := by
  unfold drawAmbientCenter
  rw [(Submodule.comapSubtypeEquivOfLe
    (drawCenter_le_domain q D)).finrank_eq]
  exact centerEquationSpan_finrank q

private theorem drawComplement_finrank
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    Module.finrank (ZMod 2) (drawComplement q D) = 2*h - t := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := D.1)
    (drawAmbientCenter q D) (drawComplement q D)
  have hc := drawComplement_spec q D
  rw [hc.codisjoint.eq_top, finrank_top (ZMod 2) D.1,
    hc.disjoint.eq_bot, finrank_bot (ZMod 2) D.1, add_zero,
    drawAmbientCenter_finrank q D, D.2.2.2.2] at hs
  have h' := hs
  simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h'
  have hct : Module.finrank (ZMod 2) (drawComplement q D) + t = 2*h := by
    omega
  exact Nat.eq_sub_of_add_eq hct

private theorem drawIncrement_inf_equation_bot
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
  drawIncrement q D ⊓ questionEquationSpan q = ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_sup.mp hx.1 with ⟨k, hk, c, hc, rfl⟩
    rcases Submodule.mem_map.mp hc with ⟨c', hc', rfl⟩
    have hxE : k + (D.1.subtype c' : Ambient I) ∈ questionEquationSpan q := by
      have hxE' := hx.2
      change k + (D.1.subtype c' : Ambient I) ∈ questionEquationSpan q at hxE'
      exact hxE'
    have hkC : k + (c' : Ambient I) ∈ centerEquationSpan q :=
      (le_sup_right : questionEquationSpan q ≤ centerEquationSpan q) hxE
    have hkA : k ∈ centerEquationSpan q :=
      (le_sup_left : q.K ≤ centerEquationSpan q) hk
    have hcA : (D.1.subtype c' : Ambient I) ∈ centerEquationSpan q := by
      have := sub_mem hkC hkA
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hcA' : c' ∈ drawAmbientCenter q D := hcA
    have hzero : c' ∈ (⊥ : Submodule (ZMod 2) D.1) := by
      rw [← (drawComplement_spec q D).disjoint.eq_bot]
      exact ⟨hcA', hc'⟩
    have hc0 : (D.1.subtype c' : Ambient I) = 0 := by simpa using hzero
    have hk0 : k = 0 := by
      have : k ∈ q.K ⊓ questionEquationSpan q := ⟨hk, by simpa [hc0] using hxE⟩
      have htrans : q.K ⊓ questionEquationSpan q = ⊥ := by
        simpa [questionEquationSpan] using q.transverse
      rw [htrans] at this
      simpa using this
    simpa [hc0, hk0]
  · exact bot_le

private theorem drawK_inf_complement_bot
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    q.K ⊓ (drawComplement q D).map D.1.subtype = ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_map.mp hx.2 with ⟨c, hc, rfl⟩
    have hcA : (c : Ambient I) ∈ centerEquationSpan q :=
      (le_sup_left : q.K ≤ centerEquationSpan q) hx.1
    have hcA' : c ∈ drawAmbientCenter q D := hcA
    have hzero : c ∈ (⊥ : Submodule (ZMod 2) D.1) := by
      rw [← (drawComplement_spec q D).disjoint.eq_bot]
      exact ⟨hcA', hc⟩
    simpa using hzero
  · exact bot_le

private theorem drawIncrement_finrank
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    Module.finrank (ZMod 2) (drawIncrement q D) = 2*h := by
  have hdim := (drawAmbientCenter q D).finrank_le
  rw [drawAmbientCenter_finrank q D, D.2.2.2.2] at hdim
  have ht : t ≤ 2*h := by omega
  unfold drawIncrement
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := Ambient I)
    q.K ((drawComplement q D).map D.1.subtype)
  rw [drawK_inf_complement_bot q D, finrank_bot, add_zero,
    q.finrank_K, Submodule.finrank_map_subtype_eq,
    drawComplement_finrank q D] at hs
  omega

noncomputable def drawPresentation
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    PresentedLeaf I J h :=
  { U := q.U
    goodU := q.goodU
    card_U := q.card_U
    L := drawIncrement q D
    L_le := drawIncrement_le_domain q D |>.trans D.2.1
    finrank_L := drawIncrement_finrank q D
    transverse := drawIncrement_inf_equation_bot q D }

private theorem drawAmbientCenter_eq
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (D : DomainDraw q h) :
    drawAmbientCenter q D =
      q.K.comap D.1.subtype ⊔ (questionEquationSpan q).comap D.1.subtype := by
  unfold drawAmbientCenter centerEquationSpan
  apply Submodule.comap_sup_of_injective D.1.injective_subtype
  · intro x hx
    exact ⟨⟨x, D.2.2.1 hx⟩, rfl⟩
  · intro x hx
    exact ⟨⟨x, D.2.2.2.1 hx⟩, rfl⟩

theorem drawPresentation_domain
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    (drawPresentation q h D).domain = D.1 := by
  unfold drawPresentation PresentedLeaf.domain drawIncrement
  apply le_antisymm
  · exact sup_le (drawIncrement_le_domain q D) D.2.2.2.1
  · intro x hx
    let xd : D.1 := ⟨x, hx⟩
    obtain ⟨a, c, ha, hc, hac⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp
        (drawComplement_spec q D).codisjoint xd
    have haA : (a : Ambient I) ∈ centerEquationSpan q := ha
    rcases Submodule.mem_sup.mp haA with ⟨k, hk, e, he, hke⟩
    apply Submodule.mem_sup.mpr
    refine ⟨k + D.1.subtype c, ?_, e, he, ?_⟩
    · apply Submodule.mem_sup.mpr
      have hcmap : D.1.subtype c ∈
          Submodule.map D.1.subtype (drawComplement q D) :=
        Submodule.mem_map.mpr ⟨c, hc, rfl⟩
      refine ⟨k, hk, D.1.subtype c, hcmap, ?_⟩
      rfl
    · change k + D.1.subtype c + (e : Ambient I) = x
      calc
        k + D.1.subtype c + (e : Ambient I) =
            (k + e) + D.1.subtype c := by abel
        _ = a + D.1.subtype c := by rw [hke]
        _ = x := by
          have hac' := congrArg (fun z : D.1 => (z : Ambient I)) hac
          exact hac'

theorem drawPresentation_center_le
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    q.K ≤ (drawPresentation q h D).L := by
  exact le_sup_left

noncomputable def drawVertex
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    LeafVertex I J h :=
  ⟨D.1, ⟨drawPresentation q h D, drawPresentation_domain q h D⟩⟩

theorem drawVertex_val
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    (drawVertex q h D).1 = D.1 := rfl

theorem drawVertex_center_le
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    q.K ≤ (drawVertex q h D).1 := by
  simpa [drawVertex] using D.2.2.1

noncomputable def drawCenter
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    CenterSubspace (drawVertex q h D) t :=
  { K := q.K
    le_domain := drawVertex_center_le q h D
    transverse := by
      have hH := vertexH_eq_of_presentation
        (drawVertex q h D) (drawPresentation q h D) (drawPresentation_domain q h D)
      rw [hH]
      simpa [drawPresentation, PresentedLeaf.H, questionEquationSpan] using q.transverse
    finrank := q.finrank_K }

theorem drawCenter_val
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D : DomainDraw q h) :
    (drawCenter q h D).K = q.K := rfl

theorem drawVertex_rel_iff
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D₁ D₂ : DomainDraw q h) :
    LeafVertex.Rel (drawVertex q h D₁) (drawVertex q h D₂) ↔ D₁.1 = D₂.1 := by
  constructor
  · intro hRel
    have hPQ := (LeafVertex.Rel_iff_presented
      (drawVertex q h D₁) (drawVertex q h D₂)
      (drawPresentation q h D₁) (drawPresentation q h D₂)
      (drawPresentation_domain q h D₁) (drawPresentation_domain q h D₂)).mp hRel
    have hDom : (drawPresentation q h D₁).domain =
        (drawPresentation q h D₂).domain := by
      have hH : (drawPresentation q h D₁).H = (drawPresentation q h D₂).H := by
        rfl
      calc
        (drawPresentation q h D₁).domain =
            (drawPresentation q h D₁).domain ⊔ (drawPresentation q h D₂).H := by
              rw [← hH]
              exact (sup_eq_left.mpr (drawPresentation q h D₁).H_le_domain).symm
        _ = (drawPresentation q h D₂).domain ⊔
            (drawPresentation q h D₁).H := hPQ
        _ = (drawPresentation q h D₂).domain :=
          sup_eq_left.mpr (drawPresentation q h D₂).H_le_domain
    simpa [drawPresentation_domain q h D₁, drawPresentation_domain q h D₂] using hDom
  · intro hD
    have hD' : D₁ = D₂ := Subtype.ext hD
    cases hD'
    exact LeafVertex.Rel.refl _

theorem drawVertex_injective
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) :
    Function.Injective (fun D : DomainDraw q h => drawVertex q h D) := by
  intro D₁ D₂ hD
  apply Subtype.ext
  have hD' : drawVertex q h D₁ = drawVertex q h D₂ := by
    simpa only using hD
  simpa [drawVertex] using congrArg Subtype.val hD'

theorem cliqueOf_drawVertex_eq_iff
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) (D₁ D₂ : DomainDraw q h) :
    cliqueOf (drawVertex q h D₁) = cliqueOf (drawVertex q h D₂) ↔ D₁.1 = D₂.1 := by
  rw [cliqueOf_eq_iff, drawVertex_rel_iff]

theorem cliqueOf_drawVertex_injective
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat) :
    Function.Injective (fun D : DomainDraw q h => cliqueOf (drawVertex q h D)) := by
  intro D₁ D₂ hD
  exact Subtype.ext ((cliqueOf_drawVertex_eq_iff q h D₁ D₂).mp hD)

end
end PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
