import PvNP.RealizableHardness.ActualTaggedConditionalDomainCollision
import PvNP.RealizableHardness.GrassmannCounting

/-! Full-domain count for a fixed tagged question, with its ambient center held fixed. -/

namespace PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
open PvNP.RealizableHardness.ActualTaggedConditionalDomainCollision
open PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

def TaggedDomainDraw {J t : Nat} (q : TaggedQuestionCenter I copies J t) (h : Nat) :=
  {D : Submodule (ZMod 2) (TaggedAmbient I copies) //
    D ≤ coordinateSpaceOf I copies q ∧ q.K ≤ D ∧ equationSpanOf I copies q ≤ D ∧
    Module.finrank (ZMod 2) D = J + 2 * h}

instance {J t h : Nat} (q : TaggedQuestionCenter I copies J t) :
    Finite (TaggedDomainDraw I copies q h) := by
  letI : Finite (Submodule (ZMod 2) (TaggedAmbient I copies)) :=
    Finite.of_injective (fun D => (D : Set (TaggedAmbient I copies)))
      SetLike.coe_injective
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance {J t h : Nat} (q : TaggedQuestionCenter I copies J t) :
    Fintype (TaggedDomainDraw I copies q h) := Fintype.ofFinite _

def taggedCenterSpan {J t : Nat} (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  q.K ⊔ equationSpanOf I copies q

def taggedCenterInCoordinate {J t : Nat} (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (coordinateSpaceOf I copies q) :=
  (taggedCenterSpan I copies q).comap (coordinateSpaceOf I copies q).subtype

theorem taggedCenterSpan_le_coordinate {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    taggedCenterSpan I copies q ≤ coordinateSpaceOf I copies q :=
  sup_le q.K_le (by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    exact ActualStarSpanIntersection.equationVector_mem_coordinateSpace
      (taggedSource I copies).support q.U e he)

theorem taggedCenterSpan_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (taggedCenterSpan I copies q) = t + J := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := TaggedAmbient I copies) q.K (equationSpanOf I copies q)
  have htrans : q.K ⊓ equationSpanOf I copies q = ⊥ := q.transverse
  rw [htrans, finrank_bot, q.finrank_K,
    taggedEquation_finrank I copies q, add_zero] at hs
  unfold taggedCenterSpan
  exact hs

theorem taggedCenterInCoordinate_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (taggedCenterInCoordinate I copies q) = t + J := by
  unfold taggedCenterInCoordinate
  rw [(Submodule.comapSubtypeEquivOfLe
    (taggedCenterSpan_le_coordinate I copies q)).finrank_eq]
  exact taggedCenterSpan_finrank I copies q

abbrev TaggedCenterQuotient {J t : Nat} (q : TaggedQuestionCenter I copies J t) :=
  coordinateSpaceOf I copies q ⧸ taggedCenterInCoordinate I copies q

theorem taggedCenterQuotient_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (TaggedCenterQuotient I copies q) = 2 * J - t := by
  have hs := (taggedCenterInCoordinate I copies q).finrank_quotient_add_finrank
  rw [taggedCenterInCoordinate_finrank I copies q,
    taggedCoordinate_finrank I copies q] at hs
  have hs' := hs
  simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hs'
  have hsum : Module.finrank (ZMod 2) (TaggedCenterQuotient I copies q) + t =
      2 * J := by simpa [Nat.add_comm, Nat.succ_mul] using hs'
  exact Nat.eq_sub_of_add_eq hsum

private theorem quotient_map_dimension
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Q L : Submodule (ZMod 2) V) (hQL : Q ≤ L) :
    Module.finrank (ZMod 2) (L.map Q.mkQ) + Module.finrank (ZMod 2) Q =
      Module.finrank (ZMod 2) L := by
  have hs := (Q.mkQ.domRestrict L).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (Q.mkQ.domRestrict L) = Q.comap L.subtype := by
    ext x
    simp
  rw [LinearMap.range_domRestrict, hk] at hs
  rw [(Submodule.comapSubtypeEquivOfLe hQL).finrank_eq] at hs
  exact hs

private def containingQuotientEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {a d : Nat} (Q : Grass V a) (had : a ≤ d) :
    {L : Grass V d // Q.val ≤ L.val} ≃ Grass (V ⧸ Q.val) (d - a) where
  toFun L := ⟨L.val.val.map Q.val.mkQ, by
    have hs := quotient_map_dimension Q.val L.val.val L.property
    rw [Q.property, L.val.property] at hs
    omega⟩
  invFun R := ⟨⟨R.val.comap Q.val.mkQ, by
      have hs := quotient_map_dimension Q.val (R.val.comap Q.val.mkQ)
        (Submodule.le_comap_mkQ Q.val R.val)
      have hm : (R.val.comap Q.val.mkQ).map Q.val.mkQ = R.val :=
        Submodule.map_comap_eq_self (by simp)
      rw [hm, R.property, Q.property] at hs
      omega⟩, Submodule.le_comap_mkQ Q.val R.val⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Submodule.comap_map_mkQ] using
      (sup_eq_right.mpr L.property : Q.val ⊔ L.val.val = L.val.val)
  right_inv R := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

private def taggedCoordinateContainingEquiv {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    TaggedDomainDraw I copies q h ≃
      {L : Grass (coordinateSpaceOf I copies q) (J + 2 * h) //
        taggedCenterInCoordinate I copies q ≤ L.val} where
  toFun D := ⟨⟨D.1.comap (coordinateSpaceOf I copies q).subtype, by
      rw [(Submodule.comapSubtypeEquivOfLe D.2.1).finrank_eq, D.2.2.2.2]⟩, by
      intro z hz
      have hc : taggedCenterSpan I copies q ≤ D.1 :=
        sup_le D.2.2.1 D.2.2.2.1
      exact hc (show (z : TaggedAmbient I copies) ∈ taggedCenterSpan I copies q from hz)⟩
  invFun L := ⟨L.val.val.map (coordinateSpaceOf I copies q).subtype, by
      exact (coordinateSpaceOf I copies q).map_subtype_le L.val.val,
      by
        intro x hx
        let z : coordinateSpaceOf I copies q := ⟨x, q.K_le hx⟩
        have hz : z ∈ taggedCenterInCoordinate I copies q :=
          (le_sup_left : q.K ≤ taggedCenterSpan I copies q) hx
        exact ⟨z, L.property hz, rfl⟩,
      by
        intro x hx
        have he : equationSpanOf I copies q ≤ coordinateSpaceOf I copies q := by
          apply Submodule.span_le.mpr
          rintro _ ⟨e, he, rfl⟩
          exact ActualStarSpanIntersection.equationVector_mem_coordinateSpace
            (taggedSource I copies).support q.U e he
        let z : coordinateSpaceOf I copies q := ⟨x, he hx⟩
        have hz : z ∈ taggedCenterInCoordinate I copies q :=
          (le_sup_right : equationSpanOf I copies q ≤ taggedCenterSpan I copies q) hx
        exact ⟨z, L.property hz, rfl⟩,
      by rw [Submodule.finrank_map_subtype_eq, L.val.property]⟩
  left_inv D := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by
      intro x hx
      exact ⟨⟨x, D.2.1 hx⟩, rfl⟩)
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective
      (coordinateSpaceOf I copies q).injective_subtype L.val.val

noncomputable def taggedDomainDrawEquiv {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) (h : Nat)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    TaggedDomainDraw I copies q h ≃
      Grass (TaggedCenterQuotient I copies q) (2 * h - t) := by
  letI : Finite (TaggedCenterQuotient I copies q) :=
    Finite.of_surjective (taggedCenterInCoordinate I copies q).mkQ
      (taggedCenterInCoordinate I copies q).mkQ_surjective
  have hd : J + 2 * h - (t + J) = 2 * h - t := by omega
  exact (taggedCoordinateContainingEquiv I copies q).trans
    ((containingQuotientEquiv
      (V := coordinateSpaceOf I copies q) (a := t + J) (d := J + 2 * h)
      ⟨taggedCenterInCoordinate I copies q,
        taggedCenterInCoordinate_finrank I copies q⟩
      (by omega)).trans (Equiv.cast (by rw [hd])))

theorem taggedDomainDraw_card {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) (h : Nat)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    Fintype.card (TaggedDomainDraw I copies q h) =
      gaussian (2 * J - t) (2 * h - t) := by
  letI : Finite (TaggedCenterQuotient I copies q) :=
    Finite.of_surjective (taggedCenterInCoordinate I copies q).mkQ
      (taggedCenterInCoordinate I copies q).mkQ_surjective
  rw [Fintype.card_congr (taggedDomainDrawEquiv I copies q h ht hh), card_grass]
  rw [taggedCenterQuotient_finrank I copies q]

/-- Choose a transverse presentation of each eligible full domain while
keeping the stored ambient center inside the transverse increment. -/
theorem taggedDomainDraw_has_leaf {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    ∃ P : ActualTaggedConcreteStarLaw.TaggedLeafOver I copies h q,
      P.1.domain I copies = D.1 := by
  let H : Submodule (ZMod 2) D.1 :=
    (equationSpanOf I copies q).comap D.1.subtype
  let K : Submodule (ZMod 2) D.1 := q.K.comap D.1.subtype
  have hdis : Disjoint K H := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    have h : (x : TaggedAmbient I copies) ∈
        q.K ⊓ equationSpanOf I copies q := ⟨hx.1, hx.2⟩
    have htrans : q.K ⊓ equationSpanOf I copies q = ⊥ := q.transverse
    rw [htrans] at h
    exact Subtype.ext (by simpa using h)
  obtain ⟨C, hKC, hcompl⟩ := hdis.exists_isCompl
  let L : Submodule (ZMod 2) (TaggedAmbient I copies) := C.map D.1.subtype
  have hLdim : Module.finrank (ZMod 2) L = 2 * h := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (K := ZMod 2) (V := D.1) H C
    rw [hcompl.symm.codisjoint.eq_top, finrank_top,
      hcompl.symm.disjoint.eq_bot, finrank_bot, add_zero] at hs
    have hHdim : Module.finrank (ZMod 2) H = J := by
      rw [(Submodule.comapSubtypeEquivOfLe D.2.2.2.1).finrank_eq]
      exact taggedEquation_finrank I copies q
    rw [hHdim, D.2.2.2.2] at hs
    rw [Submodule.finrank_map_subtype_eq]
    omega
  let P : TaggedPresentedLeaf I copies J h :=
    { U := q.U
      goodU := q.goodU
      card_U := q.card_U
      L := L
      L_le := by
        intro x hx
        rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact D.2.1 y.2
      finrank_L := hLdim
      transverse := by
        apply le_antisymm ?_ bot_le
        intro x hx
        rcases Submodule.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
        have he : y ∈ H := hx.2
        have hbot : y ∈ C ⊓ H := ⟨hy, he⟩
        rw [hcompl.disjoint.eq_bot] at hbot
        simpa using congrArg D.1.subtype hbot }
  refine ⟨⟨P, rfl, ?_⟩, ?_⟩
  · intro x hx
    let y : D.1 := ⟨x, D.2.2.1 hx⟩
    have hy : y ∈ K := hx
    exact ⟨y, hKC hy, rfl⟩
  · change P.domain I copies = D.1
    dsimp only [P, TaggedPresentedLeaf.domain, TaggedPresentedLeaf.H, L]
    rw [sup_comm]
    change equationSpanOf I copies q ⊔ C.map D.1.subtype = D.1
    have hHmap : H.map D.1.subtype = equationSpanOf I copies q := by
      simp [H, Submodule.map_comap_subtype, inf_of_le_right D.2.2.2.1]
    calc
      equationSpanOf I copies q ⊔ C.map D.1.subtype =
          H.map D.1.subtype ⊔ C.map D.1.subtype := by rw [hHmap]
      _ = (H ⊔ C).map D.1.subtype := (Submodule.map_sup H C D.1.subtype).symm
      _ = D.1 := by rw [hcompl.symm.codisjoint.eq_top]; simp

noncomputable def taggedDomainDraw_leaf {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    ActualTaggedConcreteStarLaw.TaggedLeafOver I copies h q :=
  Classical.choose (taggedDomainDraw_has_leaf I copies q D)

theorem taggedDomainDraw_leaf_domain {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    (taggedDomainDraw_leaf I copies q D).1.domain I copies = D.1 :=
  Classical.choose_spec (taggedDomainDraw_has_leaf I copies q D)

def taggedLeaf_domainDraw {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (P : TaggedLeafOver I copies h q) :
    TaggedDomainDraw I copies q h := by
  refine ⟨P.1.domain I copies, ?_, ?_, ?_, ?_⟩
  · simpa only [coordinateSpaceOf, P.2.1] using
      P.1.domain_le_coordinateSpace I copies
  · exact P.2.2.trans le_sup_left
  · simpa only [equationSpanOf, TaggedPresentedLeaf.H, P.2.1] using
      P.1.H_le_domain I copies
  · exact vertex_dim I copies (taggedCanonicalVertex I copies P.1)

theorem taggedLeaf_domainDraw_leaf {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    taggedLeaf_domainDraw I copies q (taggedDomainDraw_leaf I copies q D) = D := by
  apply Subtype.ext
  exact taggedDomainDraw_leaf_domain I copies q D

theorem taggedLeaf_domainDraw_eq_iff {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (P : TaggedLeafOver I copies h q)
    (D : TaggedDomainDraw I copies q h) :
    taggedLeaf_domainDraw I copies q P = D ↔ P.1.domain I copies = D.1 := by
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

def taggedLeafDomainFiber {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :=
  {P : TaggedLeafOver I copies h q // taggedLeaf_domainDraw I copies q P = D}

instance {J t h : Nat} (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    Fintype (taggedLeafDomainFiber I copies q D) := by
  unfold taggedLeafDomainFiber
  infer_instance

noncomputable def taggedLeafDomainFiberEquiv {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    taggedLeafDomainFiber I copies q D ≃
      {P : VertexPresentation I copies
        (taggedCanonicalVertex I copies (taggedDomainDraw_leaf I copies q D).1) //
        q.K ≤ P.1.L} where
  toFun P := ⟨⟨P.1.1,
      (taggedLeaf_domainDraw_eq_iff I copies q P.1 D).mp P.2 |>.trans
        (taggedDomainDraw_leaf_domain I copies q D).symm⟩, P.1.2.2⟩
  invFun P := ⟨⟨P.1.1, by
      have hU := tagged_presented_U_eq_of_domain_eq I copies P.1.1
        (taggedDomainDraw_leaf I copies q D).1 P.1.2
      exact hU.trans (taggedDomainDraw_leaf I copies q D).2.1,
      P.2⟩, by
      apply (taggedLeaf_domainDraw_eq_iff I copies q _ D).mpr
      exact P.1.2.trans (taggedDomainDraw_leaf_domain I copies q D)⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem taggedLeafDomainFiber_card {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (D : TaggedDomainDraw I copies q h) :
    Fintype.card (taggedLeafDomainFiber I copies q D) =
      2 ^ (J * (2 * h - t)) := by
  classical
  exact (Fintype.card_congr (taggedLeafDomainFiberEquiv I copies q D)).trans
    (tagged_conditional_presentation_fiber_card I copies q
      (taggedDomainDraw_leaf I copies q D))

theorem taggedDomainDraw_nonempty {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    Nonempty (TaggedDomainDraw I copies q h) := by
  have hc : 0 < Fintype.card (TaggedDomainDraw I copies q h) := by
    rw [taggedDomainDraw_card I copies q h ht hh]
    exact gaussian_pos (by omega : 2 * h - t ≤ 2 * J - t)
  exact Fintype.card_pos_iff.mp hc

private theorem taggedLeafOver_card {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Fintype.card (TaggedLeafOver I copies h q) =
      Fintype.card (TaggedDomainDraw I copies q h) *
        2 ^ (J * (2 * h - t)) := by
  classical
  calc
    Fintype.card (TaggedLeafOver I copies h q) =
        Fintype.card (Σ D : TaggedDomainDraw I copies q h,
          taggedLeafDomainFiber I copies q D) :=
      (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (taggedLeaf_domainDraw I copies q))).symm
    _ = ∑ D : TaggedDomainDraw I copies q h,
          Fintype.card (taggedLeafDomainFiber I copies q D) := Fintype.card_sigma
    _ = ∑ _D : TaggedDomainDraw I copies q h,
          2 ^ (J * (2 * h - t)) := by
      apply Finset.sum_congr rfl
      intro D _
      exact taggedLeafDomainFiber_card I copies q D
    _ = Fintype.card (TaggedDomainDraw I copies q h) *
          2 ^ (J * (2 * h - t)) := by simp [Finset.sum_const]

/-- For each fixed tagged question, independent uniform conditional leaf
presentations induce exactly the uniform distribution on eligible full
domains. The center is the same stored ambient `q.K` in both laws. -/
theorem uniform_taggedLeafDomain_pushforward {J t h : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    letI : Nonempty (TaggedDomainDraw I copies q h) :=
      taggedDomainDraw_nonempty I copies q ht hh
    letI : Nonempty (TaggedLeafOver I copies h q) :=
      ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
    ActualFiniteLaw.pushforward (taggedLeaf_domainDraw I copies q)
      (ActualFiniteLaw.uniformLaw (TaggedLeafOver I copies h q)) =
        ActualFiniteLaw.uniformLaw (TaggedDomainDraw I copies q h) := by
  classical
  letI : Nonempty (TaggedDomainDraw I copies q h) :=
    taggedDomainDraw_nonempty I copies q ht hh
  letI : Nonempty (TaggedLeafOver I copies h q) :=
    ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
  apply ActualFiniteLaw.FiniteLaw.ext
  intro D
  rw [ActualFiniteLaw.pushforward_apply, ActualFiniteLaw.uniformLaw_apply]
  simp_rw [ActualFiniteLaw.uniformLaw_apply (TaggedLeafOver I copies h q)]
  have hsum :
      (∑ P : TaggedLeafOver I copies h q,
        if taggedLeaf_domainDraw I copies q P = D then
          (1 : ℚ) / Fintype.card (TaggedLeafOver I copies h q) else 0) =
      (Fintype.card (taggedLeafDomainFiber I copies q D) : ℚ) /
        Fintype.card (TaggedLeafOver I copies h q) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [← Fintype.card_subtype
      (fun P : TaggedLeafOver I copies h q =>
        taggedLeaf_domainDraw I copies q P = D)]
    simp [taggedLeafDomainFiber, div_eq_mul_inv]
  rw [hsum, taggedLeafDomainFiber_card I copies q D,
    taggedLeafOver_card I copies q]
  have hc : ((2 ^ (J * (2 * h - t)) : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero _ (by decide : (2 : Nat) ≠ 0))
  have hd : (Fintype.card (TaggedDomainDraw I copies q h) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedDomainDraw I copies q h) ≠ 0)
  field_simp
  simp [Nat.cast_mul, mul_comm]

end
end PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
