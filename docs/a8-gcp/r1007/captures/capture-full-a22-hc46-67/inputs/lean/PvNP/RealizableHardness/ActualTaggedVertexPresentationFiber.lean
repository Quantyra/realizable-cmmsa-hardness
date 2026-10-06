import PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
import PvNP.RealizableHardness.ActualFiniteLaw

/-! A presented leaf `(U,L)` is a presentation of the full leaf vertex
`D = H_U ⊔ L`.  This file counts the presentations of each vertex.  The
constant fiber is needed to compare uniform presentation draws with the
manuscript's uniform vertex draw. -/

namespace PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

def VertexPresentation {J h : Nat} (v : TaggedPresentedVertex I copies J h) :=
  {P : TaggedPresentedLeaf I copies J h // P.domain I copies = v.1}

instance {J h : Nat} (v : TaggedPresentedVertex I copies J h) :
    Fintype (VertexPresentation I copies v) := by
  unfold VertexPresentation
  infer_instance

def vertexBase {J h : Nat} (v : TaggedPresentedVertex I copies J h) :
    VertexPresentation I copies v :=
  ⟨Classical.choose v.property, Classical.choose_spec v.property⟩

theorem rows_eq_base {J h : Nat}
    (v : TaggedPresentedVertex I copies J h)
    (P : VertexPresentation I copies v) :
    P.1.U = (vertexBase I copies v).1.U :=
  tagged_presented_U_eq_of_domain_eq I copies P.1
    (vertexBase I copies v).1 (P.2.trans (vertexBase I copies v).2.symm)

/-- Two presentations of the same full vertex lie in the same tagged class.
Thus passing from presentations to vertices does not split a class. -/
theorem class_eq_of_domain_eq {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h)
    (hD : P.domain I copies = Q.domain I copies) :
    taggedClassOf I copies P = taggedClassOf I copies Q := by
  apply (taggedClassOf_eq_iff I copies).mpr
  change P.domain I copies ⊔ Q.H I copies =
    Q.domain I copies ⊔ P.H I copies
  rw [hD, taggedPresented_H_eq_of_domain_eq I copies P Q hD]

private theorem base_H_le_vertex {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    (vertexBase I copies v).1.H I copies ≤ v.1 := by
  exact le_trans le_sup_right (le_of_eq (vertexBase I copies v).2)

def vertexEquationSpace {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Submodule (ZMod 2) v.1 :=
  ((vertexBase I copies v).1.H I copies).comap v.1.subtype

theorem vertexEquationSpace_eq_of_presentation {J h : Nat}
    (v : TaggedPresentedVertex I copies J h)
    (P : VertexPresentation I copies v) :
    vertexEquationSpace I copies v =
      (P.1.H I copies).comap v.1.subtype := by
  exact congrArg (fun H : Submodule (ZMod 2) (TaggedAmbient I copies) =>
      H.comap v.1.subtype)
    ((congrArg (equationSpan (taggedSource I copies).support)
      (rows_eq_base I copies v P)).symm)

theorem vertex_dim {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Module.finrank (ZMod 2) v.1 = J + 2 * h := by
  let P := (vertexBase I copies v).1
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := TaggedAmbient I copies) (P.H I copies) P.L
  have htrans : P.H I copies ⊓ P.L = ⊥ := by
    have h : P.L ⊓ P.H I copies = ⊥ := P.transverse
    rw [inf_comm]
    exact h
  rw [htrans, finrank_bot, add_zero, sup_comm] at hd
  change Module.finrank (ZMod 2) (P.domain I copies) =
    Module.finrank (ZMod 2) (P.H I copies) +
      Module.finrank (ZMod 2) P.L at hd
  rw [(vertexBase I copies v).2] at hd
  have hH : Module.finrank (ZMod 2) (P.H I copies) = J := by
    change Module.finrank (ZMod 2)
      (equationSpan (taggedSource I copies).support P.U) = J
    rw [equationSpan_finrank_eq_card
      (taggedSource I copies).support (taggedSource_support_card I copies)
      P.U P.goodU, P.card_U]
  rw [hH, P.finrank_L] at hd
  omega

theorem vertexEquationSpace_dim {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Module.finrank (ZMod 2) (vertexEquationSpace I copies v) = J := by
  rw [vertexEquationSpace,
    (Submodule.comapSubtypeEquivOfLe (base_H_le_vertex I copies v)).finrank_eq]
  rw [TaggedPresentedLeaf.H, equationSpan_finrank_eq_card
    (taggedSource I copies).support (taggedSource_support_card I copies)
    (vertexBase I copies v).1.U (vertexBase I copies v).1.goodU,
    (vertexBase I copies v).1.card_U]

def presentationToComplement {J h : Nat}
    (v : TaggedPresentedVertex I copies J h)
    (P : VertexPresentation I copies v) :
    {L : Submodule (ZMod 2) v.1 //
      IsCompl (vertexEquationSpace I copies v) L} := by
  let L := P.1.L.comap v.1.subtype
  have hLle : P.1.L ≤ v.1 := by
    exact le_trans le_sup_left (le_of_eq P.2)
  have hH : P.1.H I copies = (vertexBase I copies v).1.H I copies := by
    exact congrArg (equationSpan (taggedSource I copies).support)
      (rows_eq_base I copies v P)
  have hLdim : Module.finrank (ZMod 2) L = 2 * h := by
    rw [(Submodule.comapSubtypeEquivOfLe hLle).finrank_eq, P.1.finrank_L]
  have hdis : Disjoint (vertexEquationSpace I copies v) L := by
    rw [disjoint_iff]
    change ((vertexBase I copies v).1.H I copies).comap v.1.subtype ⊓
      P.1.L.comap v.1.subtype = ⊥
    have htrans : P.1.H I copies ⊓ P.1.L = ⊥ := by
      have h : P.1.L ⊓ P.1.H I copies = ⊥ := P.1.transverse
      rw [inf_comm]
      exact h
    rw [← Submodule.comap_inf, ← hH, htrans]
    exact Submodule.ker_subtype v.1
  have hdim : Module.finrank (ZMod 2) v.1 ≤
      Module.finrank (ZMod 2) (vertexEquationSpace I copies v) +
      Module.finrank (ZMod 2) L := by
    rw [vertex_dim I copies v, vertexEquationSpace_dim I copies v, hLdim]
  exact ⟨L, (Submodule.isCompl_iff_disjoint _ _ hdim).mpr hdis⟩

private theorem presentationToComplement_injective {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Function.Injective (presentationToComplement I copies v) := by
  intro P Q hPQ
  have hrows : P.1.U = Q.1.U :=
    (rows_eq_base I copies v P).trans (rows_eq_base I copies v Q).symm
  have hcomap : P.1.L.comap v.1.subtype = Q.1.L.comap v.1.subtype :=
    congrArg Subtype.val hPQ
  have hPle : P.1.L ≤ v.1 :=
    le_trans le_sup_left (le_of_eq P.2)
  have hQle : Q.1.L ≤ v.1 :=
    le_trans le_sup_left (le_of_eq Q.2)
  have hL : P.1.L = Q.1.L := by
    have h := congrArg (fun L : Submodule (ZMod 2) v.1 =>
      L.map v.1.subtype) hcomap
    simpa [Submodule.map_comap_subtype, inf_of_le_right hPle,
      inf_of_le_right hQle] using h
  apply Subtype.ext
  rcases P with ⟨P, hP⟩
  rcases Q with ⟨Q, hQ⟩
  change P = Q
  cases P with
  | mk U goodU card_U L L_le finrank_L transverse =>
    cases Q with
    | mk U' goodU' card_U' L' L_le' finrank_L' transverse' =>
      have hU : U = U' := hrows
      have hL' : L = L' := hL
      cases hU
      cases hL'
      rfl

private theorem presentationToComplement_surjective {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Function.Surjective (presentationToComplement I copies v) := by
  intro Q
  let P₀ := (vertexBase I copies v).1
  let L : Submodule (ZMod 2) (TaggedAmbient I copies) :=
    Q.1.map v.1.subtype
  have hHle : P₀.H I copies ≤ v.1 := base_H_le_vertex I copies v
  have hLle : L ≤ v.1 := by
    exact Submodule.map_subtype_le v.1 Q.1
  have hHmap : v.1.mapIic (vertexEquationSpace I copies v) =
      (⟨P₀.H I copies, hHle⟩ : Set.Iic v.1) := by
    apply Subtype.ext
    change (vertexEquationSpace I copies v).map v.1.subtype = P₀.H I copies
    rw [vertexEquationSpace, Submodule.map_comap_subtype]
    exact inf_of_le_right hHle
  have hcompl : IsCompl
      (⟨P₀.H I copies, hHle⟩ : Set.Iic v.1)
      (v.1.mapIic Q.1) := by
    rw [← hHmap]
    exact (v.1.mapIic.isCompl_iff).mp Q.2
  have hprops := (Set.Iic.isCompl_iff).mp hcompl
  have htrans : L ⊓ P₀.H I copies = ⊥ := by
    have h0 : P₀.H I copies ⊓ L = ⊥ := by
      simpa only [Submodule.coe_mapIic_apply] using
        (disjoint_iff.mp hprops.1)
    rw [inf_comm]
    exact h0
  have hdomain : L ⊔ P₀.H I copies = v.1 := by
    simpa [L, sup_comm] using hprops.2
  have hLdim : Module.finrank (ZMod 2) L = 2 * h := by
    have hd := Submodule.finrank_add_eq_of_isCompl Q.2
    rw [vertexEquationSpace_dim I copies v, vertex_dim I copies v] at hd
    have hq : Module.finrank (ZMod 2) Q.1 = 2 * h := by omega
    simpa [L, Submodule.finrank_map_subtype_eq] using hq
  have hLcoord : L ≤ coordinateSpace (taggedSource I copies).support P₀.U :=
    hLle.trans (by
      rw [← (vertexBase I copies v).2]
      exact P₀.domain_le_coordinateSpace I copies)
  let P : TaggedPresentedLeaf I copies J h :=
    { U := P₀.U
      goodU := P₀.goodU
      card_U := P₀.card_U
      L := L
      L_le := hLcoord
      finrank_L := hLdim
      transverse := by simpa [TaggedPresentedLeaf.H] using htrans }
  refine ⟨⟨P, ?_⟩, ?_⟩
  · exact hdomain
  · apply Subtype.ext
    change L.comap v.1.subtype = Q.1
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective Q.1

noncomputable def presentationComplementEquiv {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    VertexPresentation I copies v ≃
      {L : Submodule (ZMod 2) v.1 //
        IsCompl (vertexEquationSpace I copies v) L} :=
  Equiv.ofBijective (presentationToComplement I copies v)
    ⟨presentationToComplement_injective I copies v,
      presentationToComplement_surjective I copies v⟩

/-- Every full tagged leaf vertex has the same number of transverse
`(U,L)` presentations. This is the incidence factor required before a
uniform presentation can be treated as a uniform manuscript vertex. -/
theorem vertexPresentation_card {J h : Nat}
    (v : TaggedPresentedVertex I copies J h) :
    Fintype.card (VertexPresentation I copies v) = 2 ^ (J * (2 * h)) := by
  classical
  letI : Finite (Submodule (ZMod 2) v.1) :=
    Finite.of_injective (fun L => (L : Set v.1)) SetLike.coe_injective
  letI : Fintype (Submodule (ZMod 2) v.1) := Fintype.ofFinite _
  let P₀ := (vertexBase I copies v).1
  have hC : IsCompl (vertexEquationSpace I copies v)
      ((P₀.L).comap v.1.subtype) :=
    (presentationToComplement I copies v (vertexBase I copies v)).2
  calc
    Fintype.card (VertexPresentation I copies v) =
        Fintype.card {L : Submodule (ZMod 2) v.1 //
          IsCompl (vertexEquationSpace I copies v) L} :=
      Fintype.card_congr (presentationComplementEquiv I copies v)
    _ = 2 ^ (Module.finrank (ZMod 2) ((P₀.L).comap v.1.subtype) *
          Module.finrank (ZMod 2) (vertexEquationSpace I copies v)) :=
      card_complements_eq_two_pow
        (vertexEquationSpace I copies v)
        ((P₀.L).comap v.1.subtype) hC
    _ = 2 ^ (J * (2 * h)) := by
      have hLle : P₀.L ≤ v.1 := by
        exact le_trans le_sup_left (le_of_eq (vertexBase I copies v).2)
      rw [(Submodule.comapSubtypeEquivOfLe hLle).finrank_eq,
        P₀.finrank_L, vertexEquationSpace_dim I copies v]
      congr 1
      exact Nat.mul_comm _ _

/-- Full-domain vertices occurring in a fixed tagged clique class. -/
def VertexClassRepresentative {J h : Nat}
    (C : TaggedLeafClass I copies J h) :=
  {v : TaggedPresentedVertex I copies J h //
    ∃ r : TaggedClassRepresentative I copies C,
      taggedCanonicalVertex I copies r.1 = v}

noncomputable instance taggedPresentedVertexFintype {J h : Nat} :
    Fintype (TaggedPresentedVertex I copies J h) := by
  letI : Finite (Submodule (ZMod 2) (TaggedAmbient I copies)) :=
    Finite.of_injective (fun D => (D : Set (TaggedAmbient I copies)))
      SetLike.coe_injective
  letI : Finite (TaggedPresentedVertex I copies J h) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance vertexClassRepresentativeFintype {J h : Nat}
    (C : TaggedLeafClass I copies J h) :
    Fintype (VertexClassRepresentative I copies C) := by
  letI : Finite (VertexClassRepresentative I copies C) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

instance vertexClassRepresentativeNonempty {J h : Nat}
    (C : TaggedLeafClass I copies J h) :
    Nonempty (VertexClassRepresentative I copies C) := by
  obtain ⟨r⟩ := taggedClassRepresentativeNonempty I copies C
  exact ⟨⟨taggedCanonicalVertex I copies r.1, ⟨r, rfl⟩⟩⟩

def classRepresentativeVertex {J h : Nat}
    {C : TaggedLeafClass I copies J h}
    (r : TaggedClassRepresentative I copies C) :
    VertexClassRepresentative I copies C :=
  ⟨taggedCanonicalVertex I copies r.1, ⟨r, rfl⟩⟩

noncomputable instance classRepresentativeFiberFintype {J h : Nat}
    {C : TaggedLeafClass I copies J h}
    (v : VertexClassRepresentative I copies C) :
    Fintype {r : TaggedClassRepresentative I copies C //
      classRepresentativeVertex I copies r = v} := by
  classical
  infer_instance

private theorem classRepresentativeVertex_surjective {J h : Nat}
    {C : TaggedLeafClass I copies J h} :
    Function.Surjective (classRepresentativeVertex I copies (C := C)) := by
  intro v
  obtain ⟨r, hr⟩ := v.2
  exact ⟨r, Subtype.ext hr⟩

/-- The presentations in a fixed tagged class above one full vertex are
exactly all presentations of that vertex. -/
noncomputable def classRepresentativeFiberEquiv {J h : Nat}
    {C : TaggedLeafClass I copies J h}
    (v : VertexClassRepresentative I copies C) :
    {r : TaggedClassRepresentative I copies C //
      classRepresentativeVertex I copies r = v} ≃
      VertexPresentation I copies v.1 := by
  classical
  let r₀ := Classical.choose v.2
  have hr₀ : taggedCanonicalVertex I copies r₀.1 = v.1 :=
    Classical.choose_spec v.2
  have hr₀D : r₀.1.domain I copies = v.1.1 :=
    congrArg Subtype.val hr₀
  refine {
    toFun := fun r => ⟨r.1.1, congrArg (fun w : VertexClassRepresentative I copies C =>
      w.1.1) r.2⟩
    invFun := fun P => ⟨⟨P.1, ?_⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (class_eq_of_domain_eq I copies P.1 r₀.1
      (P.2.trans hr₀D.symm)).trans r₀.2
  · apply Subtype.ext
    apply Subtype.ext
    exact P.2
  · intro r
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro P
    apply Subtype.ext
    rfl

theorem classRepresentativeFiber_card {J h : Nat}
    {C : TaggedLeafClass I copies J h}
    (v : VertexClassRepresentative I copies C) :
    Fintype.card {r : TaggedClassRepresentative I copies C //
      classRepresentativeVertex I copies r = v} = 2 ^ (J * (2 * h)) := by
  classical
  exact (Fintype.card_congr (classRepresentativeFiberEquiv I copies v)).trans
    (vertexPresentation_card I copies v.1)

private theorem classRepresentative_card {J h : Nat}
    (C : TaggedLeafClass I copies J h) :
    Fintype.card (TaggedClassRepresentative I copies C) =
      Fintype.card (VertexClassRepresentative I copies C) *
        2 ^ (J * (2 * h)) := by
  classical
  calc
    Fintype.card (TaggedClassRepresentative I copies C) =
        Fintype.card (Σ v : VertexClassRepresentative I copies C,
          {r : TaggedClassRepresentative I copies C //
            classRepresentativeVertex I copies r = v}) :=
      (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (classRepresentativeVertex I copies (C := C)))).symm
    _ = ∑ v : VertexClassRepresentative I copies C,
          Fintype.card {r : TaggedClassRepresentative I copies C //
            classRepresentativeVertex I copies r = v} :=
      Fintype.card_sigma
    _ = ∑ _v : VertexClassRepresentative I copies C,
          2 ^ (J * (2 * h)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact classRepresentativeFiber_card I copies v
    _ = Fintype.card (VertexClassRepresentative I copies C) *
          2 ^ (J * (2 * h)) := by
      simp [Finset.sum_const]

/-- Uniform presentation representatives push forward to uniform full-domain
vertices in the same tagged class. This repairs the representative law used
by the physical manuscript sampler; no table coherence is assumed. -/
theorem uniform_classRepresentative_pushforward {J h : Nat}
    (C : TaggedLeafClass I copies J h) :
    pushforward (classRepresentativeVertex I copies)
      (uniformLaw (TaggedClassRepresentative I copies C)) =
        uniformLaw (VertexClassRepresentative I copies C) := by
  classical
  apply FiniteLaw.ext
  intro v
  rw [pushforward_apply, uniformLaw_apply]
  simp_rw [uniformLaw_apply (TaggedClassRepresentative I copies C)]
  have hsum :
      (∑ r : TaggedClassRepresentative I copies C,
        if classRepresentativeVertex I copies r = v then
          (1 : ℚ) / Fintype.card (TaggedClassRepresentative I copies C) else 0) =
      (Fintype.card {r : TaggedClassRepresentative I copies C //
        classRepresentativeVertex I copies r = v} : ℚ) /
        Fintype.card (TaggedClassRepresentative I copies C) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [← Fintype.card_subtype
      (fun r : TaggedClassRepresentative I copies C =>
        classRepresentativeVertex I copies r = v)]
    simp [div_eq_mul_inv]
  rw [hsum, classRepresentativeFiber_card I copies v,
    classRepresentative_card I copies C]
  have hc : ((2 ^ (J * (2 * h)) : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero _ (by decide : (2 : Nat) ≠ 0))
  have hv : (Fintype.card (VertexClassRepresentative I copies C) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (VertexClassRepresentative I copies C) ≠ 0)
  field_simp
  simp [Nat.cast_mul, mul_comm]

end
end PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
