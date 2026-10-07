import PvNP.RealizableHardness.ActualTaggedConditionalGraphCount
import PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
import PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
import PvNP.RealizableHardness.ActualQuestionCenterCollisionBound

/-! Conditional tagged leaf-domain fibers and the ordered class-collision mass. -/

namespace PvNP.RealizableHardness.ActualTaggedConditionalDomainCollision

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
open PvNP.RealizableHardness.ActualTaggedConditionalGraphCount
open PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-- For one actual tagged center `q` and one sampled full domain, the number
of eligible transverse leaf presentations of that domain containing the stored
ambient center `q.K` is `2^(J*(2*h-t))`. -/
theorem tagged_conditional_presentation_fiber_card
    {J t h : Nat} (q : TaggedQuestionCenter I copies J t)
    (P₀ : TaggedLeafOver I copies h q) :
    Fintype.card
      {P : VertexPresentation I copies (taggedCanonicalVertex I copies P₀.1) //
        q.K ≤ P.1.L} = 2 ^ (J * (2 * h - t)) := by
  letI : Finite (Submodule (ZMod 2) (taggedCanonicalVertex I copies P₀.1).1) :=
    Finite.of_injective (fun L => (L : Set (taggedCanonicalVertex I copies P₀.1).1))
      SetLike.coe_injective
  letI : Fintype (Submodule (ZMod 2) (taggedCanonicalVertex I copies P₀.1).1) :=
    Fintype.ofFinite _
  let v := taggedCanonicalVertex I copies P₀.1
  let p₀ : VertexPresentation I copies v := ⟨P₀.1, rfl⟩
  let C : Submodule (ZMod 2) v.1 :=
    (presentationToComplement I copies v p₀).1
  let H : Submodule (ZMod 2) v.1 := vertexEquationSpace I copies v
  have hCompl : IsCompl H C :=
    (presentationToComplement I copies v p₀).2
  have hKleD : q.K ≤ v.1 := by
    exact P₀.2.2.trans le_sup_left
  let KD : Submodule (ZMod 2) v.1 := q.K.comap v.1.subtype
  have hKDleC : KD ≤ C := by
    intro x hx
    exact P₀.2.2 hx
  let KC : Submodule (ZMod 2) C := KD.comap C.subtype
  have hKCmap : KC.map C.subtype = KD := by
    simpa only [KC, Submodule.map_comap_subtype,
      inf_of_le_right hKDleC]
  have hCdim : Module.finrank (ZMod 2) C = 2 * h := by
    have hLle : P₀.1.L ≤ v.1 := le_sup_left
    change Module.finrank (ZMod 2) (P₀.1.L.comap v.1.subtype) = 2 * h
    rw [(Submodule.comapSubtypeEquivOfLe hLle).finrank_eq]
    exact P₀.1.finrank_L
  have hKDdim : Module.finrank (ZMod 2) KD = t := by
    change Module.finrank (ZMod 2) (q.K.comap v.1.subtype) = t
    rw [(Submodule.comapSubtypeEquivOfLe hKleD).finrank_eq]
    exact q.finrank_K
  have hKCdim : Module.finrank (ZMod 2) KC = t := by
    change Module.finrank (ZMod 2) (KD.comap C.subtype) = t
    rw [(Submodule.comapSubtypeEquivOfLe hKDleC).finrank_eq]
    exact hKDdim
  have hHdim : Module.finrank (ZMod 2) H = J :=
    vertexEquationSpace_dim I copies v
  let e := presentationComplementEquiv I copies v
  have hiff (P : VertexPresentation I copies v) :
      q.K ≤ P.1.L ↔
      KC.map C.subtype ≤ (e P).1 := by
    rw [hKCmap]
    change q.K ≤ P.1.L ↔ KD ≤ P.1.L.comap v.1.subtype
    constructor
    · intro h x hx
      exact h hx
    · intro h x hx
      let y : v.1 := ⟨x, hKleD hx⟩
      exact h (show y ∈ KD from hx)
  calc
    Fintype.card {P : VertexPresentation I copies v // q.K ≤ P.1.L} =
        Fintype.card
          {L : {M : Submodule (ZMod 2) v.1 // IsCompl H M} //
            KC.map C.subtype ≤ L.1} :=
      Fintype.card_congr (e.subtypeEquiv hiff)
    _ = 2 ^ ((Module.finrank (ZMod 2) C - Module.finrank (ZMod 2) KC) *
        Module.finrank (ZMod 2) H) :=
      card_conditional_complements H C hCompl KC
    _ = 2 ^ (J * (2 * h - t)) := by
      rw [hCdim, hKCdim, hHdim, Nat.mul_comm]

end
end PvNP.RealizableHardness.ActualTaggedConditionalDomainCollision
