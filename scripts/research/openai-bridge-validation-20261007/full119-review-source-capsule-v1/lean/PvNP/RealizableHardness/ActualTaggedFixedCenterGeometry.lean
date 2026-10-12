import PvNP.RealizableHardness.ActualFinite3LinSource
import PvNP.RealizableHardness.TaggedFinite3LinSource
import PvNP.RealizableHardness.ActualStarSpanIntersection
import Mathlib.LinearAlgebra.Projection

/-! A source-specific fixed-center geometry spike for the semantic tagged copy.
The center is the stored ambient `q.K`; projection into an arbitrary complement
is used only to select leaf domains. This module does not define a star test or
table acceptance. A later fixed global table must be restricted on `q.K` inside
the proved leaf domain, rather than on a freshly sampled complement center. -/

namespace PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.Finite3LinSource

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance (I : Instance N m) : DecidableEq I.RowId := Classical.decEq _
local instance (I : Instance N m) : DecidableEq I.GlobalVar := inferInstance

abbrev TaggedRow := Fin copies × I.RowId
abbrev TaggedVar := Fin copies × I.GlobalVar
abbrev TaggedAmbient := TaggedVar I copies → ZMod 2

def taggedSource :=
  (Finite3LinSource.ofActual I).taggedCopy copies

theorem taggedSource_support_card (r : TaggedRow I copies) :
    ((taggedSource I copies).support r).card = 3 := by
  classical
  rcases r with ⟨k, e⟩
  rw [taggedSource, taggedCopy_support]
  rw [Finset.card_image_of_injective]
  · rw [Finite3LinSource.ofActual_support]
    exact I.support_card e
  · intro x y h
    exact congrArg Prod.snd h

structure TaggedQuestionCenter (J t : Nat) where
  U : Finset (TaggedRow I copies)
  goodU : GoodQuestion (taggedSource I copies).support U
  card_U : U.card = J
  K : Submodule (ZMod 2) (TaggedAmbient I copies)
  K_le : K ≤ coordinateSpace (taggedSource I copies).support U
  finrank_K : Module.finrank (ZMod 2) K = t
  transverse : K ⊓ equationSpan (taggedSource I copies).support U = ⊥

variable {J t : Nat}

def equationSpanOf (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  equationSpan (taggedSource I copies).support q.U

def coordinateSpaceOf (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  coordinateSpace (taggedSource I copies).support q.U

def equationInCoordinate (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (coordinateSpaceOf I copies q) :=
  (equationSpanOf I copies q).comap (coordinateSpaceOf I copies q).subtype

noncomputable def transverseComplement (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (coordinateSpaceOf I copies q) :=
  Classical.choose (Submodule.exists_isCompl (equationInCoordinate I copies q))

theorem transverseComplement_isCompl (q : TaggedQuestionCenter I copies J t) :
    IsCompl (equationInCoordinate I copies q) (transverseComplement I copies q) :=
  Classical.choose_spec (Submodule.exists_isCompl (equationInCoordinate I copies q))

def centerInCoordinate (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (coordinateSpaceOf I copies q) :=
  q.K.comap (coordinateSpaceOf I copies q).subtype

def projectedCenter (q : TaggedQuestionCenter I copies J t) :
    Submodule (ZMod 2) (transverseComplement I copies q) :=
  (centerInCoordinate I copies q).map
    ((transverseComplement I copies q).projectionOnto
      (equationInCoordinate I copies q)
      (transverseComplement_isCompl I copies q).symm)

def complementToAmbient (q : TaggedQuestionCenter I copies J t)
    (L : Submodule (ZMod 2) (transverseComplement I copies q)) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  (L.map (transverseComplement I copies q).subtype).map
    (coordinateSpaceOf I copies q).subtype

/-- The ambient fixed center lies in each selected leaf domain `H_U + L`.
It need not lie in the selected transverse complement itself. -/
theorem tagged_fixedCenter_le_leafDomain
    (q : TaggedQuestionCenter I copies J t)
    (L : Submodule (ZMod 2) (transverseComplement I copies q))
    (hKL : projectedCenter I copies q ≤ L) :
    q.K ≤ equationSpanOf I copies q ⊔ complementToAmbient I copies q L := by
  intro x hx
  let xc : coordinateSpaceOf I copies q := ⟨x, q.K_le hx⟩
  let pc : transverseComplement I copies q :=
    (transverseComplement I copies q).projectionOnto
      (equationInCoordinate I copies q)
      (transverseComplement_isCompl I copies q).symm xc
  have hp : pc ∈ L := by
    apply hKL
    apply Submodule.mem_map.mpr
    exact ⟨xc, hx, rfl⟩
  have hpA : (pc : TaggedAmbient I copies) ∈ complementToAmbient I copies q L := by
    apply Submodule.mem_map.mpr
    refine ⟨(pc : coordinateSpaceOf I copies q), ?_, rfl⟩
    exact Submodule.mem_map.mpr ⟨pc, hp, rfl⟩
  have hdiff : xc - (pc : coordinateSpaceOf I copies q) ∈
      equationInCoordinate I copies q :=
    (transverseComplement I copies q).sub_projection_mem
      (transverseComplement_isCompl I copies q).symm xc
  have hH : x - (pc : TaggedAmbient I copies) ∈ equationSpanOf I copies q := hdiff
  have hsum : x = (x - (pc : TaggedAmbient I copies)) + (pc : TaggedAmbient I copies) := by
    abel
  rw [hsum]
  exact add_mem ((le_sup_left : equationSpanOf I copies q ≤
    equationSpanOf I copies q ⊔ complementToAmbient I copies q L) hH)
    ((le_sup_right : complementToAmbient I copies q L ≤
      equationSpanOf I copies q ⊔ complementToAmbient I copies q L) hpA)

end
end PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
