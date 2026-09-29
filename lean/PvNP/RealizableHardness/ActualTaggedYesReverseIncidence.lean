import PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw

/-! Reverse incidence for the manuscript's YES sampler: the number of
eligible stored centers inside a fixed presented leaf is independent of
the leaf and of its copied row question. -/

namespace PvNP.RealizableHardness.ActualTaggedYesReverseIncidence

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

def CentersInLeaf {J t h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :=
  {K : TaggedCenterOver I copies t
      (⟨P.U, P.goodU, P.card_U⟩ : TaggedGoodU I copies J) // K.1 ≤ P.L}

noncomputable def centersInLeafEquivGrass {J t h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    CentersInLeaf I copies (t := t) P ≃ Grass P.L t where
  toFun K := ⟨K.1.1.comap P.L.subtype,
    by rw [(Submodule.comapSubtypeEquivOfLe K.2).finrank_eq]; exact K.1.2.2.1⟩
  invFun G := by
    refine ⟨⟨G.1.map P.L.subtype, ?_, ?_, ?_⟩, ?_⟩
    · exact (Submodule.map_le_iff_le_comap).2 (by
        intro x hx
        exact P.L_le x.property)
    · simpa [Submodule.finrank_map_subtype_eq] using G.2
    · apply le_antisymm ?_ bot_le
      exact le_trans (inf_le_inf_right _ (Submodule.map_subtype_le P.L G.1))
        (le_of_eq P.transverse)
    · exact Submodule.map_subtype_le P.L G.1
  left_inv := by
    intro K
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by
      intro x hx
      exact ⟨⟨x, K.2 hx⟩, rfl⟩)
  right_inv := by
    intro G
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective G.1

noncomputable instance centersInLeafFintype {J t h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    Fintype (CentersInLeaf I copies (t := t) P) := by
  letI : Finite P.L := Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofEquiv _ (centersInLeafEquivGrass I copies P).symm

/-- The reverse incidence has one constant multiplicity for every eligible
presented leaf, independently of the copied question and of the leaf. -/
theorem centersInLeaf_card {J t h : Nat}
    (P : TaggedPresentedLeaf I copies J h) :
    Fintype.card (CentersInLeaf I copies (t := t) P) =
      gaussian (2 * h) t := by
  classical
  letI : Finite P.L := Finite.of_injective Subtype.val Subtype.val_injective
  rw [Fintype.card_congr (centersInLeafEquivGrass I copies P), card_grass]
  rw [P.finrank_L]

end
end PvNP.RealizableHardness.ActualTaggedYesReverseIncidence
