import PvNP.RealizableHardness.ActualLeafCenterRestriction

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

instance leafVertexFinite : Finite (LeafVertex I J h) := by
  let : Finite (Submodule (ZMod 2) (I.GlobalVar → ZMod 2)) :=
    Finite.of_injective (fun Q => (Q : Set (I.GlobalVar → ZMod 2))) SetLike.coe_injective
  unfold LeafVertex
  infer_instance

noncomputable instance leafVertexFintype : Fintype (LeafVertex I J h) :=
  Fintype.ofFinite _

/-- Equivalence class of `v` under `LeafVertex.Rel`. -/
def relClass (v : LeafVertex I J h) : Finset (LeafVertex I J h) :=
  Finset.univ.filter (fun w => LeafVertex.Rel v w)

theorem mem_relClass_iff {v w : LeafVertex I J h} :
    w ∈ relClass v ↔ LeafVertex.Rel v w := by
  simp [relClass]

theorem relClass_nonempty (v : LeafVertex I J h) : (relClass v).Nonempty :=
  ⟨v, mem_relClass_iff.mpr (LeafVertex.Rel.refl v)⟩

/-- Restriction to a shared center is unchanged by transport along the class. -/
theorem restrictToCenter_class_invariant
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φ : LeafLabel v) :
    restrictToCenter Cw (transportedLeafLabel hvw φ) =
      LinearMap.comp (restrictToCenter Cv φ)
        (Submodule.inclusion (le_of_eq hK.symm)) :=
  restrictToCenter_transport hvw Cv Cw hK φ

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
