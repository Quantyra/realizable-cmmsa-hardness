import PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw

/-! Nonempty tagged center and raw transverse leaf fibers under the manuscript
dimension inequalities. The final theorem instantiates the ordered raw-table
representative comparison; it makes no numerical NO-soundness claim. -/

namespace PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualSourceStarLaw
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

private def supportOf {J t : Nat} (q : TaggedQuestionCenter I copies J t) :
    Finset (TaggedVar I copies) :=
  questionSupport (taggedSource I copies).support q.U

private noncomputable def taggedCoordinateEquiv {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    coordinateSpaceOf I copies q ≃ₗ[ZMod 2]
      ((x : ↥(supportOf I copies q)) → ZMod 2) := by
  let S := supportOf I copies q
  let f : coordinateSpaceOf I copies q →ₗ[ZMod 2] ((x : ↥S) → ZMod 2) :=
    { toFun := fun v x => v.1 x.1
      map_add' := by intro x y; funext z; simp
      map_smul' := by intro a x; funext z; simp }
  let g : ((x : ↥S) → ZMod 2) →ₗ[ZMod 2] coordinateSpaceOf I copies q :=
    { toFun := fun v =>
        ⟨fun x => if hx : x ∈ S then v ⟨x, hx⟩ else 0, by
          intro x hx
          change (if h : x ∈ S then v ⟨x, h⟩ else 0) = 0
          have hxS : x ∉ S := by simpa [S, supportOf] using hx
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
        · simp [f, g, hx, v.2 x (by simpa [S, supportOf] using hx)]
      right_inv := by
        intro v; funext x; simp [f, g] }

private theorem taggedSupport_card {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    (supportOf I copies q).card = 3 * J := by
  classical
  rw [supportOf, questionSupport, Finset.card_biUnion]
  · simp_rw [taggedSource_support_card I copies]
    simp [q.card_U, Nat.mul_comm]
  · intro e he f hf hne
    exact q.goodU.1 he hf hne

theorem taggedCoordinate_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (coordinateSpaceOf I copies q) = 3 * J := by
  rw [LinearEquiv.finrank_eq (taggedCoordinateEquiv I copies q)]
  simp [taggedSupport_card I copies q]

private theorem taggedEquation_le_coordinate {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    equationSpanOf I copies q ≤ coordinateSpaceOf I copies q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  exact equationVector_mem_coordinateSpace
    (taggedSource I copies).support q.U e he

theorem taggedEquation_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (equationSpanOf I copies q) = J := by
  change Module.finrank (ZMod 2) (equationSpan (taggedSource I copies).support q.U) = J
  calc
    _ = q.U.card := equationSpan_finrank_eq_card
      (taggedSource I copies).support (taggedSource_support_card I copies)
      q.U q.goodU
    _ = J := q.card_U

theorem taggedEquationInCoordinate_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (equationInCoordinate I copies q) = J := by
  unfold equationInCoordinate
  rw [(Submodule.comapSubtypeEquivOfLe
    (taggedEquation_le_coordinate I copies q)).finrank_eq]
  exact taggedEquation_finrank I copies q

theorem taggedComplement_finrank {J t : Nat}
    (q : TaggedQuestionCenter I copies J t) :
    Module.finrank (ZMod 2) (transverseComplement I copies q) = 2 * J := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := coordinateSpaceOf I copies q)
    (equationInCoordinate I copies q) (transverseComplement I copies q)
  have hc := transverseComplement_isCompl I copies q
  rw [hc.codisjoint.eq_top, finrank_top (ZMod 2) (coordinateSpaceOf I copies q),
    hc.disjoint.eq_bot, finrank_bot (ZMod 2) (coordinateSpaceOf I copies q), add_zero,
    taggedEquationInCoordinate_finrank I copies q,
    taggedCoordinate_finrank I copies q] at hs
  omega

/-- Every eligible tagged row set has a transverse center of each rank at
most `2J`. -/
theorem taggedCenterOver_nonempty {J t : Nat} (U : TaggedGoodU I copies J)
    (ht : t ≤ 2 * J) : Nonempty (TaggedCenterOver I copies t U) := by
  let q : TaggedQuestionCenter I copies J 0 :=
    { U := U.1
      goodU := U.2.1
      card_U := U.2.2
      K := ⊥
      K_le := bot_le
      finrank_K := finrank_bot _ _
      transverse := by simp }
  let C := transverseComplement I copies q
  letI : Finite C := Finite.of_injective Subtype.val Subtype.val_injective
  have hC : Module.finrank (ZMod 2) C = 2 * J :=
    taggedComplement_finrank I copies q
  have hgrass : Nonempty (Grass C t) := by
    apply Fintype.card_pos_iff.mp
    rw [card_grass, hC]
    exact gaussian_pos ht
  let g : Grass C t := Classical.choice hgrass
  let K : Submodule (ZMod 2) (TaggedAmbient I copies) :=
    (g.val.map C.subtype).map (coordinateSpaceOf I copies q).subtype
  refine ⟨⟨K, ?_, ?_, ?_⟩⟩
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  · dsimp [K]
    rw [Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
    exact g.property
  · apply le_antisymm
    · intro x hx
      rcases Submodule.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
      rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
      have he : (z : coordinateSpaceOf I copies q) ∈
          equationInCoordinate I copies q := hx.2
      have hb : (z : coordinateSpaceOf I copies q) ∈
          equationInCoordinate I copies q ⊓ C := ⟨he, z.2⟩
      rw [(transverseComplement_isCompl I copies q).disjoint.eq_bot] at hb
      simpa using hb
    · exact bot_le

/-- The center is kept in the raw transverse increment `L` itself. In
particular the eventual leaf domain contains the stored center. -/
theorem taggedLeafOver_nonempty {J t h : Nat}
    (U : TaggedGoodU I copies J) (K : TaggedCenterOver I copies t U)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)) := by
  let q := questionOf I copies U K
  let E := equationInCoordinate I copies q
  let KC : Submodule (ZMod 2) (coordinateSpaceOf I copies q) :=
    K.1.comap (coordinateSpaceOf I copies q).subtype
  have hKC : Module.finrank (ZMod 2) KC = t := by
    have hqKle : K.1 ≤ coordinateSpaceOf I copies q := by
      simpa only [q, questionOf, coordinateSpaceOf] using K.2.1
    dsimp [KC]
    rw [(Submodule.comapSubtypeEquivOfLe hqKle).finrank_eq]
    exact K.2.2.1
  have hdis : Disjoint KC E := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    have h : (x : TaggedAmbient I copies) ∈
        K.1 ⊓ equationSpanOf I copies q := ⟨hx.1, hx.2⟩
    change (x : TaggedAmbient I copies) ∈
      K.1 ⊓ equationSpan (taggedSource I copies).support U.1 at h
    rw [K.2.2.2] at h
    exact Subtype.ext (by simpa using h)
  obtain ⟨C, hKC_le, hcompl⟩ := hdis.exists_isCompl
  letI : Finite C := Finite.of_injective Subtype.val Subtype.val_injective
  have hC : Module.finrank (ZMod 2) C = 2 * J := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (K := ZMod 2) (V := coordinateSpaceOf I copies q) E C
    rw [hcompl.symm.codisjoint.eq_top,
      finrank_top (ZMod 2) (coordinateSpaceOf I copies q),
      hcompl.symm.disjoint.eq_bot,
      finrank_bot (ZMod 2) (coordinateSpaceOf I copies q), add_zero,
      taggedEquationInCoordinate_finrank I copies q,
      taggedCoordinate_finrank I copies q] at hs
    omega
  let KC' : Submodule (ZMod 2) C := KC.comap C.subtype
  have hKC' : Module.finrank (ZMod 2) KC' = t := by
    rw [(Submodule.comapSubtypeEquivOfLe hKC_le).finrank_eq]
    exact hKC
  let g : Grass C t := ⟨KC', hKC'⟩
  have hExt : Nonempty (Extension g (2 * h)) :=
    extension_nonempty g ht (by omega : 2 * h ≤ Module.finrank (ZMod 2) C)
  let Lg := (Classical.choice hExt).1
  let L : Submodule (ZMod 2) (TaggedAmbient I copies) :=
    (Lg.val.map C.subtype).map (coordinateSpaceOf I copies q).subtype
  let P : TaggedPresentedLeaf I copies J h :=
    { U := q.U
      goodU := q.goodU
      card_U := q.card_U
      L := L
      L_le := by
        intro x hx
        rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact y.2
      finrank_L := by
        dsimp [L]
        rw [Submodule.finrank_map_subtype_eq,
          Submodule.finrank_map_subtype_eq]
        exact Lg.property
      transverse := by
        apply le_antisymm
        · intro x hx
          rcases Submodule.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
          rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
          have he : (z : coordinateSpaceOf I copies q) ∈ E := hx.2
          have hc : (z : coordinateSpaceOf I copies q) ∈ C := z.2
          have hb : (z : coordinateSpaceOf I copies q) ∈ E ⊓ C := ⟨he, hc⟩
          rw [hcompl.symm.disjoint.eq_bot] at hb
          simpa using hb
        · exact bot_le }
  refine ⟨⟨P, rfl, ?_⟩⟩
  intro x hx
  have hxc : (⟨x, K.2.1 hx⟩ : coordinateSpaceOf I copies q) ∈ KC := hx
  have hxcC : (⟨x, K.2.1 hx⟩ : coordinateSpaceOf I copies q) ∈ C :=
    hKC_le hxc
  have hg : (⟨⟨x, K.2.1 hx⟩, hxcC⟩ : C) ∈ Lg.val :=
    (Classical.choice hExt).2 hxc
  apply Submodule.mem_map.mpr
  refine ⟨(⟨x, K.2.1 hx⟩ : coordinateSpaceOf I copies q), ?_, rfl⟩
  exact Submodule.mem_map.mpr
    ⟨(⟨⟨x, K.2.1 hx⟩, hxcC⟩ : C), hg, rfl⟩

/-- A normalized complete ordered star law at the explicit padding and
dimension guards, with no caller-supplied fiber witnesses. -/
def paddedOrderedStarLaw {J t h k T : Nat}
    (hT : 4 ≤ T) (hm : 0 < m)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    ActualFiniteLaw.FiniteLaw
      (TaggedSample I (ActualQuestionMassBridge.actualPaddingCopies J T) J t h k) := by
  let copies := ActualQuestionMassBridge.actualPaddingCopies J T
  letI : Nonempty (TaggedGoodU I copies J) :=
    taggedGoodU_nonempty_of_padding I J T hT hm
  exact orderedStarLaw I copies J
    (fun U => taggedCenterOver_nonempty I copies U (by omega))
    (fun U K => taggedLeafOver_nonempty I copies U K ht hh)

/-- Manuscript-style copy padding and dimension bounds discharge both
sampler nonemptiness assumptions in the fixed-table selection comparison. -/
theorem ordered_sample_exists_selected_of_padding
    {J t h k T : Nat} (hT : 4 ≤ T) (hm : 0 < m)
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I (ActualQuestionMassBridge.actualPaddingCopies J T))
    (raw : TaggedRawVertexTable I
      (ActualQuestionMassBridge.actualPaddingCopies J T) J h) :
    let copies := ActualQuestionMassBridge.actualPaddingCopies J T
    ∃ s : TaggedRepresentativeChoice I copies J h,
      taggedPhysicalMass I copies
        (paddedOrderedStarLaw I (k := k) hT hm ht hh).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C raw ≤
      taggedSelectedMass I copies
        (paddedOrderedStarLaw I (k := k) hT hm ht hh).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C raw s +
      taggedClassCollisionMass I copies
        (paddedOrderedStarLaw I (k := k) hT hm ht hh).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) := by
  let copies := ActualQuestionMassBridge.actualPaddingCopies J T
  letI : Nonempty (TaggedGoodU I copies J) :=
    taggedGoodU_nonempty_of_padding I J T hT hm
  simpa only [paddedOrderedStarLaw] using ordered_sample_exists_selected I copies J
    (fun U => taggedCenterOver_nonempty I copies U (by omega))
    (fun U K => taggedLeafOver_nonempty I copies U K ht hh) C raw

end
end PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
