import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
import PvNP.RealizableHardness.TripleRestrictionRank

/-! The row-coordinate frame and product law for one actual tagged good
question. The frame is a proof device, not information given to prover two.
Uncompiled; source-game marginal and decoder integration are still required. -/
namespace PvNP.RealizableHardness.ActualTaggedRowDeletion
open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualTaggedFixedCenterGeometry
open ActualTaggedConcreteStarLaw ActualStarQuestionSupport ActualStarSpanIntersection
open TripleRestrictionRank
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance : DecidableEq I.RowId := Classical.decEq _
variable {J : Nat} (U : TaggedGoodU I copies J)

abbrev ActualCoordinateSpace := coordinateSpace (taggedSource I copies).support U.1
abbrev ActualRowDraw := ↥U.1 → BlockChoice

def rowIndexEquiv : Fin J ≃ ↥U.1 :=
  Fintype.equivOfCardEq (by simpa using U.2.2.symm)

def rowVariable (c : Coord J) :=
  (taggedSource I copies).row (rowIndexEquiv I copies U c.1).1 c.2

private theorem row_mem_support (e : TaggedRow I copies) (i : Fin 3) :
    (taggedSource I copies).row e i ∈ (taggedSource I copies).support e :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem rowVariable_mem_support (c : Coord J) :
    rowVariable I copies U c ∈ questionSupport (taggedSource I copies).support U.1 :=
  Finset.mem_biUnion.mpr
    ⟨(rowIndexEquiv I copies U c.1).1, (rowIndexEquiv I copies U c.1).2,
      row_mem_support I copies _ c.2⟩

theorem rowVariable_injective : Function.Injective (rowVariable I copies U) := by
  intro c d hcd
  have hrows : (rowIndexEquiv I copies U c.1).1 =
      (rowIndexEquiv I copies U d.1).1 := by
    by_contra hne
    have hd := U.2.1.1 (rowIndexEquiv I copies U c.1).2
      (rowIndexEquiv I copies U d.1).2 hne
    have hc := row_mem_support I copies (rowIndexEquiv I copies U c.1).1 c.2
    have hd' := row_mem_support I copies (rowIndexEquiv I copies U d.1).1 d.2
    change rowVariable I copies U c ∈ _ at hc
    change rowVariable I copies U d ∈ _ at hd'
    rw [← hcd] at hd'
    exact Finset.disjoint_left.mp hd hc hd'
  have hfirst : c.1 = d.1 :=
    (rowIndexEquiv I copies U).injective (Subtype.ext hrows)
  have hsecond : c.2 = d.2 := by
    apply (taggedSource I copies).row_injective (rowIndexEquiv I copies U d.1).1
    simpa only [rowVariable, hfirst] using hcd
  exact Prod.ext hfirst hsecond

def rowVariableEquiv : Coord J ≃
    ↥(questionSupport (taggedSource I copies).support U.1) :=
  Equiv.ofBijective
    (fun c => ⟨rowVariable I copies U c, rowVariable_mem_support I copies U c⟩)
    ⟨by
      intro c d hcd
      exact rowVariable_injective I copies U (congrArg Subtype.val hcd), by
      intro v
      rcases Finset.mem_biUnion.mp v.2 with ⟨e, he, hve⟩
      rcases Finset.mem_image.mp hve with ⟨i, _, hiv⟩
      refine ⟨((rowIndexEquiv I copies U).symm ⟨e, he⟩, i), ?_⟩
      apply Subtype.ext
      simpa only [rowVariable, Equiv.apply_symm_apply] using hiv⟩

/-- Evaluate the actual supported vector at the variables of the enumerated
rows. Both row membership and position within each row are preserved. -/
def actualRowCoordinateEquiv : ActualCoordinateSpace I copies U ≃ₗ[ZMod 2] Vector J where
  toFun v c := v.1 (rowVariable I copies U c)
  invFun w :=
    ⟨fun x => if hx : x ∈ questionSupport (taggedSource I copies).support U.1 then
      w ((rowVariableEquiv I copies U).symm ⟨x, hx⟩) else 0, by
        intro x hx
        simp [hx]⟩
  map_add' := by intro v w; rfl
  map_smul' := by intro a v; rfl
  left_inv := by
    intro v
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ questionSupport (taggedSource I copies).support U.1
    · simp only [dif_pos hx]
      have hv := congrArg Subtype.val
        ((rowVariableEquiv I copies U).apply_symm_apply ⟨x, hx⟩)
      change rowVariable I copies U ((rowVariableEquiv I copies U).symm ⟨x, hx⟩) = x at hv
      rw [hv]
    · simp only [dif_neg hx]
      exact (v.2 x hx).symm
  right_inv := by
    intro w
    funext c
    simp only [dif_pos (rowVariable_mem_support I copies U c)]
    change w ((rowVariableEquiv I copies U).symm (rowVariableEquiv I copies U c)) = w c
    rw [Equiv.symm_apply_apply]

def rowDrawEquiv : ActualRowDraw I copies U ≃ Draw J where
  toFun s j := s (rowIndexEquiv I copies U j)
  invFun d e := d ((rowIndexEquiv I copies U).symm e)
  left_inv := by intro s; funext e; simp
  right_inv := by intro d; funext j; simp

/-- A variable is retained precisely when its actual source row keeps all
positions or keeps its specified singleton position. -/
def keptActualVariable (s : ActualRowDraw I copies U) (x : TaggedVar I copies) : Prop :=
  ∃ e : ↥U.1, ∃ i : Fin 3,
    (taggedSource I copies).row e.1 i = x ∧ (s e = none ∨ s e = some i)

theorem keptActualVariable_rowVariable_iff
    (s : ActualRowDraw I copies U) (c : Coord J) :
    keptActualVariable I copies U s (rowVariable I copies U c) ↔
      kept (rowDrawEquiv I copies U s) c := by
  constructor
  · rintro ⟨e, i, hvar, hkeep⟩
    let j := (rowIndexEquiv I copies U).symm e
    have hcoord : (j, i) = c := by
      apply rowVariable_injective I copies U
      simpa only [rowVariable, j, Equiv.apply_symm_apply] using hvar
    have he : e = rowIndexEquiv I copies U c.1 := by
      have hj := congrArg Prod.fst hcoord
      simpa only [j, Equiv.apply_symm_apply] using
        congrArg (rowIndexEquiv I copies U) hj
    have hi : i = c.2 := congrArg Prod.snd hcoord
    simpa only [kept, rowDrawEquiv, he, hi] using hkeep
  · intro hkeep
    exact ⟨rowIndexEquiv I copies U c.1, c.2, rfl, hkeep⟩

def actualRetained (s : ActualRowDraw I copies U) :
    Submodule (ZMod 2) (ActualCoordinateSpace I copies U) where
  carrier := {v | ∀ x, ¬ keptActualVariable I copies U s x → v.1 x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

theorem coordinate_mem_retained_iff
    (s : ActualRowDraw I copies U) (v : ActualCoordinateSpace I copies U) :
    actualRowCoordinateEquiv I copies U v ∈ retained (rowDrawEquiv I copies U s) ↔
      v ∈ actualRetained I copies U s := by
  constructor
  · intro hv x hx
    by_cases hxs : x ∈ questionSupport (taggedSource I copies).support U.1
    · let c := (rowVariableEquiv I copies U).symm ⟨x, hxs⟩
      have hc : rowVariable I copies U c = x :=
        congrArg Subtype.val ((rowVariableEquiv I copies U).apply_symm_apply ⟨x, hxs⟩)
      have hn : ¬ kept (rowDrawEquiv I copies U s) c := by
        intro hk
        apply hx
        rw [← hc]
        exact (keptActualVariable_rowVariable_iff I copies U s c).mpr hk
      have hz := hv c hn
      change v.1 (rowVariable I copies U c) = 0 at hz
      simpa only [hc] using hz
    · exact v.2 x hxs
  · intro hv c hc
    apply hv (rowVariable I copies U c)
    exact fun hx => hc ((keptActualVariable_rowVariable_iff I copies U s c).mp hx)

/-- Exact retained-subspace equality for each individual deletion draw. -/
theorem actualRetained_map_coordinates (s : ActualRowDraw I copies U) :
    (actualRetained I copies U s).map (actualRowCoordinateEquiv I copies U).toLinearMap =
      retained (rowDrawEquiv I copies U s) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (coordinate_mem_retained_iff I copies U s v).mpr hv
  · intro hw
    refine ⟨(actualRowCoordinateEquiv I copies U).symm w, ?_, ?_⟩
    · apply (coordinate_mem_retained_iff I copies U s _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hw
    · exact (actualRowCoordinateEquiv I copies U).apply_symm_apply w

def actualRowDrawMass (beta : Rat) (s : ActualRowDraw I copies U) : Rat :=
  ∏ e : ↥U.1, blockMass beta (s e)

theorem actualRowDrawMass_eq (beta : Rat) (s : ActualRowDraw I copies U) :
    actualRowDrawMass I copies U beta s =
      FiniteSampling.trialMass (blockMass beta) J (rowDrawEquiv I copies U s) := by
  exact (Equiv.prod_comp (rowIndexEquiv I copies U) (fun e => blockMass beta (s e))).symm

/-- Reindexing actual independent row draws preserves every event mass.
This is conditional on the fixed actual U; it does not identify the outer U
marginal or expose that U to the second prover. -/
theorem actualRowEvent_eq_coordinate_probability
    (beta : Rat) (P : Draw J → Prop) :
    (∑ s : ActualRowDraw I copies U,
      if P (rowDrawEquiv I copies U s) then actualRowDrawMass I copies U beta s else 0) =
      probability beta P := by
  simp_rw [actualRowDrawMass_eq]
  exact Equiv.sum_comp (rowDrawEquiv I copies U)
    (fun d => if P d then FiniteSampling.trialMass (blockMass beta) J d else 0)

theorem actualRowDrawMass_nonneg (beta : Rat) (hbeta : 0 ≤ beta)
    (hbeta1 : beta ≤ 1) (s : ActualRowDraw I copies U) :
    0 ≤ actualRowDrawMass I copies U beta s := by
  rw [actualRowDrawMass_eq]
  exact drawMass_nonneg beta hbeta hbeta1 _

theorem actualRowDrawMass_sum (beta : Rat) :
    ∑ s : ActualRowDraw I copies U, actualRowDrawMass I copies U beta s = 1 := by
  have h := actualRowEvent_eq_coordinate_probability I copies U beta (fun _ => True)
  simpa only [if_true, probability_univ] using h

/-- Every event of the retained coordinate subspace has the same mass under
the actual row product and the manuscript's triple restriction. -/
theorem actualRetainedEvent_eq_coordinate_probability
    (beta : Rat) (E : Submodule (ZMod 2) (Vector J) → Prop) :
    (∑ s : ActualRowDraw I copies U,
      if E ((actualRetained I copies U s).map
        (actualRowCoordinateEquiv I copies U).toLinearMap)
      then actualRowDrawMass I copies U beta s else 0) =
      probability beta (fun d => E (retained d)) := by
  simp_rw [actualRetained_map_coordinates]
  exact actualRowEvent_eq_coordinate_probability I copies U beta
    (fun d => E (retained d))

end
end PvNP.RealizableHardness.ActualTaggedRowDeletion
