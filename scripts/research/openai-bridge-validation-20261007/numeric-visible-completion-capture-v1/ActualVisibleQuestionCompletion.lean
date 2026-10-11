import PvNP.RealizableHardness.ActualTaggedRowDeletion
import PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence

/-! The second prover's completion and table use only its visible variable
set and the globally fixed selected table. No original question is an input. -/
namespace PvNP.RealizableHardness.ActualVisibleQuestionCompletion

open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedFixedCenterGeometry ActualTaggedConcreteStarLaw
open ActualTaggedPresentedSelection ActualTaggedRowDeletion ActualTaggedCommonLeafCoherence
open ActualTaggedSelectedDecoderBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N rows : Nat} (I : Instance N rows) (copies J : Nat)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

def Reachable (X : Finset (TaggedVar I copies)) : Prop :=
  ∃ U : TaggedGoodU I copies J,
    X ⊆ questionSupport (taggedSource I copies).support U.1

def completion (X : Finset (TaggedVar I copies)) (hX : Reachable I copies J X) :
    TaggedGoodU I copies J := Classical.choose hX

theorem completion_contains (X : Finset (TaggedVar I copies))
    (hX : Reachable I copies J X) :
    X ⊆ questionSupport (taggedSource I copies).support (completion I copies J X hX).1 :=
  Classical.choose_spec hX

theorem completion_eq_of_visible_eq (X Y : Finset (TaggedVar I copies))
    (hX : Reachable I copies J X) (hY : Reachable I copies J Y) (hXY : X = Y) :
    completion I copies J X hX = completion I copies J Y hY := by
  subst Y
  rfl

def retainedVariables (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U) :
    Finset (TaggedVar I copies) :=
  Finset.univ.filter (keptActualVariable I copies U s)

theorem retainedVariables_subset_support
    (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U) :
    retainedVariables I copies J U s ⊆ questionSupport (taggedSource I copies).support U.1 := by
  intro x hx
  obtain ⟨e, i, hrow, _hkeep⟩ := (Finset.mem_filter.mp hx).2
  apply Finset.mem_biUnion.mpr
  refine ⟨e.1, e.2, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hrow⟩

theorem retainedVariables_reachable
    (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U) :
    Reachable I copies J (retainedVariables I copies J U s) :=
  ⟨U, retainedVariables_subset_support I copies J U s⟩

/-- The visible coordinate space is indexed by the retained variables alone. -/
def visibleCoordinateSpace (X : Finset (TaggedVar I copies)) :
    Submodule (ZMod 2) (TaggedAmbient I copies) where
  carrier := {v | ∀ x, x ∉ X → v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro c v hv x hx; simp [hv x hx]

theorem visibleCoordinateSpace_le_question
    (X : Finset (TaggedVar I copies)) (U : TaggedGoodU I copies J)
    (hXU : X ⊆ questionSupport (taggedSource I copies).support U.1) :
    visibleCoordinateSpace I copies X ≤ coordinateSpace (taggedSource I copies).support U.1 := by
  intro v hv x hx
  exact hv x (fun hX => hx (hXU hX))

/-- The visible-space representation is exactly the original retained space
embedded into the global variable ambient, for every individual draw. -/
theorem actualRetained_map_visible
    (U : TaggedGoodU I copies J) (s : ActualRowDraw I copies U) :
    (actualRetained I copies U s).map (ActualCoordinateSpace I copies U).subtype =
      visibleCoordinateSpace I copies (retainedVariables I copies J U s) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro x hx
    apply hw x
    intro hkeep
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hkeep⟩)
  · intro hv
    have hU := visibleCoordinateSpace_le_question I copies J
      (retainedVariables I copies J U s) U (retainedVariables_subset_support I copies J U s)
    refine ⟨⟨v, hU hv⟩, ?_, rfl⟩
    intro x hx
    apply hv x
    intro hmem
    exact hx (Finset.mem_filter.mp hmem).2

def visiblePresentation {h : Nat}
    (X : Finset (TaggedVar I copies)) (U : TaggedGoodU I copies J)
    (hXU : X ⊆ questionSupport (taggedSource I copies).support U.1)
    (L : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hLX : L ≤ visibleCoordinateSpace I copies X)
    (hdim : Module.finrank (ZMod 2) L = 2*h)
    (htrans : L ⊓ equationSpan (taggedSource I copies).support U.1 = ⊥) :
    TaggedPresentedLeaf I copies J h where
  U := U.1
  goodU := U.2.1
  card_U := U.2.2
  L := L
  L_le := hLX.trans (visibleCoordinateSpace_le_question I copies J X U hXU)
  finrank_L := hdim
  transverse := htrans

/-- A total table for every visible set, including impossible questions and
nontransverse leaf entries. Its only fixed auxiliary data are the global raw
table and the one globally selected representative per class. -/
def visibleLeafTable {h : Nat}
    (T : TaggedRawVertexTable I copies J h) (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies))
    (L : Submodule (ZMod 2) (TaggedAmbient I copies)) : Module.Dual (ZMod 2) L :=
  if hX : Reachable I copies J X then
    if L ⊓ equationSpan (taggedSource I copies).support (completion I copies J X hX).1 = ⊥ then
      (taggedSelectedDomainTable I copies T choice
        (L ⊔ equationSpan (taggedSource I copies).support (completion I copies J X hX).1)).comp
          (Submodule.inclusion le_sup_left)
    else 0
  else 0

theorem visibleLeafTable_zero_of_unreachable {h : Nat}
    (T : TaggedRawVertexTable I copies J h) (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies)) (hX : ¬ Reachable I copies J X)
    (L : Submodule (ZMod 2) (TaggedAmbient I copies)) :
    visibleLeafTable I copies J T choice X L = 0 := by
  simp only [visibleLeafTable, dif_neg hX]

theorem visibleLeafTable_zero_of_nontransverse {h : Nat}
    (T : TaggedRawVertexTable I copies J h) (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies)) (hX : Reachable I copies J X)
    (L : Submodule (ZMod 2) (TaggedAmbient I copies))
    (htrans : L ⊓ equationSpan (taggedSource I copies).support
      (completion I copies J X hX).1 ≠ ⊥) :
    visibleLeafTable I copies J T choice X L = 0 := by
  simp only [visibleLeafTable, dif_pos hX, if_neg htrans]

theorem visibleLeafTable_eq_canonical_restriction {h : Nat}
    (T : TaggedRawVertexTable I copies J h) (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies)) (hX : Reachable I copies J X)
    (L : Submodule (ZMod 2) (TaggedAmbient I copies))
    (htrans : L ⊓ equationSpan (taggedSource I copies).support
      (completion I copies J X hX).1 = ⊥) (x : L) :
    visibleLeafTable I copies J T choice X L x =
      taggedSelectedDomainTable I copies T choice
        (L ⊔ equationSpan (taggedSource I copies).support (completion I copies J X hX).1)
        ⟨x.1, le_sup_left x.2⟩ := by
  simp only [visibleLeafTable, dif_pos hX, if_pos htrans, LinearMap.comp_apply]

/-- The same global canonical label is recovered on every leaf transverse
to both legitimate questions. No statement covers exceptional entries. -/
theorem visibleLeafTable_agrees_with_original {h : Nat}
    (T : TaggedRawVertexTable I copies J h) (choice : TaggedRepresentativeChoice I copies J h)
    (X : Finset (TaggedVar I copies)) (U : TaggedGoodU I copies J)
    (hXU : X ⊆ questionSupport (taggedSource I copies).support U.1)
    (L : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hLX : L ≤ visibleCoordinateSpace I copies X)
    (hdim : Module.finrank (ZMod 2) L = 2*h)
    (hU : L ⊓ equationSpan (taggedSource I copies).support U.1 = ⊥)
    (h0 : L ⊓ equationSpan (taggedSource I copies).support
      (completion I copies J X ⟨U, hXU⟩).1 = ⊥) (x : L) :
    visibleLeafTable I copies J T choice X L x =
      taggedSelectedDomainTable I copies T choice
        (L ⊔ equationSpan (taggedSource I copies).support U.1) ⟨x.1, le_sup_left x.2⟩ := by
  let hX : Reachable I copies J X := ⟨U, hXU⟩
  let U0 := completion I copies J X hX
  let P := visiblePresentation I copies J X U hXU L hLX hdim hU
  let Q := visiblePresentation I copies J X U0 (completion_contains I copies J X hX)
    L hLX hdim h0
  rw [visibleLeafTable_eq_canonical_restriction I copies J T choice X hX L h0 x]
  exact (canonical_table_agrees_on_shared_leaf I copies T choice P Q rfl x).symm

end
end PvNP.RealizableHardness.ActualVisibleQuestionCompletion
