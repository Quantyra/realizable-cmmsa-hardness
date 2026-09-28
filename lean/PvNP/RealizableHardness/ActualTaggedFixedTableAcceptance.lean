import PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry

/-! Fixed global-table acceptance on the semantic tagged carrier.

`Tcenter` and `Tleaf` are arguments before a question or leaf is selected. The
test uses the stored ambient `q.K`, and checks the copied row right-hand sides
on every selected full leaf domain. This is an event interface, not a claim
that the present untagged question law samples these tagged stars. -/

namespace PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance (I : Instance N m) : DecidableEq I.RowId := Classical.decEq _
local instance (I : Instance N m) : DecidableEq I.GlobalVar := inferInstance
variable {J t : Nat}

/-- A leaf is an extension of the projection of the *fixed* tagged center. -/
structure TaggedLeaf (q : TaggedQuestionCenter I copies J t) where
  L : Submodule (ZMod 2) (transverseComplement I copies q)
  containsCenter : projectedCenter I copies q ≤ L

def TaggedLeaf.domain {q : TaggedQuestionCenter I copies J t}
    (leaf : TaggedLeaf I copies q) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  equationSpanOf I copies q ⊔ complementToAmbient I copies q leaf.L

theorem TaggedLeaf.center_le_domain {q : TaggedQuestionCenter I copies J t}
    (leaf : TaggedLeaf I copies q) : q.K ≤ leaf.domain :=
  tagged_fixedCenter_le_leafDomain I copies q leaf.L leaf.containsCenter

/-- Both tables are chosen globally, before the tagged question and leaves. -/
abbrev TaggedCenterTable :=
  (K : Submodule (ZMod 2) (TaggedAmbient I copies)) → K →ₗ[ZMod 2] ZMod 2

abbrev TaggedLeafTable :=
  (D : Submodule (ZMod 2) (TaggedAmbient I copies)) → D →ₗ[ZMod 2] ZMod 2

/-- The one table label on the full domain restricts to the stored center. -/
def TaggedLeaf.restrictedLabel {q : TaggedQuestionCenter I copies J t}
    (leaf : TaggedLeaf I copies q) (Tleaf : TaggedLeafTable I copies) :
    q.K →ₗ[ZMod 2] ZMod 2 :=
  (Tleaf leaf.domain).comp (Submodule.inclusion leaf.center_le_domain)

/-- Each queried copied equation has its indicator in the full domain. -/
theorem TaggedLeaf.equation_mem_domain
    {q : TaggedQuestionCenter I copies J t}
    (leaf : TaggedLeaf I copies q) (e : TaggedRow I copies)
    (he : e ∈ q.U) :
    equationVector (taggedSource I copies).support e ∈ leaf.domain := by
  apply (le_sup_left : equationSpanOf I copies q ≤ leaf.domain)
  exact equationVector_mem_equationSpan (taggedSource I copies).support q.U e he

/-- The leaf label obeys the actual copied source right-hand sides. -/
def TaggedLeaf.respectsRows {q : TaggedQuestionCenter I copies J t}
    (leaf : TaggedLeaf I copies q) (Tleaf : TaggedLeafTable I copies) : Prop :=
  ∀ e (he : e ∈ q.U),
    (Tleaf leaf.domain)
      ⟨equationVector (taggedSource I copies).support e,
        leaf.equation_mem_domain I copies e he⟩ =
      (taggedSource I copies).rhs e

/-- One fixed-table tagged star event, with one stored center and all leaves.
The test remains meaningful for repeated leaves. -/
def taggedAccepts (Tcenter : TaggedCenterTable I copies)
    (Tleaf : TaggedLeafTable I copies)
    (q : TaggedQuestionCenter I copies J t)
    {arity : Nat} (leaves : Fin arity → TaggedLeaf I copies q) : Prop :=
  ∀ i, (leaves i).respectsRows I copies Tleaf ∧
    (leaves i).restrictedLabel I copies Tleaf = Tcenter q.K

/-- An honest global linear assignment fixes both tables once, before draws. -/
def globalCenterTable
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    TaggedCenterTable I copies :=
  fun K => f.comp K.subtype

def globalLeafTable
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2) :
    TaggedLeafTable I copies :=
  fun D => f.comp D.subtype

/-- A satisfying global linear assignment passes every tagged star sample.
The restriction proof uses the stored `q.K` inclusion, not a replacement center. -/
theorem taggedAccepts_global
    (f : TaggedAmbient I copies →ₗ[ZMod 2] ZMod 2)
    (hsat : ∀ e : TaggedRow I copies,
      f (equationVector (taggedSource I copies).support e) =
        (taggedSource I copies).rhs e)
    (q : TaggedQuestionCenter I copies J t)
    {arity : Nat} (leaves : Fin arity → TaggedLeaf I copies q) :
    taggedAccepts I copies (globalCenterTable I copies f)
      (globalLeafTable I copies f) q leaves := by
  intro i
  constructor
  · intro e he
    exact hsat e
  · ext x
    rfl

end
end PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
