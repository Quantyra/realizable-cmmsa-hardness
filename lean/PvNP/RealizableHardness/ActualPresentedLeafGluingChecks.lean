import PvNP.RealizableHardness.ActualPresentedLeafGluing

namespace PvNP.RealizableHardness.ActualPresentedLeafGluingChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualCompatibleRhsFunctional
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

#check PresentedLeaf
#check PresentedLeaf.H
#check PresentedLeaf.domain
#check PresentedLeaf.H_le_coordinateSpace
#check PresentedLeaf.H_le_domain
#check PresentedLeaf.domain_le_coordinateSpace
#check RawLeafLabel
#check RespectsAt
#check LeafVertex
#check LeafLabel
#check H_eq_of_domain_eq
#check respectsAt_iff_of_domain_eq
#check actual_existsUnique_gluedLeafRhsFunctional

#print axioms H_eq_of_domain_eq
#print axioms respectsAt_iff_of_domain_eq
#print axioms actual_existsUnique_gluedLeafRhsFunctional

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

def oneRowActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 1

def oneRowU : Finset oneRowActual.RowId := {Sum.inl 0}

theorem oneRowU_good : GoodQuestion oneRowActual.support oneRowU := by
  simp [GoodQuestion, oneRowU]

def oneRowPresented : PresentedLeaf oneRowActual 1 0 where
  U := oneRowU
  goodU := oneRowU_good
  card_U := by simp [oneRowU]
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

def oneRowVertex : LeafVertex oneRowActual 1 0 :=
  ⟨oneRowPresented.domain, oneRowPresented, rfl⟩

example : LeafLabel oneRowVertex := by
  let fC := Classical.choose
    (actual_exists_coordinateFunctional oneRowActual oneRowU oneRowU_good)
  have hfC := Classical.choose_spec
    (actual_exists_coordinateFunctional oneRowActual oneRowU oneRowU_good)
  let fD : RawLeafLabel oneRowActual oneRowPresented.domain :=
    fC.comp (Submodule.inclusion oneRowPresented.domain_le_coordinateSpace)
  refine ⟨fD, oneRowPresented, rfl, ?_⟩
  intro e he
  change fC ⟨equationVector oneRowActual.support e, _⟩ =
    oneRowActual.rowRhs e
  exact hfC e he

example :
    ∃ (f : RawLeafLabel oneRowActual oneRowPresented.domain),
      RespectsAt oneRowPresented rfl f ∧
      ∃! F : ↥(oneRowPresented.domain ⊔
          equationSpan oneRowActual.support oneRowU) →ₗ[ZMod 2] ZMod 2,
        F.comp (Submodule.inclusion le_sup_left) = f ∧
        ∀ e (he : e ∈ oneRowU),
          F ⟨equationVector oneRowActual.support e,
            Submodule.mem_sup_right
              (equationVector_mem_equationSpan
                oneRowActual.support oneRowU e he)⟩ =
            oneRowActual.rowRhs e := by
  obtain ⟨fC, hfC⟩ :=
    actual_exists_coordinateFunctional oneRowActual oneRowU oneRowU_good
  let fD : RawLeafLabel oneRowActual oneRowPresented.domain :=
    fC.comp (Submodule.inclusion oneRowPresented.domain_le_coordinateSpace)
  have hfD : RespectsAt oneRowPresented rfl fD := by
    intro e he
    change fC ⟨equationVector oneRowActual.support e, _⟩ =
      oneRowActual.rowRhs e
    exact hfC e he
  exact ⟨fD, hfD,
    actual_existsUnique_gluedLeafRhsFunctional oneRowActual oneRowPresented
      oneRowU oneRowU_good fD hfD⟩

def emptyPresented {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : PresentedLeaf I 0 0 where
  U := ∅
  goodU := by simp [GoodQuestion]
  card_U := by simp
  L := ⊥
  L_le := by simp
  finrank_L := by simp
  transverse := by simp

def zeroRawLeafLabel {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)) : RawLeafLabel I D :=
  (0 : D →ₗ[ZMod 2] ZMod 2)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    ∃! F : ↥((emptyPresented I).domain ⊔
        equationSpan I.support ∅) →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) =
          zeroRawLeafLabel I (emptyPresented I).domain ∧
      ∀ e (he : e ∈ (∅ : Finset I.RowId)),
        F ⟨equationVector I.support e,
          Submodule.mem_sup_right
            (equationVector_mem_equationSpan I.support ∅ e he)⟩ =
          I.rowRhs e := by
  have hgood : GoodQuestion I.support (∅ : Finset I.RowId) := by
    simp [GoodQuestion]
  have hf : RespectsAt (emptyPresented I) rfl
      (zeroRawLeafLabel I (emptyPresented I).domain) := by
    intro e he
    have hempty : e ∉ (∅ : Finset I.RowId) := by simp
    exact (hempty he).elim
  exact actual_existsUnique_gluedLeafRhsFunctional I (emptyPresented I)
    ∅ hgood (zeroRawLeafLabel I (emptyPresented I).domain) hf

example : oneRowPresented.H = oneRowPresented.H := by
  exact H_eq_of_domain_eq oneRowPresented oneRowPresented rfl

example (f : RawLeafLabel oneRowActual oneRowPresented.domain) :
    RespectsAt oneRowPresented rfl f ↔
      RespectsAt oneRowPresented rfl f := by
  exact respectsAt_iff_of_domain_eq
    oneRowPresented oneRowPresented rfl rfl f

end
end PvNP.RealizableHardness.ActualPresentedLeafGluingChecks
