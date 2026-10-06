import PvNP.RealizableHardness.ActualLeafRepresentativeSampler

namespace PvNP.RealizableHardness.ActualCliqueCollisionTransfer

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

local instance rowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

abbrev LeafTable {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (J h : Nat) :=
  (v : LeafVertex I J h) → LeafLabel v

def LeafClique {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) (J h : Nat) :=
  {C : Finset (LeafVertex I J h) // ∃ v, C = relClass v}

def cliqueOf {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (v : LeafVertex I J h) : LeafClique I J h :=
  ⟨relClass v, ⟨v, rfl⟩⟩

def CliqueRepresentative {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m} (C : LeafClique I J h) :=
  {v : LeafVertex I J h // cliqueOf v = C}

instance cliqueRepresentativeNonempty {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m} (C : LeafClique I J h) :
    Nonempty (CliqueRepresentative C) := by
  obtain ⟨v, hv⟩ := C.property
  exact ⟨⟨v, Subtype.ext hv.symm⟩⟩

abbrev RepresentativeChoice
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (J h : Nat) :=
  (C : LeafClique I J h) → CliqueRepresentative C

instance representativeChoiceNonempty {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Nonempty (RepresentativeChoice I J h) := by infer_instance

theorem relClass_eq_iff {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    {v w : LeafVertex I J h} :
    relClass v = relClass w ↔ LeafVertex.Rel v w := by
  constructor
  · intro h
    have hw : w ∈ relClass v := by
      rw [h]
      exact mem_relClass_iff.mpr (LeafVertex.Rel.refl w)
    exact mem_relClass_iff.mp hw
  · intro hvw
    ext z
    constructor
    · intro hz
      apply mem_relClass_iff.mpr
      exact LeafVertex.Rel.trans (LeafVertex.Rel.symm hvw) (mem_relClass_iff.mp hz)
    · intro hz
      apply mem_relClass_iff.mpr
      exact LeafVertex.Rel.trans hvw (mem_relClass_iff.mp hz)

theorem cliqueOf_eq_iff {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    {v w : LeafVertex I J h} :
    cliqueOf v = cliqueOf w ↔ LeafVertex.Rel v w := by
  constructor
  · intro h
    exact relClass_eq_iff.mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact relClass_eq_iff.mpr h

theorem representative_rel {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (s : RepresentativeChoice I J h)
    (v : LeafVertex I J h) :
    LeafVertex.Rel (s (cliqueOf v)).1 v := by
  apply cliqueOf_eq_iff.mp
  exact (s (cliqueOf v)).property

noncomputable def selectedTable {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (s : RepresentativeChoice I J h) : LeafTable I J h :=
  fun v => transportedLeafLabel (representative_rel s v)
    (T (s (cliqueOf v)).1)

theorem selectedTable_clique_consistent {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    {v w : LeafVertex I J h} (hvw : LeafVertex.Rel v w) :
  transportedLeafLabel hvw (selectedTable T s v) = selectedTable T s w := by
  have hC : cliqueOf v = cliqueOf w :=
    Subtype.ext (relClass_eq_iff.mpr hvw)
  have dependent_choice_congr :
      ∀ (C₁ C₂ : LeafClique I J h) (hC' : C₁ = C₂),
        Eq.ndrec (s C₁) hC' = s C₂ := by
    intro C₁ C₂ hC'
    cases hC'
    rfl
  have hscast :
      Eq.ndrec (motive := CliqueRepresentative) (s (cliqueOf v)) hC =
        s (cliqueOf w) := by
    exact dependent_choice_congr _ _ hC
  have subtype_val_transport :
      ∀ (C₁ C₂ : LeafClique I J h) (hC' : C₁ = C₂)
        (x : CliqueRepresentative C₁),
        (Eq.ndrec x hC').1 = x.1 := by
    intro C₁ C₂ hC' x
    cases hC'
    rfl
  have hrep : (s (cliqueOf v)).1 = (s (cliqueOf w)).1 := by
    have hval := congrArg Subtype.val hscast
    exact (subtype_val_transport _ _ hC (s (cliqueOf v))).symm.trans hval
  have transport_congr :
      ∀ (x y z : LeafVertex I J h) (hxy : x = y)
        (hr : LeafVertex.Rel x z) (hs : LeafVertex.Rel y z)
        (tx : LeafLabel x) (ty : LeafLabel y)
        (ht : Eq.ndrec tx hxy = ty),
        transportedLeafLabel hr tx = transportedLeafLabel hs ty := by
    intro x y z hxy hr hs tx ty ht
    cases hxy
    cases ht
    rfl
  have hcoh := transportedLeafLabel_coherence
    (representative_rel s v) hvw (T (s (cliqueOf v)).1)
  have htable :
      Eq.ndrec (T (s (cliqueOf v)).1) hrep = T (s (cliqueOf w)).1 := by
    have table_congr :
        ∀ (x y : LeafVertex I J h) (hxy : x = y),
          Eq.ndrec (T x) hxy = T y := by
      intro x y hxy
      cases hxy
      rfl
    exact table_congr _ _ hrep
  have htransport := transport_congr
    (s (cliqueOf v)).1 (s (cliqueOf w)).1 w hrep
    (LeafVertex.Rel.trans (representative_rel s v) hvw)
    (representative_rel s w)
    (T (s (cliqueOf v)).1) (T (s (cliqueOf w)).1) htable
  change transportedLeafLabel hvw
      (transportedLeafLabel (representative_rel s v) (T (s (cliqueOf v)).1)) =
    transportedLeafLabel (representative_rel s w) (T (s (cliqueOf w)).1)
  exact hcoh.trans htransport

end
end PvNP.RealizableHardness.ActualCliqueCollisionTransfer
