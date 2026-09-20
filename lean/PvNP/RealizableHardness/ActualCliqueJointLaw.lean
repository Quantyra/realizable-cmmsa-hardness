import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import PvNP.RealizableHardness.ActualCliqueCollisionTransfer

namespace PvNP.RealizableHardness.ActualCliqueCollisionTransfer

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

local instance leafCliqueFintype {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) :
    Fintype (LeafClique I J h) :=
  Fintype.ofInjective (fun C : LeafClique I J h => C.1) Subtype.val_injective

local instance cliqueRepresentativeFintype {N m J h : Nat}
    {I : ActualOccurrenceAllocation.Instance N m} (C : LeafClique I J h) :
    Fintype (CliqueRepresentative C) :=
  Fintype.ofInjective (fun v : CliqueRepresentative C => v.1) Subtype.val_injective

abbrev LabelTuple {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (vs : Fin k → LeafVertex I J h) :=
  (i : Fin k) → LeafLabel (vs i)

abbrev IndependentChoice {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (vs : Fin k → LeafVertex I J h) :=
  (i : Fin k) → CliqueRepresentative (cliqueOf (vs i))

def DistinctCliques {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (vs : Fin k → LeafVertex I J h) : Prop :=
  Function.Injective (fun i => cliqueOf (vs i))

def CliqueCollision {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (vs : Fin k → LeafVertex I J h) : Prop :=
  ¬ DistinctCliques vs

noncomputable def uniformMean (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℚ) : ℚ :=
  (∑ x, f x) / Fintype.card α

private theorem uniformMean_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : β → ℚ) :
  uniformMean α (fun x => f (e x)) = uniformMean β f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

private theorem uniformMean_prod_fst
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℚ) :
  uniformMean (α × β) (fun x => f x.1) = uniformMean α f := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp
  simp only [Fintype.card]
  ring

private theorem uniformMean_restrict_injective
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → Type*) [∀ c, Fintype (A c)]
    [∀ c, Nonempty (A c)]
    (key : ι → κ) (hkey : Function.Injective key)
    (g : ((i : ι) → A (key i)) → ℚ) :
  uniformMean ((c : κ) → A c)
      (fun s => g (fun i => s (key i))) =
    uniformMean ((i : ι) → A (key i)) g := by
  classical
  let p : κ → Prop := fun c => c ∈ Set.range key
  let e : ι ≃ Set.range key := Equiv.ofInjective key hkey
  let Unused := (c : {c : κ // c ∉ Set.range key}) → A c.1
  let split := Equiv.piEquivPiSubtypeProd p A
  let used : ((i : ι) → A (key i)) ≃
      ((c : Set.range key) → A c.1) :=
    Equiv.piCongrLeft (fun c : Set.range key => A c.1) e
  let total : ((c : κ) → A c) ≃
      (((i : ι) → A (key i)) × Unused) :=
    split.trans (Equiv.prodCongr used.symm (Equiv.refl Unused))
  have hrestrict (s : (c : κ) → A c) :
      (total s).1 = (fun i => s (key i)) := by
    funext i
    change
      (Equiv.piCongrLeft (fun c : Set.range key => A c.1) e).symm
          (fun c : Set.range key => s c.1) i = s (key i)
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  calc
    uniformMean ((c : κ) → A c)
        (fun s => g (fun i => s (key i))) =
        uniformMean ((c : κ) → A c)
          (fun s => (fun x => g x.1) (total s)) := by
      apply congrArg (uniformMean ((c : κ) → A c))
      funext s
      exact congrArg g (hrestrict s).symm
    _ = uniformMean
          (((i : ι) → A (key i)) × Unused)
          (fun x => g x.1) :=
      uniformMean_equiv total (fun x => g x.1)
    _ = uniformMean ((i : ι) → A (key i)) g :=
      uniformMean_prod_fst g

def independentLabels {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (vs : Fin k → LeafVertex I J h)
    (r : IndependentChoice vs) : LabelTuple vs :=
  fun i => transportedLeafLabel
    (cliqueOf_eq_iff.mp (r i).property) (T (r i).1)

def selectedLabels {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (s : RepresentativeChoice I J h)
    (vs : Fin k → LeafVertex I J h) : LabelTuple vs :=
  fun i => selectedTable T s (vs i)

theorem jointLaw_eq_of_distinctCliques
    {N m J h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (T : LeafTable I J h) (vs : Fin k → LeafVertex I J h)
    (hdist : DistinctCliques vs) (F : LabelTuple vs → ℚ) :
  uniformMean (RepresentativeChoice I J h)
      (fun s => F (selectedLabels T s vs)) =
    uniformMean (IndependentChoice vs)
      (fun r => F (independentLabels T vs r)) := by
  have hlabels (s : RepresentativeChoice I J h) :
      independentLabels T vs (fun i => s (cliqueOf (vs i))) =
        selectedLabels T s vs := by
    funext i
    unfold independentLabels selectedLabels selectedTable
    change transportedLeafLabel
        (cliqueOf_eq_iff.mp (s (cliqueOf (vs i))).property)
        (T (s (cliqueOf (vs i))).1) =
      transportedLeafLabel (representative_rel s (vs i))
        (T (s (cliqueOf (vs i))).1)
    have hrel :
        cliqueOf_eq_iff.mp (s (cliqueOf (vs i))).property =
          representative_rel s (vs i) :=
      Subsingleton.elim _ _
    rw [hrel]
  calc
    uniformMean (RepresentativeChoice I J h)
        (fun s => F (selectedLabels T s vs)) =
      uniformMean (RepresentativeChoice I J h)
        (fun s => F (independentLabels T vs
          (fun i => s (cliqueOf (vs i))))) := by
      apply congrArg (uniformMean (RepresentativeChoice I J h))
      funext s
      rw [hlabels s]
    _ = uniformMean (IndependentChoice vs)
        (fun r => F (independentLabels T vs r)) := by
      simpa only [IndependentChoice, RepresentativeChoice] using
        (uniformMean_restrict_injective
          (A := fun C => CliqueRepresentative C)
          (key := fun i => cliqueOf (vs i)) hdist
          (fun r => F (independentLabels T vs r)))

end
end PvNP.RealizableHardness.ActualCliqueCollisionTransfer
