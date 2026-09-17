import PvNP.RealizableHardness.ActualStarAcceptance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

local instance sourceStarRowIdDecidableEq : DecidableEq I.RowId :=
  Classical.decEq _

local instance sourceStarGlobalVarDecidableEq : DecidableEq I.GlobalVar :=
  inferInstance

local instance sourceStarGlobalVarFintype : Fintype I.GlobalVar :=
  inferInstance

/-- Pairing of a domain vector with a global assignment. -/
noncomputable def honestRawLabel
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (x : I.GlobalVar → ZMod 2) : RawLeafLabel I D :=
  { toFun := fun z => ∑ i : I.GlobalVar, z.1 i * x i
    map_add' := fun a b => by
      simp only [AddMemClass.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun r a => by
      simp only [RingHom.id_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => mul_assoc r (a.1 i) (x i)) ?_
      exact (Finset.mul_sum Finset.univ (fun i => a.1 i * x i) r).symm }

private theorem honestRawLabel_toFun
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (x : I.GlobalVar → ZMod 2) (z : D) :
    (honestRawLabel (D := D) x).toFun z = ∑ i : I.GlobalVar, z.1 i * x i :=
  rfl

theorem honestRawLabel_eval_equation
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2)
    (e : I.RowId) (he : e ∈ P.U) :
    (honestRawLabel (D := P.domain) x).toFun
        ⟨equationVector I.support e, P.H_le_domain
          (equationVector_mem_equationSpan I.support P.U e he)⟩ =
      x (I.row e 0) + x (I.row e 1) + x (I.row e 2) := by
  rw [honestRawLabel_toFun]
  have hsubset : I.support e ⊆ (Finset.univ : Finset I.GlobalVar) :=
    Finset.subset_univ _
  have hzero : ∀ i ∈ (Finset.univ : Finset I.GlobalVar), i ∉ I.support e →
      equationVector I.support e i * x i = 0 := by
    intro i _ hi
    simp [equationVector, hi]
  have hsum :
      ∑ i : I.GlobalVar, equationVector I.support e i * x i =
        ∑ i ∈ I.support e, x i := by
    rw [← Finset.sum_subset hsubset hzero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [equationVector, hi]
  rw [hsum, I.support_eq e]
  have hinj : Set.InjOn (I.row e) (Finset.univ : Finset (Fin 3)) := by
    intro a _ b _ hab
    exact (Finite3LinSource.ofActual I).row_injective e hab
  rw [Finset.sum_image hinj, Fin.sum_univ_three]

private theorem ofActual_badRow_false_iff
    (x : I.GlobalVar → ZMod 2) (e : I.RowId) :
    (Finite3LinSource.ofActual I).badRow x e = false ↔
      x (I.row e 0) + x (I.row e 1) + x (I.row e 2) = I.rowRhs e := by
  change decide
      (¬ (x ((Finite3LinSource.ofActual I).row e 0)
          + x ((Finite3LinSource.ofActual I).row e 1)
          + x ((Finite3LinSource.ofActual I).row e 2) =
        (Finite3LinSource.ofActual I).rhs e)) = false ↔ _
  simp only [Finite3LinSource.ofActual_row, Finite3LinSource.ofActual_rhs]
  constructor
  · intro h
    exact of_not_not (decide_eq_false_iff_not.mp h)
  · intro h
    simp [h]

theorem honestRawLabel_respects_iff
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2) :
    RespectsAt P rfl (honestRawLabel (D := P.domain) x) ↔
      ∀ e ∈ P.U, (Finite3LinSource.ofActual I).badRow x e = false := by
  constructor
  · intro hf e he
    exact (ofActual_badRow_false_iff x e).mpr
      ((honestRawLabel_eval_equation P x e he).symm.trans (hf e he))
  · intro hbad e he
    exact (honestRawLabel_eval_equation P x e he).trans
      ((ofActual_badRow_false_iff x e).mp (hbad e he))

noncomputable def honestPackaged
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2)
    (hx : RespectsAt P rfl (honestRawLabel (D := P.domain) x)) :
    LeafLabel ⟨P.domain, ⟨P, rfl⟩⟩ :=
  packagedLabel P (honestRawLabel (D := P.domain) x) hx

private theorem honestPackaged_restrict
    {v : LeafVertex I J h} {k : Nat}
    (C : CenterSubspace v k) (φ : LeafLabel v)
    (x : I.GlobalVar → ZMod 2)
    (hφ : φ.1 = honestRawLabel (D := v.1) x)
    (z : C.K) :
    restrictToCenter C φ z =
      ∑ i : I.GlobalVar, (z : I.GlobalVar → ZMod 2) i * x i := by
  rw [restrictToCenter_eq_subtype, hφ]
  rfl

private theorem honestPackaged_val
    (P : PresentedLeaf I J h) (x : I.GlobalVar → ZMod 2)
    (hx : RespectsAt P rfl (honestRawLabel (D := P.domain) x)) :
    (honestPackaged P x hx).1 =
      honestRawLabel (D := (⟨P.domain, ⟨P, rfl⟩⟩ : LeafVertex I J h).1) x :=
  rfl

theorem restrictionAgreesOnCenter_honest
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (x : I.GlobalVar → ZMod 2)
    (hxP : RespectsAt P rfl (honestRawLabel (D := P.domain) x))
    (hxQ : RespectsAt Q rfl (honestRawLabel (D := Q.domain) x))
    {k : Nat}
    (Cv : CenterSubspace ⟨P.domain, ⟨P, rfl⟩⟩ k)
    (Cw : CenterSubspace ⟨Q.domain, ⟨Q, rfl⟩⟩ k)
    (hK : Cv.K = Cw.K) :
    restrictionAgreesOnCenter
      ((LeafVertex.Rel_iff_presented _ _ P Q rfl rfl).mpr hPQ)
      Cv Cw hK (honestPackaged P x hxP) (honestPackaged Q x hxQ) := by
  let v : LeafVertex I J h := ⟨P.domain, ⟨P, rfl⟩⟩
  let w : LeafVertex I J h := ⟨Q.domain, ⟨Q, rfl⟩⟩
  refine (restrictionAgreesOnCenter_iff_source
      (v := v) (w := w)
      ((LeafVertex.Rel_iff_presented v w P Q rfl rfl).mpr hPQ)
      Cv Cw hK (honestPackaged P x hxP) (honestPackaged Q x hxQ)).mpr ?_
  apply LinearMap.ext
  intro z
  have hleft :
      LinearMap.comp (restrictToCenter Cv (honestPackaged P x hxP))
          (Submodule.inclusion (le_of_eq hK.symm)) z =
        ∑ i : I.GlobalVar, (z : I.GlobalVar → ZMod 2) i * x i :=
    honestPackaged_restrict Cv (honestPackaged P x hxP) x
      (honestPackaged_val P x hxP)
      (Submodule.inclusion (le_of_eq hK.symm) z)
  have hright :
      restrictToCenter Cw (honestPackaged Q x hxQ) z =
        ∑ i : I.GlobalVar, (z : I.GlobalVar → ZMod 2) i * x i :=
    honestPackaged_restrict Cw (honestPackaged Q x hxQ) x
      (honestPackaged_val Q x hxQ) z
  exact hleft.trans hright.symm

theorem starAccepts_honest
    {n k : Nat}
    (Ps : Fin n → PresentedLeaf I J h)
    (x : I.GlobalVar → ZMod 2)
    (hx : ∀ i, RespectsAt (Ps i) rfl (honestRawLabel (D := (Ps i).domain) x))
    (Cs : ∀ i, CenterSubspace ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩ k)
    (hK : ∀ i j, (Cs i).K = (Cs j).K) :
    starAccepts
      (fun i => ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩)
      (fun i => ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩)
      (fun i => LeafVertex.Rel.refl _)
      Cs Cs (fun i => rfl)
      (fun i => honestPackaged (Ps i) x (hx i))
      (fun i => honestPackaged (Ps i) x (hx i)) := by
  intro i
  let v : LeafVertex I J h := ⟨(Ps i).domain, ⟨Ps i, rfl⟩⟩
  refine (restrictionAgreesOnCenter_iff_source
      (v := v) (w := v)
      (LeafVertex.Rel.refl v) (Cs i) (Cs i) rfl
      (honestPackaged (Ps i) x (hx i))
      (honestPackaged (Ps i) x (hx i))).mpr ?_
  apply LinearMap.ext
  intro z
  have hleft :
      LinearMap.comp (restrictToCenter (Cs i) (honestPackaged (Ps i) x (hx i)))
          (Submodule.inclusion (le_of_eq (rfl : (Cs i).K = (Cs i).K).symm)) z =
        ∑ j : I.GlobalVar, (z : I.GlobalVar → ZMod 2) j * x j :=
    honestPackaged_restrict (Cs i) (honestPackaged (Ps i) x (hx i)) x
      (honestPackaged_val (Ps i) x (hx i))
      (Submodule.inclusion (le_of_eq (rfl : (Cs i).K = (Cs i).K).symm) z)
  have hright :
      restrictToCenter (Cs i) (honestPackaged (Ps i) x (hx i)) z =
        ∑ j : I.GlobalVar, (z : I.GlobalVar → ZMod 2) j * x j :=
    honestPackaged_restrict (Cs i) (honestPackaged (Ps i) x (hx i)) x
      (honestPackaged_val (Ps i) x (hx i)) z
  exact hleft.trans hright.symm

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
