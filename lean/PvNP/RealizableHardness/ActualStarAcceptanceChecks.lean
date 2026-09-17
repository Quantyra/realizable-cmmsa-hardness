import PvNP.RealizableHardness.ActualStarAcceptance
import PvNP.RealizableHardness.ActualLeafRejectionUnionChecks

namespace PvNP.RealizableHardness.ActualStarAcceptanceChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualLeafRejectionUnionChecks
noncomputable section

#check starAccepts
#check starAccepts_iff_anyFail_zero
#check starAccepts_of_source_agrees
#check starAcceptsCenter
#check starAcceptsCenter_iff_starAccepts

#print axioms starAccepts_iff_anyFail_zero
#print axioms starAccepts_of_source_agrees
#print axioms starAcceptsCenter_iff_starAccepts

private theorem id_source_agrees {N m J h k : Nat}
    {I : ActualOccurrenceAllocation.Instance N m}
    {v : LeafVertex I J h} (C : CenterSubspace v k) (φ : LeafLabel v)
    (hK : C.K = C.K) :
    LinearMap.comp (restrictToCenter C φ)
        (Submodule.inclusion (le_of_eq hK.symm)) =
      restrictToCenter C φ := by
  have : Submodule.inclusion (le_of_eq hK.symm) = LinearMap.id :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.comp_id]

private theorem mid_source_agrees :
    LinearMap.comp (restrictToCenter sourceCenter sourcePackaged)
        (Submodule.inclusion (le_of_eq source_mid_center_eq.symm)) =
      restrictToCenter midCenter midPackaged :=
  (restrictionAgreesOnCenter_iff_source source_mid_vertex_rel sourceCenter midCenter
    source_mid_center_eq sourcePackaged midPackaged).mp rfl

example :
    starAccepts
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
      (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => sourceCenter)
      (fun _ => source_center_eq)
      (fun _ => sourcePackaged) (fun _ => sourcePackaged) ↔
      anyFailIndicator
        (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
        (fun _ => source_vertex_rel)
        (fun _ => sourceCenter) (fun _ => sourceCenter)
        (fun _ => source_center_eq)
        (fun _ => sourcePackaged) (fun _ => sourcePackaged) = 0 :=
  starAccepts_iff_anyFail_zero
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
    (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => sourceCenter)
    (fun _ => source_center_eq)
    (fun _ => sourcePackaged) (fun _ => sourcePackaged)

example :
    starAccepts
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
      (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => sourceCenter)
      (fun _ => source_center_eq)
      (fun _ => sourcePackaged) (fun _ => sourcePackaged) :=
  starAccepts_of_source_agrees
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => sourceVertex)
    (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => sourceCenter)
    (fun _ => source_center_eq)
    (fun _ => sourcePackaged) (fun _ => sourcePackaged)
    (fun _ => id_source_agrees sourceCenter sourcePackaged source_center_eq)

example :
    starAccepts
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) ↔
      anyFailIndicator
        (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
        (fun _ => source_mid_vertex_rel)
        (fun _ => sourceCenter) (fun _ => midCenter)
        (fun _ => source_mid_center_eq)
        (fun _ => sourcePackaged) (fun _ => midPackaged) = 0 :=
  starAccepts_iff_anyFail_zero
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)

example :
    starAccepts
      (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) :=
  starAccepts_of_source_agrees
    (fun _ : Fin 1 => sourceVertex) (fun _ : Fin 1 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)
    (fun _ => mid_source_agrees)

example :
    starAccepts
      (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => sourceVertex)
      (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => sourceCenter)
      (fun _ => source_center_eq)
      (fun _ => sourcePackaged) (fun _ => sourcePackaged) ↔
      anyFailIndicator
        (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => sourceVertex)
        (fun _ => source_vertex_rel)
        (fun _ => sourceCenter) (fun _ => sourceCenter)
        (fun _ => source_center_eq)
        (fun _ => sourcePackaged) (fun _ => sourcePackaged) = 0 :=
  starAccepts_iff_anyFail_zero
    (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => sourceVertex)
    (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => sourceCenter)
    (fun _ => source_center_eq)
    (fun _ => sourcePackaged) (fun _ => sourcePackaged)

example :
    starAccepts
      (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => sourceVertex)
      (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => sourceCenter)
      (fun _ => source_center_eq)
      (fun _ => sourcePackaged) (fun _ => sourcePackaged) :=
  starAccepts_of_source_agrees
    (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => sourceVertex)
    (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => sourceCenter)
    (fun _ => source_center_eq)
    (fun _ => sourcePackaged) (fun _ => sourcePackaged)
    (fun _ => id_source_agrees sourceCenter sourcePackaged source_center_eq)

example :
    starAccepts
      (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) ↔
      anyFailIndicator
        (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
        (fun _ => source_mid_vertex_rel)
        (fun _ => sourceCenter) (fun _ => midCenter)
        (fun _ => source_mid_center_eq)
        (fun _ => sourcePackaged) (fun _ => midPackaged) = 0 :=
  starAccepts_iff_anyFail_zero
    (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)

example :
    starAccepts
      (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
      (fun _ => source_mid_vertex_rel)
      (fun _ => sourceCenter) (fun _ => midCenter)
      (fun _ => source_mid_center_eq)
      (fun _ => sourcePackaged) (fun _ => midPackaged) :=
  starAccepts_of_source_agrees
    (fun _ : Fin 2 => sourceVertex) (fun _ : Fin 2 => midVertex)
    (fun _ => source_mid_vertex_rel)
    (fun _ => sourceCenter) (fun _ => midCenter)
    (fun _ => source_mid_center_eq)
    (fun _ => sourcePackaged) (fun _ => midPackaged)
    (fun _ => mid_source_agrees)

example :
    starAcceptsCenter sourceVertex sourceCenter sourcePackaged
      (fun _ : Fin 1 => sourceVertex) (fun _ => source_vertex_rel)
      (fun _ => sourceCenter) (fun _ => source_center_eq)
      (fun _ => sourcePackaged) ↔
      starAccepts (fun _ => sourceVertex)
        (fun _ : Fin 1 => sourceVertex) (fun _ => source_vertex_rel)
        (fun _ => sourceCenter) (fun _ => sourceCenter)
        (fun _ => source_center_eq)
        (fun _ => sourcePackaged) (fun _ => sourcePackaged) :=
  starAcceptsCenter_iff_starAccepts sourceVertex sourceCenter sourcePackaged
    (fun _ : Fin 1 => sourceVertex) (fun _ => source_vertex_rel)
    (fun _ => sourceCenter) (fun _ => source_center_eq)
    (fun _ => sourcePackaged)

example :
    starAcceptsCenter sourceVertex sourceCenter sourcePackaged
      (fun _ : Fin 2 => midVertex) (fun _ => source_mid_vertex_rel)
      (fun _ => midCenter) (fun _ => source_mid_center_eq)
      (fun _ => midPackaged) ↔
      starAccepts (fun _ => sourceVertex)
        (fun _ : Fin 2 => midVertex) (fun _ => source_mid_vertex_rel)
        (fun _ => sourceCenter) (fun _ => midCenter)
        (fun _ => source_mid_center_eq)
        (fun _ => sourcePackaged) (fun _ => midPackaged) :=
  starAcceptsCenter_iff_starAccepts sourceVertex sourceCenter sourcePackaged
    (fun _ : Fin 2 => midVertex) (fun _ => source_mid_vertex_rel)
    (fun _ => midCenter) (fun _ => source_mid_center_eq)
    (fun _ => midPackaged)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAccepts
      (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) ↔
      anyFailIndicator
        (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
        (fun _ => empty_vertex_rel I)
        (fun _ => emptyCenter I) (fun _ => emptyCenter I)
        (fun _ => empty_center_eq I)
        (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) = 0 :=
  starAccepts_iff_anyFail_zero
    (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAccepts
      (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) :=
  starAccepts_of_source_agrees
    (fun _ : Fin 0 => emptyVertex I) (fun _ : Fin 0 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)
    (fun i => Fin.elim0 i)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAcceptsCenter (emptyVertex I) (emptyCenter I) (emptyPackaged I)
      (fun _ : Fin 0 => emptyVertex I) (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) ↔
      starAccepts (fun _ => emptyVertex I)
        (fun _ : Fin 0 => emptyVertex I) (fun _ => empty_vertex_rel I)
        (fun _ => emptyCenter I) (fun _ => emptyCenter I)
        (fun _ => empty_center_eq I)
        (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) :=
  starAcceptsCenter_iff_starAccepts (emptyVertex I) (emptyCenter I)
    (emptyPackaged I) (fun _ : Fin 0 => emptyVertex I)
    (fun _ => empty_vertex_rel I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I) (fun _ => emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAccepts
      (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) ↔
      anyFailIndicator
        (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
        (fun _ => empty_vertex_rel I)
        (fun _ => emptyCenter I) (fun _ => emptyCenter I)
        (fun _ => empty_center_eq I)
        (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) = 0 :=
  starAccepts_iff_anyFail_zero
    (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAccepts
      (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
      (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => emptyCenter I)
      (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) :=
  starAccepts_of_source_agrees
    (fun _ : Fin 1 => emptyVertex I) (fun _ : Fin 1 => emptyVertex I)
    (fun _ => empty_vertex_rel I)
    (fun _ => emptyCenter I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I)
    (fun _ => emptyPackaged I) (fun _ => emptyPackaged I)
    (fun _ => id_source_agrees (emptyCenter I) (emptyPackaged I) (empty_center_eq I))

example {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) :
    starAcceptsCenter (emptyVertex I) (emptyCenter I) (emptyPackaged I)
      (fun _ : Fin 1 => emptyVertex I) (fun _ => empty_vertex_rel I)
      (fun _ => emptyCenter I) (fun _ => empty_center_eq I)
      (fun _ => emptyPackaged I) ↔
      starAccepts (fun _ => emptyVertex I)
        (fun _ : Fin 1 => emptyVertex I) (fun _ => empty_vertex_rel I)
        (fun _ => emptyCenter I) (fun _ => emptyCenter I)
        (fun _ => empty_center_eq I)
        (fun _ => emptyPackaged I) (fun _ => emptyPackaged I) :=
  starAcceptsCenter_iff_starAccepts (emptyVertex I) (emptyCenter I)
    (emptyPackaged I) (fun _ : Fin 1 => emptyVertex I)
    (fun _ => empty_vertex_rel I) (fun _ => emptyCenter I)
    (fun _ => empty_center_eq I) (fun _ => emptyPackaged I)

end
end PvNP.RealizableHardness.ActualStarAcceptanceChecks
