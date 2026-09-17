import PvNP.RealizableHardness.ActualStarQuestionSupport
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic

namespace PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualStarQuestionSupport

variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

def equationVector (row : E → Finset X) (e : E) : X → ZMod 2 :=
  fun x => if x ∈ row e then 1 else 0

def equationSpan (row : E → Finset X) (U : Finset E) :
    Submodule (ZMod 2) (X → ZMod 2) :=
  Submodule.span (ZMod 2) (equationVector row '' (U : Set E))

def coordinateSpace (row : E → Finset X) (U : Finset E) :
    Submodule (ZMod 2) (X → ZMod 2) :=
  { carrier := {v | ∀ x, x ∉ questionSupport row U → v x = 0}
    zero_mem' := by
      intro x hx
      simp
    add_mem' := by
      intro v w hv hw x hx
      simp only [Pi.add_apply]
      rw [hv x hx, hw x hx, add_zero]
    smul_mem' := by
      intro a v hv x hx
      simp only [Pi.smul_apply]
      rw [hv x hx, smul_zero] }

lemma equationVector_mem_coordinateSpace
    (row : E → Finset X) (U : Finset E) (e : E) (he : e ∈ U) :
    equationVector row e ∈ coordinateSpace row U := by
  intro x hx
  simp only [equationVector]
  by_cases hxe : x ∈ row e
  · exfalso
    exact hx (Finset.mem_biUnion.mpr ⟨e, he, hxe⟩)
  · simp [hxe]

lemma equationVector_mem_equationSpan
    (row : E → Finset X) (U : Finset E) (e : E) (he : e ∈ U) :
    equationVector row e ∈ equationSpan row U := by
  exact Submodule.subset_span ⟨e, he, rfl⟩

theorem equationSpan_inf_coordinateSpace
    (row : E → Finset X)
    (hthree : ∀ e, (row e).card = 3)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ (row f)).card ≤ 1)
    (U U' : Finset E)
    (hU : GoodQuestion row U) (hU' : GoodQuestion row U') :
    equationSpan row U' ⊓ coordinateSpace row U =
      equationSpan row (U' ∩ U) := by
  classical
  apply le_antisymm
  · intro v hv
    rcases (Finsupp.mem_span_image_iff_linearCombination (R := ZMod 2)).mp hv.1 with
      ⟨l, hlU', hlcomb⟩
    have hcoeff : ∀ e ∈ U', e ∉ U → l e = 0 := by
      intro e he heU
      have heU' : e ∈ U' := by
        exact he
      obtain ⟨x, hxe, hxU, hxrest⟩ :=
        new_row_private_coordinate row hthree hlinear U U' hU hU' e heU' heU
      have hxother : ∀ f ∈ U', f ≠ e → equationVector row f x = 0 := by
        intro f hf hfe
        have hxf : x ∉ row f := by
          intro hxin
          apply hxrest
          exact Finset.mem_biUnion.mpr
            ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hxin⟩
        simp [equationVector, hxf]
      have hrepr : (∑ f ∈ U', l f • equationVector row f) = v := by
        simpa only [Finsupp.linearCombination_apply_of_mem_supported (ZMod 2) hlU'] using hlcomb
      have heval := congrFun hrepr x
      have hleft : (∑ f ∈ U', l f • equationVector row f) x = l e := by
        simp only [Finset.sum_apply, Pi.smul_apply]
        rw [Finset.sum_eq_single e]
        · simp [equationVector, hxe]
        · intro f hf hfe
          simp [hxother f hf hfe]
        · intro he'
          exact (he' he).elim
      rw [hleft, hv.2 x hxU] at heval
      exact heval
    apply (Finsupp.mem_span_image_iff_linearCombination (R := ZMod 2)).mpr
    refine ⟨l, ?_, hlcomb⟩
    rw [Finsupp.mem_supported']
    intro e heinter
    by_cases heU' : e ∈ U'
    · have heU : e ∉ U := by
        intro he
        apply heinter
        exact Finset.mem_inter.mpr ⟨heU', he⟩
      exact hcoeff e heU' heU
    · exact (Finsupp.mem_supported' (ZMod 2) l).mp hlU' e (by simpa using heU')
  · intro v hv
    apply Submodule.mem_inf.mpr
    constructor
    · exact Submodule.span_mono (by
        rintro w ⟨e, he, rfl⟩
        exact ⟨e, (Finset.mem_inter.mp he).1, rfl⟩) hv
    · apply (Submodule.span_le.mpr ?_) hv
      rintro w ⟨e, he, rfl⟩
      exact equationVector_mem_coordinateSpace row U e (Finset.mem_inter.mp he).2

#print axioms equationSpan_inf_coordinateSpace
end PvNP.RealizableHardness.ActualStarSpanIntersection
