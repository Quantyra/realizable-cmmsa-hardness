import PvNP.RealizableHardness.ActualStarSpanIntersection
import PvNP.RealizableHardness.ActualFinite3LinSource
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.Defs

namespace PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section

variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

theorem equationVectors_linearIndependent
    (row : E → Finset X) (U : Finset E)
    (hpair : (U : Set E).Pairwise (fun e f => Disjoint (row e) (row f)))
    (hnonempty : ∀ e ∈ U, (row e).Nonempty) :
    LinearIndependent (ZMod 2) (fun e : ↥U => equationVector row e.1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  obtain ⟨x, hx⟩ := hnonempty i.1 i.2
  have hsingle : (∑ j, g j • equationVector row j.1) x = g i := by
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp [equationVector, hx]
    · intro j _ hji
      have hbase : i.1 ≠ j.1 := by
        intro hij
        apply hji
        exact Subtype.ext hij.symm
      have hdis : Disjoint (row i.1) (row j.1) := hpair i.2 j.2 hbase
      have hxnot : x ∉ row j.1 := (Finset.disjoint_left.mp hdis) hx
      simp [equationVector, hxnot]
    · simp
  have heval := congrFun hsum x
  rw [hsingle] at heval
  simpa using heval

theorem existsUnique_rhsFunctional
    (row : E → Finset X) (rhs : E → ZMod 2)
    (hthree : ∀ e, (row e).card = 3)
    (U : Finset E) (hU : GoodQuestion row U) :
    ∃! psi : equationSpan row U →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ U),
        psi ⟨equationVector row e,
          equationVector_mem_equationSpan row U e he⟩ = rhs e := by
  let v : ↥U → equationSpan row U := fun e =>
    ⟨equationVector row e.1,
      equationVector_mem_equationSpan row U e.1 e.2⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (equationSpan row U).subtype
    change LinearIndependent (ZMod 2)
      (fun e : ↥U => equationVector row e.1)
    exact equationVectors_linearIndependent row U hU.1 (fun e he => by
      apply Finset.card_pos.mp
      rw [hthree e]
      decide)
  have hrange : Set.range v =
      (((↑) : equationSpan row U → (X → ZMod 2)) ⁻¹'
        (equationVector row '' (U : Set E))) := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨e, he, hval⟩
      refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      exact hval
  have htop : Submodule.span (ZMod 2)
      (((↑) : equationSpan row U → (X → ZMod 2)) ⁻¹'
        (equationVector row '' (U : Set E))) = ⊤ := by
    exact Submodule.span_span_coe_preimage
      (R := ZMod 2) (M := X → ZMod 2)
      (s := equationVector row '' (U : Set E))
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    rw [hrange, htop]
  let b : Module.Basis ↥U (ZMod 2) (equationSpan row U) :=
    Module.Basis.mk hv hspan
  have hb (e : ↥U) : b e = v e := by
    simp [b]
  let psi : equationSpan row U →ₗ[ZMod 2] ZMod 2 :=
    b.constr (ZMod 2) (fun e => rhs e.1)
  refine ⟨psi, ?_, ?_⟩
  · intro e he
    change psi (v ⟨e, he⟩) = rhs e
    rw [← hb]
    exact b.constr_basis (ZMod 2) (fun e => rhs e.1) ⟨e, he⟩
  · intro phi hphi
    apply b.ext
    intro e
    rw [hb e, hphi e.1 e.2]
    rw [← hb e]
    change rhs e.1 = (b.constr (ZMod 2) (fun j => rhs j.1)) (b e)
    exact (b.constr_basis (ZMod 2) (fun j => rhs j.1) e).symm

open PvNP.RealizableHardness
open ActualOccurrenceAllocation

local instance actualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

theorem actual_existsUnique_rhsFunctional
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (U : Finset I.RowId)
    (hU : GoodQuestion I.support U) :
    ∃! psi : equationSpan I.support U →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ U),
        psi ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support U e he⟩ =
          I.rowRhs e := by
  exact existsUnique_rhsFunctional I.support I.rowRhs I.support_card U hU

theorem equationSpan_finrank_eq_card
    (row : E → Finset X)
    (hthree : ∀ e, (row e).card = 3)
    (U : Finset E) (hU : GoodQuestion row U) :
    Module.finrank (ZMod 2) (equationSpan row U) = U.card := by
  let v : ↥U → (X → ZMod 2) := fun e => equationVector row e.1
  have hv : LinearIndependent (ZMod 2) v := by
    exact equationVectors_linearIndependent row U hU.1 (fun e he => by
      apply Finset.card_pos.mp
      rw [hthree e]
      decide)
  have hrange : Set.range v = equationVector row '' (U : Set E) := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨e, he, hval⟩
      exact ⟨⟨e, he⟩, hval⟩
  rw [equationSpan, ← hrange]
  simpa using finrank_span_eq_card hv

end
end PvNP.RealizableHardness.ActualRhsFunctionalConstruction
