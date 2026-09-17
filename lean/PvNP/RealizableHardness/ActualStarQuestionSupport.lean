import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

namespace PvNP.RealizableHardness.ActualStarQuestionSupport
variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

def questionSupport (row : E → Finset X) (U : Finset E) : Finset X := U.biUnion row

def GoodQuestion (row : E → Finset X) (U : Finset E) : Prop :=
  (U : Set E).Pairwise (fun e f => Disjoint (row e) (row f)) ∧
  ∀ e ∈ U, ∀ f ∈ U, e ≠ f →
    ∀ g : E, ∀ x ∈ row e, ∀ y ∈ row f,
      x ∈ row g → y ∈ row g → False

theorem excluded_row_points_eq
    (row : E → Finset X)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ (row f)).card ≤ 1)
    (U : Finset E) (hU : GoodQuestion row U)
    (e : E) (he : e ∉ U)
    (x y : X) (hx : x ∈ row e) (hy : y ∈ row e)
    (hxU : x ∈ questionSupport row U)
    (hyU : y ∈ questionSupport row U) : x = y := by
  classical
  rw [questionSupport, Finset.mem_biUnion] at hxU hyU
  obtain ⟨f, hf, hxf⟩ := hxU
  obtain ⟨g, hg, hyg⟩ := hyU
  by_cases hfg : f = g
  · subst g
    have hef : e ≠ f := by
      intro h
      apply he
      simpa only [h] using hf
    exact (Finset.card_le_one.mp (hlinear e f hef)) x
      (Finset.mem_inter.mpr ⟨hx, hxf⟩) y (Finset.mem_inter.mpr ⟨hy, hyg⟩)
  · exact False.elim (hU.2 f hf g hg hfg e x hxf y hyg hx hy)

theorem excluded_row_overlap_le_one
    (row : E → Finset X)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ (row f)).card ≤ 1)
    (U : Finset E) (hU : GoodQuestion row U)
    (e : E) (he : e ∉ U) :
    ((row e) ∩ questionSupport row U).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  rcases Finset.mem_inter.mp hx with ⟨hxe, hxU⟩
  rcases Finset.mem_inter.mp hy with ⟨hye, hyU⟩
  exact excluded_row_points_eq row hlinear U hU e he x y hxe hye hxU hyU

theorem new_row_private_coordinate
    (row : E → Finset X)
    (hthree : ∀ e, (row e).card = 3)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ (row f)).card ≤ 1)
    (U U' : Finset E)
    (hU : GoodQuestion row U) (hU' : GoodQuestion row U')
    (e : E) (he : e ∈ U') (hnew : e ∉ U) :
    ∃ x ∈ row e,
      x ∉ questionSupport row U ∧
      x ∉ questionSupport row (U'.erase e) := by
  classical
  have hoverlap : ((row e) ∩ questionSupport row U).card ≤ 1 :=
    excluded_row_overlap_le_one row hlinear U hU e hnew
  have hex : ∃ x ∈ row e, x ∉ questionSupport row U := by
    by_contra h
    push Not at h
    have hsub : row e ⊆ (row e) ∩ questionSupport row U := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hx, h x hx⟩
    have hcard : (row e).card ≤ ((row e) ∩ questionSupport row U).card :=
      Finset.card_le_card hsub
    rw [hthree e] at hcard
    omega
  obtain ⟨x, hxrow, hxnotU⟩ := hex
  refine ⟨x, hxrow, hxnotU, ?_⟩
  intro hxerase
  rw [questionSupport, Finset.mem_biUnion] at hxerase
  obtain ⟨f, hf, hxf⟩ := hxerase
  have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
  have hfU' : f ∈ U' := (Finset.mem_erase.mp hf).2
  have hdis : Disjoint (row e) (row f) := hU'.1 he hfU' (Ne.symm hfe)
  exact (Finset.disjoint_left.mp hdis) hxrow hxf

#print axioms excluded_row_points_eq
#print axioms excluded_row_overlap_le_one
#print axioms new_row_private_coordinate
end PvNP.RealizableHardness.ActualStarQuestionSupport
