import PvNP.RealizableHardness.ActualGraphEdges
import Mathlib.Data.Fintype.Card

/-! Source-only incidence bound for the actual retained nonloop edge occurrences.
Parallel reversal orbits are distinct edges. No simple-graph or degree premise is assumed. -/
namespace PvNP.RealizableHardness.ActualGraphIncidence
open ActualGraphEdges
set_option autoImplicit false
noncomputable section

def Incident {n : Nat} (p : Vertex n) (e : Edge n) : Prop :=
  e.val.1 = p ∨ (reverse e.val).1 = p

instance {n : Nat} (p : Vertex n) (e : Edge n) : Decidable (Incident p e) :=
  inferInstanceAs (Decidable (_ ∨ _))

abbrev IncidentEdge {n : Nat} (p : Vertex n) := {e : Edge n // Incident p e}

def incidentEdges {n : Nat} (p : Vertex n) : Finset (Edge n) :=
  Finset.univ.filter (Incident p)

/-- Use the representative dart when it starts at p, otherwise its reversal. -/
def atPort {n : Nat} (p : Vertex n) (e : Edge n) : Dart n :=
  if e.val.1 = p then e.val else reverse e.val

theorem incident_exclusive {n : Nat} (p : Vertex n) (e : Edge n) :
    ¬ (e.val.1 = p ∧ (reverse e.val).1 = p) := by
  rintro ⟨hs, ht⟩
  exact edge_terminals_distinct e (hs.trans ht.symm)

theorem atPort_source {n : Nat} (p : Vertex n) (e : Edge n) (h : Incident p e) :
    (atPort p e).1 = p := by
  by_cases hs : e.val.1 = p
  · simp [atPort, hs]
  · have ht : (reverse e.val).1 = p := h.resolve_left hs
    simp [atPort, hs, ht]

/-- Canonicalizing either orientation recovers the entire representative dart. -/
theorem canonical_atPort {n : Nat} (p : Vertex n) (e : Edge n) :
    canonical (atPort p e) = e.val := by
  by_cases hs : e.val.1 = p
  · simpa only [atPort, if_pos hs] using canonical_of_rep e.property
  · simp only [atPort, if_neg hs]
    rw [canonical_reverse (rep_nonloop e.property), canonical_of_rep e.property]

theorem atPort_injective {n : Nat} (p : Vertex n) : Function.Injective (atPort p) := by
  intro e f h
  apply Subtype.ext
  have hc := congrArg (@canonical n) h
  simpa only [canonical_atPort] using hc

def incidentLabel {n : Nat} (p : Vertex n) (e : IncidentEdge p) : Fin 3 :=
  (atPort p e.val).2

/-- Equal labels at the fixed source p imply equal full darts, then equal edge orbits. -/
theorem incidentLabel_injective {n : Nat} (p : Vertex n) :
    Function.Injective (incidentLabel p) := by
  intro e f h
  have hd : atPort p e.val = atPort p f.val := by
    apply Prod.ext
    · exact (atPort_source p e.val e.property).trans (atPort_source p f.val f.property).symm
    · exact h
  apply Subtype.ext
  exact atPort_injective p hd

theorem incident_card_le_three {n : Nat} (p : Vertex n) :
    Fintype.card (IncidentEdge p) ≤ 3 := by
  have h := Fintype.card_le_of_injective (incidentLabel p) (incidentLabel_injective p)
  simpa only [Fintype.card_fin] using h

theorem incidentEdges_card {n : Nat} (p : Vertex n) :
    (incidentEdges p).card = Fintype.card (IncidentEdge p) := by
  simpa only [incidentEdges, IncidentEdge] using (Fintype.card_subtype (Incident p)).symm

theorem incidentEdges_card_le_three {n : Nat} (p : Vertex n) :
    (incidentEdges p).card ≤ 3 := by
  rw [incidentEdges_card]
  exact incident_card_le_three p

theorem distinct_incident_labels {n : Nat} (p : Vertex n) (e f : IncidentEdge p)
    (h : e ≠ f) : incidentLabel p e ≠ incidentLabel p f :=
  fun he => h (incidentLabel_injective p he)

end
end PvNP.RealizableHardness.ActualGraphIncidence
