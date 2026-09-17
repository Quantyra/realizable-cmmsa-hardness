import PvNP.RealizableHardness.ActualGraphIncidence

/-! Source-only checks: not compiled or independently accepted. -/
namespace PvNP.RealizableHardness.ActualGraphIncidenceChecks
open ActualGraphEdges ActualGraphIncidence

#print axioms incident_exclusive
#print axioms atPort_source
#print axioms canonical_atPort
#print axioms atPort_injective
#print axioms incidentLabel_injective
#print axioms incident_card_le_three
#print axioms incidentEdges_card
#print axioms incidentEdges_card_le_three
#print axioms distinct_incident_labels

#check incidentLabel_injective
#check incidentEdges_card_le_three

example {n : Nat} (p : Vertex n) : (incidentEdges p).card ≤ 3 :=
  incidentEdges_card_le_three p
example {n : Nat} (p : Vertex n) (e : IncidentEdge p) : (atPort p e.val).1 = p :=
  atPort_source p e.val e.property
example {n : Nat} (p : Vertex n) (e : Edge n) : canonical (atPort p e) = e.val :=
  canonical_atPort p e
example {n : Nat} (p : Vertex n) (e f : IncidentEdge p) (h : e ≠ f) :
    incidentLabel p e ≠ incidentLabel p f := distinct_incident_labels p e f h
example (p : Vertex 0) : False := Fin.elim0 p.1

end PvNP.RealizableHardness.ActualGraphIncidenceChecks
