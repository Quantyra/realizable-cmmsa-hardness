import PvNP.RealizableHardness.ActualEqualityCloud
import PvNP.RealizableHardness.ActualGraphIncidence

/-! Uncompiled source draft: degrees count occurrences in the actual generated row list.
No original-source rows, global degree-four theorem, or runtime bound is asserted. -/
namespace PvNP.RealizableHardness.ActualEqualityCloudDegree
open ActualGraphEdges ActualEqualityCloud ActualGraphIncidence
open scoped BigOperators
set_option autoImplicit false
noncomputable section

def containsVar {n : Nat} (v : GlobalVar n)
    (q : (Fin 3 → GlobalVar n) × ZMod 2) : Bool :=
  decide (v ∈ Finset.univ.image q.1)

/-- Count rows with multiplicity, rather than deduplicating row values. -/
def degree {n : Nat} (v : GlobalVar n) : Nat :=
  (rows n).countP (containsVar v)

private theorem countP_as_sum {A : Type*} (p : A → Bool) (l : List A) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]

theorem local_count {n : Nat} (v : GlobalVar n) (e : Edge n) :
    (localRows e).countP (containsVar v) =
      EqualityGadget.relabeledDegree (embedding e) v := by
  rw [countP_as_sum, localRows_eq, List.map_ofFn, Fin.sum_ofFn]
  unfold EqualityGadget.relabeledDegree
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Function.comp_def, containsVar, decide_eq_true_eq]
  unfold ActualEqualityCloud.row
  rw [← EqualityGadget.relabeledSupport_eq]

theorem degree_eq_sum {n : Nat} (v : GlobalVar n) :
    degree v = ∑ e : Edge n, EqualityGadget.relabeledDegree (embedding e) v := by
  unfold degree rows
  rw [List.countP_flatMap]
  simp_rw [Function.comp_def, local_count]
  rw [← List.sum_toFinset _ (edgeList_nodup n), edgeList_toFinset]

theorem port_outside {n : Nat} (p : Vertex n) (e : Edge n)
    (h : ¬ Incident p e) : Sum.inl p ∉ Set.range (embedding e) := by
  rintro ⟨u, hu⟩
  have hs : e.val.1 ≠ p := fun he => h (Or.inl he)
  have ht : (reverse e.val).1 ≠ p := fun he => h (Or.inr he)
  fin_cases u <;> simp_all [embedding, embedFn]

theorem local_port_degree {n : Nat} (p : Vertex n) (e : Edge n) :
    EqualityGadget.relabeledDegree (embedding e) (Sum.inl p) =
      if Incident p e then 1 else 0 := by
  by_cases h : Incident p e
  · rw [if_pos h]
    rcases h with hs | ht
    · subst p
      simpa [embedding, embedFn] using
        EqualityGadget.relabeled_degree (embedding e) (0 : EqualityGadget.Var)
    · subst p
      simpa [embedding, embedFn] using
        EqualityGadget.relabeled_degree (embedding e) (1 : EqualityGadget.Var)
  · rw [if_neg h]
    exact EqualityGadget.relabeled_degree_outside (embedding e) _ (port_outside p e h)

theorem port_degree_eq_incidence {n : Nat} (p : Vertex n) :
    degree (Sum.inl p) = (incidentEdges p).card := by
  rw [degree_eq_sum]
  simp_rw [local_port_degree]
  simp only [incidentEdges, Finset.card_filter]

theorem port_degree_le_three {n : Nat} (p : Vertex n) : degree (Sum.inl p) ≤ 3 := by
  rw [port_degree_eq_incidence]
  exact incidentEdges_card_le_three p

/-- Fresh edge tags exclude every internal variable from every other copy. -/
theorem internal_outside {n : Nat} (e f : Edge n) (i : Fin 5) (h : e ≠ f) :
    Sum.inr (e,i) ∉ Set.range (embedding f) := by
  rintro ⟨u, hu⟩
  have hf : f ≠ e := Ne.symm h
  fin_cases u <;> simp_all [embedding, embedFn]

theorem local_internal_degree {n : Nat} (e : Edge n) (i : Fin 5) :
    EqualityGadget.relabeledDegree (embedding e) (Sum.inr (e,i)) = 2 := by
  have h := EqualityGadget.relabeled_degree (embedding e)
  fin_cases i
  · simpa [embedding, embedFn] using h (2 : EqualityGadget.Var)
  · simpa [embedding, embedFn] using h (3 : EqualityGadget.Var)
  · simpa [embedding, embedFn] using h (4 : EqualityGadget.Var)
  · simpa [embedding, embedFn] using h (5 : EqualityGadget.Var)
  · simpa [embedding, embedFn] using h (6 : EqualityGadget.Var)

theorem internal_degree_exact {n : Nat} (e : Edge n) (i : Fin 5) :
    degree (Sum.inr (e,i)) = 2 := by
  rw [degree_eq_sum]
  rw [Finset.sum_eq_single e]
  · exact local_internal_degree e i
  · intro f _ hfe
    exact EqualityGadget.relabeled_degree_outside (embedding f) _
      (internal_outside e f i (Ne.symm hfe))
  · simp

theorem localRows_length {n : Nat} (e : Edge n) : (localRows e).length = 4 := by
  rw [localRows_eq]
  simp

theorem rows_length (n : Nat) : (rows n).length = 4 * Fintype.card (Edge n) := by
  have h (l : List (Edge n)) : (l.flatMap localRows).length = 4 * l.length := by
    induction l with
    | nil => simp
    | cons e l ih => simp [ih, localRows_length, Nat.mul_add, Nat.add_comm]
  rw [rows, h, edgeList_length]

end
end PvNP.RealizableHardness.ActualEqualityCloudDegree
