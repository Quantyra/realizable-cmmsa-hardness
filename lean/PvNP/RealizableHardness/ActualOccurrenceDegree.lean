import PvNP.RealizableHardness.ActualOccurrenceAllocation
import PvNP.RealizableHardness.ActualEqualityCloudDegree

/-! Uncompiled source draft. Degrees count occurrences in the actual original-plus-cloud list.
No runtime, source gap, or hardness theorem is asserted. -/
namespace PvNP.RealizableHardness.ActualOccurrenceDegree
open ActualOccurrenceAllocation
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
variable {N m : Nat} (I : Instance N m)

def containsVar (x : I.GlobalVar)
    (q : (Fin 3 → I.GlobalVar) × ZMod 2) : Bool :=
  decide (x ∈ Finset.univ.image q.1)

def degree (x : I.GlobalVar) : Nat := I.rows.countP (containsVar I x)
def originalDegree (x : I.GlobalVar) : Nat := I.originalRows.countP (containsVar I x)

private theorem countP_as_sum {A : Type*} (p : A → Bool) (l : List A) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]

theorem originalDegree_eq (x : I.GlobalVar) :
    originalDegree I x = (Finset.univ.filter (fun r : Fin m => x ∈ I.originalSupport r)).card := by
  unfold originalDegree Instance.originalRows
  rw [countP_as_sum, List.map_ofFn, Fin.sum_ofFn, Finset.card_filter]
  simp only [Function.comp_def, containsVar, decide_eq_true_eq, Instance.originalSupport]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : x ∈ Finset.univ.image (I.originalRow r) <;> simp [h]

theorem originalDegree_le_one (x : I.GlobalVar) : originalDegree I x ≤ 1 := by
  rw [originalDegree_eq]
  apply Finset.card_le_one.mpr
  intro r hr s hs
  by_contra h
  exact (Finset.disjoint_left.mp (I.original_disjoint r s h))
    (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2

theorem internal_not_original (v : Fin N)
    (z : ActualGraphEdges.Edge (I.size v) × Fin 5) (r : Fin m) :
    I.tag v (Sum.inr z) ∉ I.originalSupport r := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  have he := congrArg I.recover hj
  change I.recover (I.anchor (r,j)) = none at he
  rw [I.recover_anchor] at he
  cases he

theorem original_internal_zero (v : Fin N)
    (z : ActualGraphEdges.Edge (I.size v) × Fin 5) :
    originalDegree I (I.tag v (Sum.inr z)) = 0 := by
  rw [originalDegree_eq]
  simp [internal_not_original]

theorem contains_tag_same (v : Fin N) (x : ActualEqualityCloud.GlobalVar (I.size v))
    (q : (Fin 3 → ActualEqualityCloud.GlobalVar (I.size v)) × ZMod 2) :
    containsVar I (I.tag v x) (I.tagRow v q) =
      ActualEqualityCloudDegree.containsVar x q := by
  unfold containsVar ActualEqualityCloudDegree.containsVar Instance.tagRow
  congr 1
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
    (I.tag v).injective.eq_iff]

theorem contains_tag_other (v w : Fin N) (h : v ≠ w)
    (x : ActualEqualityCloud.GlobalVar (I.size v))
    (q : (Fin 3 → ActualEqualityCloud.GlobalVar (I.size w)) × ZMod 2) :
    containsVar I (I.tag v x) (I.tagRow w q) = false := by
  apply decide_eq_false_iff_not.mpr
  intro hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
  exact h (congrArg Sigma.fst hj).symm

theorem tagged_count_same (v : Fin N) (x : ActualEqualityCloud.GlobalVar (I.size v))
    (l : List ((Fin 3 → ActualEqualityCloud.GlobalVar (I.size v)) × ZMod 2)) :
    (l.map (I.tagRow v)).countP (containsVar I (I.tag v x)) =
      l.countP (ActualEqualityCloudDegree.containsVar x) := by
  induction l with
  | nil => rfl
  | cons q l ih => simp only [List.map_cons, List.countP_cons, contains_tag_same, ih]

theorem tagged_count_other (v w : Fin N) (h : v ≠ w)
    (x : ActualEqualityCloud.GlobalVar (I.size v))
    (l : List ((Fin 3 → ActualEqualityCloud.GlobalVar (I.size w)) × ZMod 2)) :
    (l.map (I.tagRow w)).countP (containsVar I (I.tag v x)) = 0 := by
  induction l with
  | nil => rfl
  | cons q l ih => simp [contains_tag_other I v w h, ih]

theorem degree_eq_original_add_cloud (v : Fin N)
    (x : ActualEqualityCloud.GlobalVar (I.size v)) :
    degree I (I.tag v x) = originalDegree I (I.tag v x) +
      ActualEqualityCloudDegree.degree x := by
  unfold degree Instance.rows
  rw [List.countP_append, List.countP_flatMap]
  change originalDegree I (I.tag v x) + _ = _
  congr 1
  dsimp only [Function.comp_def]
  unfold ActualEqualityCloudDegree.degree
  rw [← List.sum_toFinset _ (List.nodup_finRange N)]
  have hu : (List.finRange N).toFinset = Finset.univ := by ext w; simp
  rw [hu, Finset.sum_eq_single v]
  · exact tagged_count_same I v x (ActualEqualityCloud.rows (I.size v))
  · intro w _ hw
    change ((ActualEqualityCloud.rows (I.size w)).map (I.tagRow w)).countP
      (containsVar I (I.tag v x)) = 0
    exact tagged_count_other I v w (Ne.symm hw) x (ActualEqualityCloud.rows (I.size w))
  · simp

theorem port_degree_le_four (v : Fin N) (p : ActualGraphEdges.Vertex (I.size v)) :
    degree I (I.tag v (Sum.inl p)) ≤ 4 := by
  rw [degree_eq_original_add_cloud]
  have ho := originalDegree_le_one I (I.tag v (Sum.inl p))
  have hc := ActualEqualityCloudDegree.port_degree_le_three p
  omega

theorem internal_degree_exact (v : Fin N)
    (e : ActualGraphEdges.Edge (I.size v)) (i : Fin 5) :
    degree I (I.tag v (Sum.inr (e,i))) = 2 := by
  rw [degree_eq_original_add_cloud, original_internal_zero,
    ActualEqualityCloudDegree.internal_degree_exact, Nat.zero_add]

theorem degree_le_four (x : I.GlobalVar) : degree I x ≤ 4 := by
  rcases x with ⟨v,p | ⟨e,i⟩⟩
  · exact port_degree_le_four I v p
  · have h := internal_degree_exact I v e i
    change degree I (I.tag v (Sum.inr (e,i))) ≤ 4
    omega

theorem degree_le_ten (x : I.GlobalVar) : degree I x ≤ 10 :=
  (degree_le_four I x).trans (by decide)

end
end PvNP.RealizableHardness.ActualOccurrenceDegree
