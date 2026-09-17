import PvNP.RealizableHardness.ActualOccurrenceCompleteness
import PvNP.RealizableHardness.ActualCloudSoundness

/-! Uncompiled source draft: actual all-port majority charging and conditional
NO-gap transfer. The explicit source NO promise is not a hardness theorem. -/
namespace PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance
open scoped BigOperators
set_option autoImplicit false
noncomputable section
variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)

def decoded (x : I.GlobalVar → ZMod 2) (v : Fin N) : ZMod 2 :=
  ActualCloudSoundness.majority (I.restrictCloud x v)

def totalMinority (x : I.GlobalVar → ZMod 2) : Nat :=
  ∑ v : Fin N, ActualCloudSoundness.minority (I.restrictCloud x v)

def originalBadIndex (x : I.GlobalVar → ZMod 2) (r : Fin m) : Bool :=
  I.badRow x (I.originalRow r, I.rhs r)

/-- Only actual source slots occur here, not arbitrary ports passed through recover. -/
abbrev BadSlot (x : I.GlobalVar → ZMod 2) :=
  {o : Slot m // x (I.anchor o) ≠ I.decoded x (I.owner o)}

abbrev ChangedRow (x : I.GlobalVar → ZMod 2) :=
  {r : Fin m // I.sourceBadRow (I.decoded x) r = true ∧ I.originalBadIndex x r = false}

abbrev MinorityPorts (x : I.GlobalVar → ZMod 2) :=
  Σ v : Fin N, {p : ActualGraphEdges.Vertex (I.size v) //
    I.restrictCloud x v (Sum.inl p) ≠ I.decoded x v}

theorem changed_has_bad_slot (x : I.GlobalVar → ZMod 2) (r : I.ChangedRow x) :
    ∃ i : Fin 3, x (I.anchor (r.val,i)) ≠ I.decoded x (I.owner (r.val,i)) := by
  by_contra hn
  push_neg at hn
  have he : I.originalBadIndex x r.val = I.sourceBadRow (I.decoded x) r.val := by
    unfold originalBadIndex badRow sourceBadRow
    change decide (¬ (x (I.anchor (r.val,0)) + x (I.anchor (r.val,1)) +
      x (I.anchor (r.val,2)) = I.rhs r.val)) = _
    rw [hn 0, hn 1, hn 2]
    rfl
  rw [r.property.1] at he
  exact Bool.false_ne_true (r.property.2.symm.trans he)

def chargeSlot (x : I.GlobalVar → ZMod 2) (r : I.ChangedRow x) : I.BadSlot x :=
  ⟨(r.val, Classical.choose (I.changed_has_bad_slot x r)),
    Classical.choose_spec (I.changed_has_bad_slot x r)⟩

theorem chargeSlot_injective (x : I.GlobalVar → ZMod 2) :
    Function.Injective (I.chargeSlot x) := by
  intro r s h
  apply Subtype.ext
  exact congrArg (fun o : I.BadSlot x => o.val.1) h

def badSlotPort (x : I.GlobalVar → ZMod 2) (o : I.BadSlot x) : I.MinorityPorts x :=
  ⟨I.owner o.val, ⟨(I.ordinal (I.owner o.val) ⟨o.val,rfl⟩, 0), o.property⟩⟩

theorem badSlotPort_injective (x : I.GlobalVar → ZMod 2) :
    Function.Injective (I.badSlotPort x) := by
  intro o t h
  have he := congrArg (fun q : I.MinorityPorts x =>
    (⟨q.1, Sum.inl q.2.val⟩ : I.GlobalVar)) h
  apply Subtype.ext
  exact I.anchor_injective he

theorem minorityPorts_card (x : I.GlobalVar → ZMod 2) :
    Fintype.card (I.MinorityPorts x) = I.totalMinority x := by
  classical
  rw [Fintype.card_sigma]
  unfold totalMinority
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.card_subtype]
  rfl

theorem badSlot_card_le (x : I.GlobalVar → ZMod 2) :
    Fintype.card (I.BadSlot x) ≤ I.totalMinority x := by
  rw [← I.minorityPorts_card x]
  exact Fintype.card_le_of_injective _ (I.badSlotPort_injective x)

theorem changedRow_card_le (x : I.GlobalVar → ZMod 2) :
    Fintype.card (I.ChangedRow x) ≤ I.totalMinority x :=
  (Fintype.card_le_of_injective _ (I.chargeSlot_injective x)).trans (I.badSlot_card_le x)

private theorem finite_countP (k : Nat) (p : Fin k → Bool) :
    (List.finRange k).countP p = ∑ r : Fin k, if p r then 1 else 0 := by
  have hl (l : List (Fin k)) (q : Fin k → Bool) :
      l.countP q = (l.map (fun a => if q a then 1 else 0)).sum := by
    induction l with
    | nil => rfl
    | cons a l ih => cases h : q a <;> simp [h, ih, Nat.add_comm]
  rw [hl, ← Fin.sum_univ_def]

theorem originalViolations_index_sum (x : I.GlobalVar → ZMod 2) :
    I.originalViolations x = ∑ r : Fin m, if I.originalBadIndex x r then 1 else 0 := by
  unfold originalViolations originalRows
  rw [List.ofFn_eq_map, List.countP_map]
  exact finite_countP _ _

theorem decoded_charging (x : I.GlobalVar → ZMod 2) :
    I.sourceViolations (I.decoded x) ≤ I.originalViolations x + I.totalMinority x := by
  classical
  have h : I.sourceViolations (I.decoded x) ≤
      I.originalViolations x + Fintype.card (I.ChangedRow x) := by
    rw [sourceViolations, finite_countP, I.originalViolations_index_sum]
    rw [Fintype.card_subtype, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    cases hs : I.sourceBadRow (I.decoded x) r <;>
      cases ho : I.originalBadIndex x r <;> simp [hs, ho]
  exact h.trans (Nat.add_le_add_left (I.changedRow_card_le x) _)

theorem clouds_lower (x : I.GlobalVar → ZMod 2) :
    FixedPortCycleFamily.kappa * (I.totalMinority x : Real) ≤
      ((∑ v : Fin N, ActualEqualityCloud.rowsViolations (I.restrictCloud x v) : Nat) : Real) := by
  unfold totalMinority
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => ActualCloudSoundness.rowsViolations_lower _)

def soundnessCoefficient : Real := min 1 FixedPortCycleFamily.kappa

theorem soundnessCoefficient_pos : 0 < soundnessCoefficient :=
  lt_min (by norm_num) FixedPortCycleFamily.kappa_pos

theorem violations_lower_decoded (x : I.GlobalVar → ZMod 2) :
    soundnessCoefficient * (I.sourceViolations (I.decoded x) : Real) ≤
      (I.violations x : Real) := by
  have hc : (I.sourceViolations (I.decoded x) : Real) ≤
      (I.originalViolations x : Real) + (I.totalMinority x : Real) := by
    exact_mod_cast I.decoded_charging x
  have hg := I.clouds_lower x
  have h0 : soundnessCoefficient ≤ 1 := min_le_left _ _
  have hk : soundnessCoefficient ≤ FixedPortCycleFamily.kappa := min_le_right _ _
  have hnon := le_of_lt soundnessCoefficient_pos
  have horig := mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg (I.originalViolations x))
  have hminor := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (I.totalMinority x))
  have hscale := mul_le_mul_of_nonneg_left hc hnon
  rw [I.violations_eq_original_add_clouds]
  push_cast at hg
  push_cast
  nlinarith

/-- Conditional transfer of an explicit source NO promise, not its NP-hardness. -/
theorem conditional_no_count (delta : Real) (x : I.GlobalVar → ZMod 2)
    (hno : ∀ y : Fin N → ZMod 2, delta * (m : Real) ≤ (I.sourceViolations y : Real)) :
    soundnessCoefficient * delta * (m : Real) ≤ (I.violations x : Real) := by
  calc
    _ = soundnessCoefficient * (delta * (m : Real)) := by ring
    _ ≤ soundnessCoefficient * (I.sourceViolations (I.decoded x) : Real) :=
      mul_le_mul_of_nonneg_left (hno (I.decoded x)) (le_of_lt soundnessCoefficient_pos)
    _ ≤ _ := I.violations_lower_decoded x

theorem conditional_no_fraction (delta : Real) (hdelta : 0 ≤ delta) (hm : 0 < m)
    (hno : ∀ y : Fin N → ZMod 2, delta * (m : Real) ≤ (I.sourceViolations y : Real))
    (x : I.GlobalVar → ZMod 2) :
    soundnessCoefficient * delta / (1 + 18 * (FixedPortCycleFamily.degree : Real)) ≤
      (I.violations x : Real) / (I.rows.length : Real) := by
  have ht : (0 : Real) < I.rows.length := by exact_mod_cast I.rows_length_pos hm
  have hc : (0 : Real) < 1 + 18 * (FixedPortCycleFamily.degree : Real) := by positivity
  have hb : (I.rows.length : Real) ≤
      (1 + 18 * (FixedPortCycleFamily.degree : Real)) * (m : Real) := by
    exact_mod_cast I.rows_length_le
  have hv := I.conditional_no_count delta x hno
  have hn : 0 ≤ soundnessCoefficient * delta :=
    mul_nonneg (le_of_lt soundnessCoefficient_pos) hdelta
  apply (div_le_div_iff₀ hc ht).mpr
  have h1 := mul_le_mul_of_nonneg_left hb hn
  have h2 := mul_le_mul_of_nonneg_right hv (le_of_lt hc)
  nlinarith

end
end PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance
