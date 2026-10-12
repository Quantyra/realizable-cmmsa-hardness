import PvNP.RealizableHardness.ActualTaggedVertexPhysicalAcceptance

/-! The independent representative draw in the tagged physical star test can
be carried by full-domain vertices. Constant presentation multiplicity makes
the pushforward exactly uniform at every queried class, and the physical
event is invariant under the choice of presentation. -/

namespace PvNP.RealizableHardness.ActualTaggedVertexPhysicalLaw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedVertexPresentationFiber
open PvNP.RealizableHardness.ActualTaggedVertexPhysicalAcceptance
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

abbrev TaggedIndependentVertexChoice {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) :=
  (i : Fin k) → VertexClassRepresentative I copies (taggedClassOf I copies (vs i))

def independentChoiceToVertices {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (r : TaggedIndependentChoice I copies vs) :
    TaggedIndependentVertexChoice I copies vs :=
  fun i => classRepresentativeVertex I copies (r i)

noncomputable def vertexChoiceToPresentations {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (v : TaggedIndependentVertexChoice I copies vs) :
    TaggedIndependentChoice I copies vs :=
  fun i => Classical.choose (v i).2

theorem vertexChoiceToPresentations_eq_vertex {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (v : TaggedIndependentVertexChoice I copies vs) (i : Fin k) :
    classRepresentativeVertex I copies
      (vertexChoiceToPresentations I copies vs v i) = v i := by
  apply Subtype.ext
  exact Classical.choose_spec (v i).2

private noncomputable def independentChoiceFiberEquiv {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (v : TaggedIndependentVertexChoice I copies vs) :
    {r : TaggedIndependentChoice I copies vs //
      independentChoiceToVertices I copies vs r = v} ≃
      ((i : Fin k) → {r : TaggedClassRepresentative I copies
          (taggedClassOf I copies (vs i)) //
        classRepresentativeVertex I copies r = v i}) where
  toFun r := fun i => ⟨r.1 i, congrFun r.2 i⟩
  invFun r := ⟨fun i => (r i).1, funext (fun i => (r i).2)⟩
  left_inv r := by apply Subtype.ext; funext i; rfl
  right_inv r := by funext i; apply Subtype.ext; rfl

noncomputable instance independentChoiceFiberFintype {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (v : TaggedIndependentVertexChoice I copies vs) :
    Fintype {r : TaggedIndependentChoice I copies vs //
      independentChoiceToVertices I copies vs r = v} := by
  classical
  infer_instance

private theorem independentChoiceFiber_card {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (v : TaggedIndependentVertexChoice I copies vs) :
    Fintype.card {r : TaggedIndependentChoice I copies vs //
      independentChoiceToVertices I copies vs r = v} =
      (2 ^ (J * (2 * h))) ^ k := by
  classical
  rw [Fintype.card_congr (independentChoiceFiberEquiv I copies vs v),
    Fintype.card_pi]
  simp_rw [classRepresentativeFiber_card I copies]
  simp

private theorem independentChoice_card {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) :
    Fintype.card (TaggedIndependentChoice I copies vs) =
      Fintype.card (TaggedIndependentVertexChoice I copies vs) *
        (2 ^ (J * (2 * h))) ^ k := by
  classical
  calc
    Fintype.card (TaggedIndependentChoice I copies vs) =
        Fintype.card (Σ v : TaggedIndependentVertexChoice I copies vs,
          {r : TaggedIndependentChoice I copies vs //
            independentChoiceToVertices I copies vs r = v}) :=
      (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (independentChoiceToVertices I copies vs))).symm
    _ = ∑ v : TaggedIndependentVertexChoice I copies vs,
          Fintype.card {r : TaggedIndependentChoice I copies vs //
            independentChoiceToVertices I copies vs r = v} :=
      Fintype.card_sigma
    _ = ∑ _v : TaggedIndependentVertexChoice I copies vs,
          (2 ^ (J * (2 * h))) ^ k := by
      apply Finset.sum_congr rfl
      intro v _
      exact independentChoiceFiber_card I copies vs v
    _ = _ := by simp [Finset.sum_const]

theorem uniform_independentChoice_pushforward {J h k : Nat}
    (vs : Fin k → TaggedPresentedLeaf I copies J h) :
    pushforward (independentChoiceToVertices I copies vs)
      (uniformLaw (TaggedIndependentChoice I copies vs)) =
        uniformLaw (TaggedIndependentVertexChoice I copies vs) := by
  classical
  apply FiniteLaw.ext
  intro v
  rw [pushforward_apply, uniformLaw_apply]
  simp_rw [uniformLaw_apply (TaggedIndependentChoice I copies vs)]
  have hsum :
      (∑ r : TaggedIndependentChoice I copies vs,
        if independentChoiceToVertices I copies vs r = v then
          (1 : ℚ) / Fintype.card (TaggedIndependentChoice I copies vs) else 0) =
      (Fintype.card {r : TaggedIndependentChoice I copies vs //
        independentChoiceToVertices I copies vs r = v} : ℚ) /
        Fintype.card (TaggedIndependentChoice I copies vs) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [← Fintype.card_subtype
      (fun r : TaggedIndependentChoice I copies vs =>
        independentChoiceToVertices I copies vs r = v)]
    simp [div_eq_mul_inv]
  rw [hsum, independentChoiceFiber_card I copies vs v,
    independentChoice_card I copies vs]
  have hc : (((2 ^ (J * (2 * h))) ^ k : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero _ (pow_ne_zero _ (by decide : (2 : Nat) ≠ 0)))
  have hv : (Fintype.card (TaggedIndependentVertexChoice I copies vs) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (TaggedIndependentVertexChoice I copies vs) ≠ 0)
  field_simp
  simp [Nat.cast_mul, mul_comm]

def taggedVertexPhysicalAccepts {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (v : TaggedIndependentVertexChoice I copies z.leaves) : Prop :=
  taggedPhysicalAccepts I copies C T z
    (vertexChoiceToPresentations I copies z.leaves v)

theorem taggedPhysicalAccepts_eq_vertexEvent {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (r : TaggedIndependentChoice I copies z.leaves) :
    taggedPhysicalAccepts I copies C T z r ↔
      taggedVertexPhysicalAccepts I copies C T z
        (independentChoiceToVertices I copies z.leaves r) := by
  apply taggedPhysicalAccepts_vertex_invariant I copies C T z r
    (vertexChoiceToPresentations I copies z.leaves
      (independentChoiceToVertices I copies z.leaves r))
  intro i
  have h := vertexChoiceToPresentations_eq_vertex I copies z.leaves
    (independentChoiceToVertices I copies z.leaves r) i
  exact congrArg Subtype.val h.symm

private theorem sum_pushforward_pullback
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (μ : FiniteLaw A) (g : B → ℚ) :
    (∑ a, μ.mass a * g (f a)) =
      ∑ b, (pushforward f μ).mass b * g b := by
  classical
  change (∑ a, μ.mass a * g (f a)) =
    ∑ b, (∑ a, if f a = b then μ.mass a else 0) * g b
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- For every fixed raw table, center table, and tagged star, the original
independent presentation mean is exactly the mean over independent uniform
full vertex representatives. The physical RHS and stored-center event is
unchanged. -/
theorem taggedPhysicalMean_eq_vertexMean {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k) :
    uniformMean (TaggedIndependentChoice I copies z.leaves)
      (fun r => if taggedPhysicalAccepts I copies C T z r then 1 else 0) =
    uniformMean (TaggedIndependentVertexChoice I copies z.leaves)
      (fun v => if taggedVertexPhysicalAccepts I copies C T z v then 1 else 0) := by
  classical
  let f := independentChoiceToVertices I copies z.leaves
  let g : TaggedIndependentVertexChoice I copies z.leaves → ℚ :=
    fun v => if taggedVertexPhysicalAccepts I copies C T z v then 1 else 0
  have hpoint (r : TaggedIndependentChoice I copies z.leaves) :
      (if taggedPhysicalAccepts I copies C T z r then (1 : ℚ) else 0) =
        g (f r) := by
    have he := taggedPhysicalAccepts_eq_vertexEvent I copies C T z r
    by_cases hp : taggedPhysicalAccepts I copies C T z r
    · have hv := he.mp hp
      simp [f, g, hp, hv]
    · have hv : ¬ taggedVertexPhysicalAccepts I copies C T z
          (independentChoiceToVertices I copies z.leaves r) := by
        intro h
        exact hp (he.mpr h)
      simp [f, g, hp, hv]
  calc
    uniformMean (TaggedIndependentChoice I copies z.leaves)
        (fun r => if taggedPhysicalAccepts I copies C T z r then 1 else 0) =
        ∑ r, (uniformLaw (TaggedIndependentChoice I copies z.leaves)).mass r *
          g (f r) := by
      unfold uniformMean
      simp_rw [uniformLaw_apply]
      simp_rw [hpoint]
      rw [Finset.sum_div]
      simp [div_eq_mul_inv, mul_comm]
    _ = ∑ v, (pushforward f
        (uniformLaw (TaggedIndependentChoice I copies z.leaves))).mass v * g v :=
      sum_pushforward_pullback f _ g
    _ = ∑ v, (uniformLaw (TaggedIndependentVertexChoice I copies z.leaves)).mass v *
        g v := by
      rw [uniform_independentChoice_pushforward I copies z.leaves]
    _ = uniformMean (TaggedIndependentVertexChoice I copies z.leaves)
        (fun v => if taggedVertexPhysicalAccepts I copies C T z v then 1 else 0) := by
      unfold uniformMean
      simp_rw [uniformLaw_apply]
      rw [Finset.sum_div]
      simp [g, div_eq_mul_inv, mul_comm]

end
end PvNP.RealizableHardness.ActualTaggedVertexPhysicalLaw
