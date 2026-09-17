/- UNCOMPILED companion source port. No Lean4.34 verification or acceptance has run for this file. -/
import PvNP.RealizableHardness.GrassmannIncidence
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fintype.BigOperators

/-! UNCOMPILED source draft. Exact GF(2) subspace counting by independent frames.
No Gaussian ratio estimate, posterior bound, runtime, or hardness result is asserted. -/
namespace PvNP.RealizableHardness.GrassmannCounting
open scoped BigOperators
open TripleRestrictionRank

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Ordered independent a-frames in the actual vector space. -/
def Frame (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] (a : ℕ) :=
  {v : Fin a → V // LinearIndependent (ZMod 2) v}

/-- Actual submodules of dimension a. -/
def Grass (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] (a : ℕ) :=
  {Q : Submodule (ZMod 2) V // Module.finrank (ZMod 2) Q = a}

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

instance frameFinite : Finite (Frame V a) := by unfold Frame; infer_instance
instance frameFintype : Fintype (Frame V a) := Fintype.ofFinite _
instance grassFinite : Finite (Grass V a) := by
  letI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun Q => (Q : Set V)) SetLike.coe_injective
  unfold Grass
  infer_instance
instance grassFintype : Fintype (Grass V a) := Fintype.ofFinite _

/-- Forget the containing subspace, retaining the ordered ambient frame. -/
def flatten (s : (Q : Grass V a) × Frame Q.val a) : Frame V a :=
  ⟨fun i => (s.2.val i).val, s.2.property.map' s.1.val.subtype s.1.val.ker_subtype⟩

lemma span_flatten (Q : Grass V a) (f : Frame Q.val a) :
    Submodule.span (ZMod 2) (Set.range (flatten ⟨Q, f⟩).val) = Q.val := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f.val i).property
  · rw [finrank_span_eq_card (flatten ⟨Q, f⟩).property, Fintype.card_fin, Q.property]

lemma flatten_injective : Function.Injective (flatten (V := V) (a := a)) := by
  rintro ⟨Q, f⟩ ⟨R, g⟩ h
  have hQR : Q = R := by
    apply Subtype.ext
    rw [← span_flatten Q f, ← span_flatten R g, h]
  cases hQR
  have hfg : f = g := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val h) i
  cases hfg
  rfl

lemma flatten_surjective : Function.Surjective (flatten (V := V) (a := a)) := by
  intro f
  let Q : Grass V a := ⟨Submodule.span (ZMod 2) (Set.range f.val), by
    simpa using finrank_span_eq_card f.property⟩
  let g : Frame Q.val a :=
    ⟨fun i => ⟨f.val i, Submodule.subset_span (Set.mem_range_self i)⟩,
      linearIndependent_span f.property⟩
  exact ⟨⟨Q, g⟩, Subtype.ext rfl⟩

/-- Explicit counted-bases decomposition; every frame determines its own span. -/
def frameEquiv : ((Q : Grass V a) × Frame Q.val a) ≃ Frame V a :=
  Equiv.ofBijective flatten ⟨flatten_injective, flatten_surjective⟩

/-- Number of ordered independent a-frames, as a natural product. -/
def frameProduct (n a : ℕ) : ℕ := ∏ i : Fin a, (2 ^ n - 2 ^ i.val)

lemma card_frame (ha : a ≤ Module.finrank (ZMod 2) V) :
    Fintype.card (Frame V a) = frameProduct (Module.finrank (ZMod 2) V) a := by
  have h := card_linearIndependent (K := ZMod 2) (V := V) ha
  change Nat.card (Frame V a) = _ at h
  rw [Nat.card_eq_fintype_card] at h
  simpa [frameProduct] using h

lemma card_internal_frame (Q : Grass V a) :
    Fintype.card (Frame Q.val a) = frameProduct a a := by
  simpa [Q.property] using (card_frame (V := Q.val) (a := a) (by rw [Q.property]))

/-- The exact double count, before natural division. -/
lemma card_grass_mul (ha : a ≤ Module.finrank (ZMod 2) V) :
    Fintype.card (Grass V a) * frameProduct a a =
      frameProduct (Module.finrank (ZMod 2) V) a := by
  have h := Fintype.card_congr (frameEquiv (V := V) (a := a))
  rw [Fintype.card_sigma, card_frame ha] at h
  simpa only [card_internal_frame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using h

lemma frameProduct_self_pos (a : ℕ) : 0 < frameProduct a a := by
  apply Finset.prod_pos
  intro i _
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) i.isLt)

/-- Gaussian binomial at q=2, including the out-of-range convention. -/
def gaussian (n a : ℕ) : ℕ :=
  if a ≤ n then frameProduct n a / frameProduct a a else 0

lemma card_grass_of_le (ha : a ≤ Module.finrank (ZMod 2) V) :
    Fintype.card (Grass V a) =
      frameProduct (Module.finrank (ZMod 2) V) a / frameProduct a a := by
  rw [← card_grass_mul ha, Nat.mul_div_left _ (frameProduct_self_pos a)]

lemma card_grass_of_lt (ha : Module.finrank (ZMod 2) V < a) :
    Fintype.card (Grass V a) = 0 := by
  letI : IsEmpty (Grass V a) := ⟨fun Q => by
    have h := Q.val.finrank_le
    rw [Q.property] at h
    exact (not_le_of_gt ha) h⟩
  exact Fintype.card_eq_zero

lemma card_grass : Fintype.card (Grass V a) = gaussian (Module.finrank (ZMod 2) V) a := by
  by_cases ha : a ≤ Module.finrank (ZMod 2) V
  · rw [gaussian, if_pos ha, card_grass_of_le ha]
  · rw [gaussian, if_neg ha, card_grass_of_lt (Nat.lt_of_not_ge ha)]

lemma gaussian_zero (n : ℕ) : gaussian n 0 = 1 := by simp [gaussian, frameProduct]
lemma gaussian_of_lt (h : n < a) : gaussian n a = 0 := by
  simp [gaussian, Nat.not_le_of_gt h]
lemma gaussian_self (n : ℕ) : gaussian n n = 1 := by
  simp only [gaussian, le_refl, ite_true]
  exact Nat.div_self (frameProduct_self_pos n)

/-- Subspaces of W are exactly ambient subspaces contained in W. -/
def includeSubspace (W : Submodule (ZMod 2) V) (Q : Grass W a) :
    {R : Grass V a // R.val ≤ W} :=
  ⟨⟨Q.val.map W.subtype, by rw [Submodule.finrank_map_subtype_eq, Q.property]⟩,
    W.map_subtype_le Q.val⟩

lemma include_injective (W : Submodule (ZMod 2) V) :
    Function.Injective (includeSubspace (a := a) W) := by
  intro Q R h
  apply Subtype.ext
  have hm : Q.val.map W.subtype = R.val.map W.subtype :=
    congrArg (fun x => x.val.val) h
  have hc := congrArg (fun S => S.comap W.subtype) hm
  simpa only [Submodule.comap_map_eq_of_injective (f := W.subtype) W.injective_subtype] using hc

lemma include_surjective (W : Submodule (ZMod 2) V) :
    Function.Surjective (includeSubspace (a := a) W) := by
  intro R
  have he : (R.val.val.comap W.subtype).map W.subtype = R.val.val := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr R.property]
  let Q : Grass W a := ⟨R.val.val.comap W.subtype, by
    rw [← Submodule.finrank_map_subtype_eq W, he, R.val.property]⟩
  refine ⟨Q, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

def containedEquiv (W : Submodule (ZMod 2) V) :
    Grass W a ≃ {R : Grass V a // R.val ≤ W} :=
  Equiv.ofBijective (includeSubspace W) ⟨include_injective W, include_surjective W⟩

lemma card_contained (W : Submodule (ZMod 2) V) :
    Nat.card {R : Grass V a // R.val ≤ W} = gaussian (Module.finrank (ZMod 2) W) a := by
  rw [← Nat.card_congr (containedEquiv (a := a) W), Nat.card_eq_fintype_card, card_grass]

/-- The accepted sampler denominator is the actual Gaussian count in retained d. -/
lemma incidenceCount_eq (d : Draw J) (a : ℕ) :
    GrassmannIncidence.incidenceCount d a =
      gaussian (Module.finrank (ZMod 2) (retained d)) a := by
  classical
  let e : {Q // Q ∈ GrassmannIncidence.fibre d a} ≃
      {Q : Grass (Vector J) a // Q.val ≤ retained d} := {
    toFun := fun Q => ⟨Q.val, (Finset.mem_filter.mp Q.property).2⟩
    invFun := fun Q => ⟨Q.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Q.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have h := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h
  exact h.trans (card_contained (a := a) (retained d))

lemma incidenceCount_zero (d : Draw J) : GrassmannIncidence.incidenceCount d 0 = 1 := by
  rw [incidenceCount_eq, gaussian_zero]

lemma incidenceCount_of_lt (d : Draw J) (ha : Module.finrank (ZMod 2) (retained d) < a) :
    GrassmannIncidence.incidenceCount d a = 0 := by
  rw [incidenceCount_eq, gaussian_of_lt ha]

end
end PvNP.RealizableHardness.GrassmannCounting
