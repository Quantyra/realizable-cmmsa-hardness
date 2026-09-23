import PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
import Mathlib.Tactic

/-! Nonrecursive support for typed Phase-A restriction and index flattening. -/

namespace PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype I]

def originalIndexEmbedding (C : Finset I) : {i : I // i ∈ C} ↪ I :=
  ⟨Subtype.val, Subtype.val_injective⟩

def flattenCarrier (C : Finset I)
    (S : Finset {i : I // i ∈ C}) : Finset I :=
  S.image (originalIndexEmbedding C)

theorem flattenCarrier_subset (C : Finset I)
    (S : Finset {i : I // i ∈ C}) : flattenCarrier C S ⊆ C := by
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  exact j.2

theorem flattenCarrier_card (C : Finset I)
    (S : Finset {i : I // i ∈ C}) : (flattenCarrier C S).card = S.card := by
  exact Finset.card_image_of_injective S (originalIndexEmbedding C).injective

theorem flattenCarrier_nonempty_iff (C : Finset I)
    (S : Finset {i : I // i ∈ C}) : (flattenCarrier C S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj, _⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j.1, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩

noncomputable def flattenCarrierEquiv (C : Finset I)
    (S : Finset {i : I // i ∈ C}) :
    {j : {i : I // i ∈ C} // j ∈ S} ≃
      {i : I // i ∈ flattenCarrier C S} :=
  Equiv.ofBijective
    (fun j => ⟨j.1.1, Finset.mem_image.mpr ⟨j.1, j.2, rfl⟩⟩)
    ⟨(by
        intro j₁ j₂ h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun x : {i : I // i ∈ flattenCarrier C S} => x.1) h),
      (by
        intro i
        rcases Finset.mem_image.mp i.2 with ⟨j, hj, hji⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        apply Subtype.ext
        exact hji)⟩

theorem flattenCarrierEquiv_original_value (C : Finset I)
    (S : Finset {i : I // i ∈ C})
    (j : {j : {i : I // i ∈ C} // j ∈ S}) :
    (flattenCarrierEquiv C S j).1 = j.1.1 := rfl

theorem flattenCarrierEquiv_inverse_original_value (C : Finset I)
    (S : Finset {i : I // i ∈ C})
    (i : {i : I // i ∈ flattenCarrier C S}) :
    ((flattenCarrierEquiv C S).symm i).1.1 = i.1 := by
  have hv := flattenCarrierEquiv_original_value C S ((flattenCarrierEquiv C S).symm i)
  have heq := congrArg Subtype.val ((flattenCarrierEquiv C S).apply_symm_apply i)
  exact hv.symm.trans heq

theorem flattenCarrierEquiv_card (C : Finset I)
    (S : Finset {i : I // i ∈ C}) :
    Fintype.card {j : {i : I // i ∈ C} // j ∈ S} =
      Fintype.card {i : I // i ∈ flattenCarrier C S} :=
  Fintype.card_congr (flattenCarrierEquiv C S)

def nestedAmbient (E : Submodule (ZMod 2) V)
    (H : Hyperplane (V := E)) : Submodule (ZMod 2) V :=
  H.1.map E.subtype

noncomputable def nestedAmbientEquiv
    (E : Submodule (ZMod 2) V) (H : Hyperplane (V := E)) :
    H.1 ≃ₗ[ZMod 2] nestedAmbient E H :=
  Submodule.equivMapOfInjective E.subtype E.injective_subtype H.1

theorem nestedAmbient_le (E : Submodule (ZMod 2) V)
    (H : Hyperplane (V := E)) : nestedAmbient E H ≤ E := by
  rintro x ⟨y, hy, rfl⟩
  exact y.2

theorem nestedAmbientEquiv_coe (E : Submodule (ZMod 2) V)
    (H : Hyperplane (V := E)) (x : H.1) :
    ((nestedAmbientEquiv E H x : nestedAmbient E H) : V) = E.subtype x := rfl

theorem nestedAmbient_finrank (E : Submodule (ZMod 2) V)
    (H : Hyperplane (V := E)) :
    Module.finrank (ZMod 2) (nestedAmbient E H) =
      Module.finrank (ZMod 2) H.1 := by
  exact (nestedAmbientEquiv E H).finrank_eq.symm

theorem nestedAmbient_finrank_add_one (E : Submodule (ZMod 2) V)
    (H : Hyperplane (V := E)) :
    Module.finrank (ZMod 2) (nestedAmbient E H) + 1 =
      Module.finrank (ZMod 2) E := by
  have hh : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) H.1 = 1 := H.2
  have hle : Module.finrank (ZMod 2) H.1 ≤ Module.finrank (ZMod 2) E :=
    H.1.finrank_le
  rw [nestedAmbient_finrank]
  omega

def restrictToAmbient (E A : Submodule (ZMod 2) V) (hAE : A ≤ E) :
    Submodule (ZMod 2) E := A.comap E.subtype

theorem restrictToAmbient_map_recovery
    (E A : Submodule (ZMod 2) V) (hAE : A ≤ E) :
    (restrictToAmbient E A hAE).map E.subtype = A := by
  unfold restrictToAmbient
  rw [Submodule.map_comap_subtype]
  exact inf_eq_right.mpr hAE

theorem restrictToAmbient_finrank
    (E A : Submodule (ZMod 2) V) (hAE : A ≤ E) :
    Module.finrank (ZMod 2) (restrictToAmbient E A hAE) =
      Module.finrank (ZMod 2) A := by
  rw [← Submodule.finrank_map_subtype_eq]
  rw [restrictToAmbient_map_recovery]

def restrictGrass (E : Submodule (ZMod 2) V) {a0 : Nat}
    (Q0 : Grass V a0) (hQE : Q0.val ≤ E) : Grass E a0 :=
  ⟨restrictToAmbient E Q0.val hQE, by
    rw [restrictToAmbient_finrank]
    exact Q0.property⟩

theorem restrictGrass_map_recovery (E : Submodule (ZMod 2) V) {a0 : Nat}
    (Q0 : Grass V a0) (hQE : Q0.val ≤ E) :
    (restrictGrass E Q0 hQE).val.map E.subtype = Q0.val :=
  restrictToAmbient_map_recovery E Q0.val hQE

theorem restrictToAmbient_mono (E A B : Submodule (ZMod 2) V)
    (hAE : A ≤ E) (hBE : B ≤ E) (hAB : A ≤ B) :
    restrictToAmbient E A hAE ≤ restrictToAmbient E B hBE := by
  intro x hx
  exact hAB hx

def restrictFamily (E : Submodule (ZMod 2) V)
    (W : I → Submodule (ZMod 2) V) (hW : ∀ i, W i ≤ E) :
    I → Submodule (ZMod 2) E :=
  fun i => restrictToAmbient E (W i) (hW i)

theorem restrictFamily_map_recovery (E : Submodule (ZMod 2) V)
    (W : I → Submodule (ZMod 2) V) (hW : ∀ i, W i ≤ E) (i : I) :
    (restrictFamily E W hW i).map E.subtype = W i :=
  restrictToAmbient_map_recovery E (W i) (hW i)

theorem restrictFamily_finrank (E : Submodule (ZMod 2) V)
    (W : I → Submodule (ZMod 2) V) (hW : ∀ i, W i ≤ E) (i : I) :
    Module.finrank (ZMod 2) (restrictFamily E W hW i) =
      Module.finrank (ZMod 2) (W i) :=
  restrictToAmbient_finrank E (W i) (hW i)

theorem restrictFamily_injective (E : Submodule (ZMod 2) V)
    (W : I → Submodule (ZMod 2) V) (hW : ∀ i, W i ≤ E)
    (hinj : Function.Injective W) : Function.Injective (restrictFamily E W hW) := by
  intro i j hij
  apply hinj
  have h := congrArg (fun A : Submodule (ZMod 2) E => A.map E.subtype) hij
  rw [restrictFamily_map_recovery, restrictFamily_map_recovery] at h
  exact h

end
end PvNP.RealizableHardness.ActualMZ24PhaseARestrictionSupport
