import PvNP.RealizableHardness.ActualSourceStarLaw
import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
import Mathlib.Logic.Equiv.Prod

/-! The uniform marginal of each ordered leaf occurrence in the actual
ordinary star law. This is used to charge a changed table on a set X by
m times its uniform Grassmann mass, even when leaf occurrences repeat. -/
namespace PvNP.RealizableHardness.ActualOrdinaryStarLeafMarginal

open PvNP.RealizableHardness
open GrassmannCounting GrassmannFlagPosterior ActualFiniteLaw ActualSourceStarLaw
open ActualChangedAmbient8SBoundary
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem uniform_function_coordinate_average
    {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → Rat) :
    (∑ s : ι → α, f (s i)) / (Fintype.card (ι → α) : Rat) =
      (∑ x : α, f x) / (Fintype.card α : Rat) := by
  classical
  let B := {j : ι // j ≠ i} → α
  let e : (ι → α) ≃ α × B := Equiv.funSplitAt i α
  have hcard : Fintype.card (ι → α) = Fintype.card α * Fintype.card B := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  have hsum : (∑ s : ι → α, f (s i)) =
      (Fintype.card B : Rat) * ∑ x : α, f x := by
    calc
      _ = ∑ p : α × B, f p.1 := Equiv.sum_comp e (fun p => f p.1)
      _ = ∑ x : α, ∑ _y : B, f x := Fintype.sum_prod_type _
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hα : (Fintype.card α : Rat) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  have hB : (Fintype.card B : Rat) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  rw [hsum, hcard]
  push_cast
  field_simp
  <;> ring

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {t d m : Nat}

private theorem extension_sum_eq_incidence
    (K : Grass V t) (f : Grass V d → Rat) :
    (∑ L : Extension K d, f L.1) =
      ∑ L : Grass V d, if K.val ≤ L.val then f L else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

private theorem sum_extension_sums
    (f : Grass V d → Rat) :
    (∑ K : Grass V t, ∑ L : Extension K d, f L.1) =
      (gaussian d t : Rat) * ∑ L : Grass V d, f L := by
  simp_rw [extension_sum_eq_incidence]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L _
  have hcount : (∑ K : Grass V t, if K.val ≤ L.val then (1 : Rat) else 0) =
      gaussian d t := by
    exact_mod_cast lowerCount (a := t) L
  calc
    (∑ K : Grass V t, if K.val ≤ L.val then f L else 0) =
        (∑ K : Grass V t, if K.val ≤ L.val then (1 : Rat) else 0) * f L := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro K _
          split_ifs <;> simp
    _ = _ := by rw [hcount]

/-- A uniform center followed by independent uniform extensions has a
uniform marginal on each ordered leaf. This concerns one occurrence i and
does not assume distinct leaves or unconditional independence of leaves. -/
theorem ordinary_leaf_average
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (i : Fin m) (f : Grass V d → Rat) :
    (∑ K : Grass V t,
      ((∑ Ls : Fin m → Extension K d, f (Ls i).1) /
        (Fintype.card (Fin m → Extension K d) : Rat)) /
          (Fintype.card (Grass V t) : Rat)) =
      (∑ L : Grass V d, f L) / (Fintype.card (Grass V d) : Rat) := by
  haveI : ∀ K : Grass V t, Nonempty (Extension K d) :=
    fun K => extension_nonempty K htd hdV
  have hinner : ∀ K : Grass V t,
      (∑ Ls : Fin m → Extension K d, f (Ls i).1) /
        (Fintype.card (Fin m → Extension K d) : Rat) =
      (∑ L : Extension K d, f L.1) /
        (gaussian (Module.finrank (ZMod 2) V - t) (d - t) : Rat) := by
    intro K
    rw [uniform_function_coordinate_average i (fun L : Extension K d => f L.1),
      extension_card K htd]
  simp_rw [hinner]
  rw [← Finset.sum_div, ← Finset.sum_div, sum_extension_sums]
  simp only [card_grass]
  have hflag : (gaussian (Module.finrank (ZMod 2) V) t : Rat) *
      gaussian (Module.finrank (ZMod 2) V - t) (d - t) =
        (gaussian (Module.finrank (ZMod 2) V) d : Rat) * gaussian d t := by
    exact_mod_cast flag_product (V := V) htd
  have hcenter : (gaussian (Module.finrank (ZMod 2) V) t : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos (htd.trans hdV))
  have hext : (gaussian (Module.finrank (ZMod 2) V - t) (d - t) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos (by omega :
      d - t ≤ Module.finrank (ZMod 2) V - t))
  have hleaf : (gaussian (Module.finrank (ZMod 2) V) d : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos hdV)
  field_simp [hcenter, hext, hleaf]
  nlinarith [congrArg (fun x : Rat => x * ∑ L : Grass V d, f L) hflag]

/-- The same nested uniform-center/independent-extension expectation used
by StarDensity, retaining the full ordered tuple and its common center. -/
def ordinaryStarAverage (f : StarTuple (V := V) t d m → Rat) : Rat :=
  ∑ K : Grass V t,
    ((∑ Ls : Fin m → Extension K d, f ⟨K, Ls⟩) /
      (Fintype.card (Fin m → Extension K d) : Rat)) /
        (Fintype.card (Grass V t) : Rat)

theorem starDensity_eq_average
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T : Labels (V := V) d) :
    StarDensity (k := m) hcenter hleaf C T =
      ordinaryStarAverage (m := m)
        (fun z => if StarAccepts C T z.1 z.2 then 1 else 0) := by
  classical
  unfold StarDensity ordinaryStarAverage
  simp only [uniformLaw_apply]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro Ls _
  ring

private theorem ordinaryStarAverage_mono
    (f g : StarTuple (V := V) t d m → Rat) (h : ∀ z, f z ≤ g z) :
    ordinaryStarAverage f ≤ ordinaryStarAverage g := by
  unfold ordinaryStarAverage
  apply Finset.sum_le_sum
  intro K _
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun Ls _ => h ⟨K, Ls⟩)

private theorem ordinaryStarAverage_add
    (f g : StarTuple (V := V) t d m → Rat) :
    ordinaryStarAverage (fun z => f z + g z) =
      ordinaryStarAverage f + ordinaryStarAverage g := by
  simp [ordinaryStarAverage, Finset.sum_add_distrib, add_div]

private theorem ordinaryStarAverage_sum
    {ι : Type*} [Fintype ι]
    (f : ι → StarTuple (V := V) t d m → Rat) :
    ordinaryStarAverage (fun z => ∑ i, f i z) =
      ∑ i, ordinaryStarAverage (f i) := by
  unfold ordinaryStarAverage
  simp_rw [Finset.sum_div]
  calc
    (∑ K : Grass V t, ∑ Ls : Fin m → Extension K d, ∑ i : ι,
        f i ⟨K, Ls⟩ / (Fintype.card (Fin m → Extension K d) : Rat) /
          (Fintype.card (Grass V t) : Rat)) =
      ∑ K : Grass V t, ∑ i : ι, ∑ Ls : Fin m → Extension K d,
        f i ⟨K, Ls⟩ / (Fintype.card (Fin m → Extension K d) : Rat) /
          (Fintype.card (Grass V t) : Rat) := by
            apply Finset.sum_congr rfl
            intro K _
            rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem ordinaryStarAverage_leaf_event
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (i : Fin m) (X : Finset (Grass V d)) :
    ordinaryStarAverage
      (fun z : StarTuple (V := V) t d m => if (z.2 i).1 ∈ X then 1 else 0) =
      (X.card : Rat) / (Fintype.card (Grass V d) : Rat) := by
  unfold ordinaryStarAverage
  rw [ordinary_leaf_average htd hdV i (fun L => if L ∈ X then 1 else 0)]
  congr 1
  simp

private theorem accepts_indicator_le_changed_occurrences
    (C : Labels (V := V) t) (T T' : Labels (V := V) d)
    (X : Finset (Grass V d))
    (houtside : ∀ L, L ∉ X → T L = T' L)
    (z : StarTuple (V := V) t d m) :
    (if StarAccepts C T z.1 z.2 then (1 : Rat) else 0) ≤
      (if StarAccepts C T' z.1 z.2 then (1 : Rat) else 0) +
        ∑ i : Fin m, if (z.2 i).1 ∈ X then (1 : Rat) else 0 := by
  classical
  have hsum : 0 ≤ ∑ i : Fin m, if (z.2 i).1 ∈ X then (1 : Rat) else 0 :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  by_cases hT : StarAccepts C T z.1 z.2
  · by_cases hT' : StarAccepts C T' z.1 z.2
    · simp only [if_pos hT, if_pos hT']
      linarith
    · have hex : ∃ i : Fin m, (z.2 i).1 ∈ X := by
        by_contra hn
        push_neg at hn
        apply hT'
        intro i x
        rw [← houtside (z.2 i).1 (hn i)]
        exact hT i x
      obtain ⟨i, hi⟩ := hex
      have hsingle : (1 : Rat) ≤
          ∑ j : Fin m, if (z.2 j).1 ∈ X then (1 : Rat) else 0 := by
        calc
          1 = (if (z.2 i).1 ∈ X then (1 : Rat) else 0) := by simp [hi]
          _ ≤ _ := Finset.single_le_sum
            (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [if_pos hT, if_neg hT', zero_add] using hsingle
  · simp only [if_neg hT]
    split_ifs <;> linarith

/-- Changing a leaf table only on X changes the actual star density by at
most m times uniform mass(X). The center table stays fixed. Repeated leaf
occurrences are retained and charged by the finite union bound. -/
theorem starDensity_change_le_leaf_mass
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T T' : Labels (V := V) d)
    (X : Finset (Grass V d))
    (houtside : ∀ L, L ∉ X → T L = T' L) :
    StarDensity (k := m) hcenter hleaf C T ≤
      StarDensity (k := m) hcenter hleaf C T' +
        (m : Rat) * ((X.card : Rat) / Fintype.card (Grass V d)) := by
  rw [starDensity_eq_average, starDensity_eq_average]
  have h := ordinaryStarAverage_mono
    (fun z : StarTuple (V := V) t d m => if StarAccepts C T z.1 z.2 then 1 else 0)
    (fun z : StarTuple (V := V) t d m =>
      (if StarAccepts C T' z.1 z.2 then 1 else 0) +
        ∑ i : Fin m, if (z.2 i).1 ∈ X then 1 else 0)
    (accepts_indicator_le_changed_occurrences C T T' X houtside)
  rw [ordinaryStarAverage_add, ordinaryStarAverage_sum] at h
  simp_rw [ordinaryStarAverage_leaf_event htd hdV] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem starDensity_abs_change_le_leaf_mass
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T T' : Labels (V := V) d)
    (X : Finset (Grass V d))
    (houtside : ∀ L, L ∉ X → T L = T' L) :
    |StarDensity (k := m) hcenter hleaf C T -
      StarDensity (k := m) hcenter hleaf C T'| ≤
        (m : Rat) * ((X.card : Rat) / Fintype.card (Grass V d)) := by
  have hforward := starDensity_change_le_leaf_mass (m := m) htd hdV hcenter hleaf C T T' X houtside
  have hreverse := starDensity_change_le_leaf_mass (m := m) htd hdV hcenter hleaf C T' T X
    (fun L hL => (houtside L hL).symm)
  apply abs_le.mpr
  constructor <;> linarith

/-- A genuine drop below half of the original density forces a large
accumulated set of changed entries under the same actual star experiment. -/
theorem density_halving_forces_changed_mass
    (htd : t ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) (hm : 0 < m)
    (hcenter : Nonempty (Grass V t))
    (hleaf : ∀ K : Grass V t, Nonempty (LeafOver K d))
    (C : Labels (V := V) t) (T T' : Labels (V := V) d)
    (X : Finset (Grass V d))
    (houtside : ∀ L, L ∉ X → T L = T' L)
    (hdrop : StarDensity (k := m) hcenter hleaf C T' <
      StarDensity (k := m) hcenter hleaf C T / 2) :
    StarDensity (k := m) hcenter hleaf C T / (2 * (m : Rat)) <
      (X.card : Rat) / Fintype.card (Grass V d) := by
  have hchange := starDensity_change_le_leaf_mass (m := m) htd hdV hcenter hleaf C T T' X houtside
  have hmRat : (0 : Rat) < m := by exact_mod_cast hm
  apply (div_lt_iff₀ (by positivity : (0 : Rat) < 2 * (m : Rat))).mpr
  nlinarith

end
end PvNP.RealizableHardness.ActualOrdinaryStarLeafMarginal
