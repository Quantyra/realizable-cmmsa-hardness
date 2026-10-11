import PvNP.RealizableHardness.NumericRefreshFormalOffer
import PvNP.RealizableHardness.ActualMaximalPairLadder

/-! Pointwise progress for the actual refreshed table and the original decoded
zoom. The preservation probability and zoom-size bounds are supplied by their
separate actual-law proofs. No stopped-history result is claimed here. -/
namespace PvNP.RealizableHardness.ActualRefreshProgress

open PvNP.RealizableHardness
open GrassmannCounting ActualMaximalPairLadder NumericRefreshFormalOffer

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat}

def zoomFinset (Q : Grass V a) (P : DecodedPair Q d) : Finset (Grass V d) :=
  Finset.univ.filter fun L => Q.val ≤ L.val ∧ L.val ≤ P.W

def zoomFinsetEquiv (Q : Grass V a) (P : DecodedPair Q d) :
    Zoom Q P ≃ ↥(zoomFinset Q P) where
  toFun z := ⟨z.1, by simpa only [zoomFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] using z.2⟩
  invFun z := ⟨z.1, by simpa only [zoomFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] using z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem zoom_card_eq_finset (Q : Grass V a) (P : DecodedPair Q d) :
    Fintype.card (Zoom Q P) = (zoomFinset Q P).card := by
  rw [Fintype.card_congr (zoomFinsetEquiv Q P), Fintype.card_coe]

theorem agreesOn_iff_target_eq
    (T : FullLabelProduct V d) (Q : Grass V a) (P : DecodedPair Q d)
    (L : Grass V d) (hLW : L.val ≤ P.W) :
    AgreesOn T (Q := Q) (P := P) L hLW ↔
      T L = targetFromMap V d P.W P.g L := by
  rw [targetFromMap_restrict V d P.W P.g L hLW]
  constructor
  · intro h
    apply LinearMap.ext
    exact h
  · intro h x
    exact congrArg (fun f : L.val →ₗ[ZMod 2] ZMod 2 => f x) h

def agreeingZoomFinsetEquiv
    (T : FullLabelProduct V d) (Q : Grass V a) (P : DecodedPair Q d) :
    AgreeingZoom T Q P ≃
      ↥((zoomFinset Q P).filter fun L => T L = targetFromMap V d P.W P.g L) where
  toFun z := ⟨z.1.1, Finset.mem_filter.mpr
    ⟨(zoomFinsetEquiv Q P z.1).2,
      (agreesOn_iff_target_eq T Q P z.1.1 z.1.2.2).mp z.2⟩⟩
  invFun z := by
    let L : Zoom Q P := (zoomFinsetEquiv Q P).symm
      ⟨z.1, (Finset.mem_filter.mp z.2).1⟩
    exact ⟨L, (agreesOn_iff_target_eq T Q P L.1 L.2.2).mpr
      (Finset.mem_filter.mp z.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem agreeingZoom_card_eq_matchCount
    (T : FullLabelProduct V d) (Q : Grass V a) (P : DecodedPair Q d) :
    Fintype.card (AgreeingZoom T Q P) =
      matchCount V d (zoomFinset Q P) (targetFromMap V d P.W P.g) T := by
  rw [Fintype.card_congr (agreeingZoomFinsetEquiv T Q P), Fintype.card_coe]
  rfl

theorem agreement_cast_eq_matchCount_ratio
    (T : FullLabelProduct V d) (Q : Grass V a) (P : DecodedPair Q d)
    (hne : Fintype.card (Zoom Q P) ≠ 0) :
    (agreement T Q P : Real) =
      (matchCount V d (zoomFinset Q P) (targetFromMap V d P.W P.g) T : Real) /
        (zoomFinset Q P).card := by
  rw [agreement_eq_fraction_of_nonempty T Q P hne,
    agreeingZoom_card_eq_matchCount, zoom_card_eq_finset]
  push_cast

/-- Refresh all of X; agreement outside X remains agreement with T itself.
The partition is on distinct Grassmann entries, without any independence
assumption about the decoded pair. -/
theorem matchCount_refresh_partition
    (X Z : Finset (Grass V d)) (G T F : FullLabelProduct V d) :
    matchCount V d Z G (refresh V d X T F) =
      matchCount V d (Z \ X) G T + matchCount V d (Z ∩ X) G F := by
  classical
  have hset : Z.filter (fun L => refresh V d X T F L = G L) =
      ((Z \ X).filter fun L => T L = G L) ∪
        ((Z ∩ X).filter fun L => F L = G L) := by
    ext L
    by_cases hx : L ∈ X <;> simp [refresh, hx]
  have hdisjoint : Disjoint
      ((Z \ X).filter fun L => T L = G L)
      ((Z ∩ X).filter fun L => F L = G L) := by
    apply Finset.disjoint_left.mpr
    intro L hL hR
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hL).1).2
      (Finset.mem_inter.mp (Finset.mem_filter.mp hR).1).2
  unfold matchCount
  rw [hset, Finset.card_union_of_disjoint hdisjoint]

theorem matchCount_mono
    (Z Z' : Finset (Grass V d)) (hZZ' : Z ⊆ Z')
    (G T : FullLabelProduct V d) :
    matchCount V d Z G T ≤ matchCount V d Z' G T := by
  apply Finset.card_le_card
  intro L hL
  exact Finset.mem_filter.mpr
    ⟨hZZ' (Finset.mem_filter.mp hL).1, (Finset.mem_filter.mp hL).2⟩

/-- The exact inverse agreement and preservation inequality force both
original-table agreement and strict growth of the actual accumulated union.
No density monotonicity or independence of the inverse output is required. -/
theorem refreshed_inverse_original_agreement_and_growth
    (X : Finset (Grass V d)) (T F : FullLabelProduct V d)
    (Q : Grass V a) (P : DecodedPair Q d) (e : Real)
    (hne : Fintype.card (Zoom Q P) ≠ 0)
    (hcurrent : e < (agreement (refresh V d X T F) Q P : Real))
    (hpreserve :
      (matchCount V d (zoomFinset Q P ∩ X) (targetFromMap V d P.W P.g) F : Real) ≤
        e / 2 * (zoomFinset Q P).card) :
    e / 2 * (zoomFinset Q P).card <
        (matchCount V d (zoomFinset Q P \ X) (targetFromMap V d P.W P.g) T : Real) ∧
      e / 2 < (agreement T Q P : Real) ∧
      (X.card : Real) + e / 2 * (zoomFinset Q P).card <
        (X ∪ zoomFinset Q P).card := by
  have hz : 0 < ((zoomFinset Q P).card : Real) := by
    have hn : (zoomFinset Q P).card ≠ 0 := by
      rwa [zoom_card_eq_finset] at hne
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [agreement_cast_eq_matchCount_ratio _ Q P hne] at hcurrent
  have hcurrent' := (lt_div_iff₀ hz).mp hcurrent
  have hsplit :
      (matchCount V d (zoomFinset Q P) (targetFromMap V d P.W P.g)
        (refresh V d X T F) : Real) =
      (matchCount V d (zoomFinset Q P \ X) (targetFromMap V d P.W P.g) T : Real) +
        (matchCount V d (zoomFinset Q P ∩ X) (targetFromMap V d P.W P.g) F : Real) := by
    exact_mod_cast matchCount_refresh_partition X (zoomFinset Q P)
      (targetFromMap V d P.W P.g) T F
  have hout : e / 2 * (zoomFinset Q P).card <
      (matchCount V d (zoomFinset Q P \ X) (targetFromMap V d P.W P.g) T : Real) := by
    linarith
  refine ⟨hout, ?_, ?_⟩
  · rw [agreement_cast_eq_matchCount_ratio T Q P hne]
    apply (lt_div_iff₀ hz).mpr
    have hmono :
        (matchCount V d (zoomFinset Q P \ X) (targetFromMap V d P.W P.g) T : Real) ≤
          (matchCount V d (zoomFinset Q P) (targetFromMap V d P.W P.g) T : Real) := by
      exact_mod_cast matchCount_mono (zoomFinset Q P \ X) (zoomFinset Q P)
        Finset.sdiff_subset (targetFromMap V d P.W P.g) T
    exact hout.trans_le hmono
  · have hcount :
        (matchCount V d (zoomFinset Q P \ X) (targetFromMap V d P.W P.g) T : Real) ≤
          ((zoomFinset Q P \ X).card : Real) := by
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset (fun L => T L = targetFromMap V d P.W P.g L)
          (zoomFinset Q P \ X))
    have hunionNat : (zoomFinset Q P \ X).card + X.card =
        (X ∪ zoomFinset Q P).card := by
      simpa only [Finset.union_comm] using
        Finset.card_sdiff_add_card (zoomFinset Q P) X
    have hunion : ((zoomFinset Q P \ X).card : Real) + X.card =
        (X ∪ zoomFinset Q P).card := by exact_mod_cast hunionNat
    linarith

end
end PvNP.RealizableHardness.ActualRefreshProgress
