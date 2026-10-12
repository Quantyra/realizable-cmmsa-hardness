import PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
import PvNP.RealizableHardness.MatrixGrassmannIdentity

/-! The actual ordinary-star matching event, tested by one fixed functional,
written as the same center-and-ordered-extension indicator used by the
Grassmann experiment. -/
namespace PvNP.RealizableHardness.ActualFixedFunctionalStarMoment

open scoped BigOperators
open PvNP.RealizableHardness
open GrassmannCounting
open ActualFiniteLaw
open ActualSourceStarLaw
open ActualOrdinaryStarMatchingFiber
open ActualOrdinaryStarWeightedSelection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

def centerMatchBit {t : Nat} (C : CenterTable (V := V) t)
    (f : Module.Dual (ZMod 2) V) (K : Grass V t) : Bool :=
  decide (f.comp K.val.subtype = C K)

def leafMatchBit {d : Nat} (T : LeafTable (V := V) d)
    (f : Module.Dual (ZMod 2) V) (L : Grass V d) : Bool :=
  decide (f.comp L.val.subtype = T L)

theorem matchesStar_iff_bits {t d k : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d k) (f : Module.Dual (ZMod 2) V) :
    MatchesStar C T z f ↔
      centerMatchBit C f z.1 = true ∧
        ∀ i : Fin k, leafMatchBit T f (z.2 i).val = true := by
  simp [MatchesStar, centerMatchBit, leafMatchBit]

/-- The exact per-star integrand in `grassmannExperiment` is the indicator of
the existing `MatchesStar` event, including the center condition at k=0. -/
theorem grassmann_integrand_eq_matchesStar_indicator {t d k : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d k) (f : Module.Dual (ZMod 2) V) :
    ((if centerMatchBit C f z.1 then (1 : Real) else 0) *
      (∏ i : Fin k, if leafMatchBit T f (z.2 i).val then (1 : Real) else 0)) =
        (if MatchesStar C T z f then 1 else 0) := by
  have hprod :
      (∏ i : Fin k, if leafMatchBit T f (z.2 i).val = true then (1 : Real) else 0) =
        (if ∀ i : Fin k, leafMatchBit T f (z.2 i).val = true then 1 else 0) :=
    by
      classical
      by_cases hall : ∀ i : Fin k, leafMatchBit T f (z.2 i).val = true
      · simp [hall]
      · rw [if_neg hall]
        obtain ⟨i, hi⟩ := not_forall.mp hall
        have hfalse : leafMatchBit T f (z.2 i).val = false := by
          cases hb : leafMatchBit T f (z.2 i).val <;> simp_all
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hfalse]
  rw [hprod]
  have hbits := matchesStar_iff_bits C T z f
  by_cases hc : centerMatchBit C f z.1 = true <;>
    by_cases hl : ∀ i : Fin k, leafMatchBit T f (z.2 i).val = true <;>
    simp [hc, hl, hbits]

/-- The weighted matching mass from the actual common-center star law is
exactly the same fixed-functional event in the independent extension
experiment. Parameters are indexed as base dimension c and appended width s,
so both laws use the identical leaf carrier `Above R s = Extension R (c+s)`. -/
theorem matchingStarMass_cast_eq_grassmannExperiment {c s k : Nat}
    (hdV : c + s ≤ Module.finrank (ZMod 2) V)
    (C : CenterTable (V := V) c)
    (T : LeafTable (V := V) (c + s))
    (f : Module.Dual (ZMod 2) V) :
    (matchingStarMass (m := k) (Nat.le_add_right c s) hdV C T f : Real) =
      MatrixGrassmannIdentity.grassmannExperiment
        (fun R : Grass V c => centerMatchBit C f R)
        (fun W : Grass V (c + s) => leafMatchBit T f W) k := by
  classical
  let mu := starLaw (V := V) (t := c) (d := c + s) (m := k)
    (Nat.le_add_right c s) hdV
  have hmass (R : Grass V c) (Ls : Fin k → Extension R (c + s)) :
      mu.mass ⟨R, Ls⟩ =
        (centerLaw R).mass R * ∏ i : Fin k,
          (extensionLaw R (Ls i)).mass (Ls i) := by
    exact starLaw_atom (V := V) (t := c) (d := c + s) (m := k)
      (Nat.le_add_right c s) hdV R Ls
  have hmassCast (R : Grass V c) (Ls : Fin k → Extension R (c + s)) :
      (mu.mass ⟨R, Ls⟩ : Real) =
      ((1 : Real) / Fintype.card (Grass V c)) *
          ∏ i : Fin k, (1 : Real) / Fintype.card (Extension R (c + s)) := by
    have hr := hmass R Ls
    rw [centerLaw_apply R R] at hr
    simp_rw [extensionLaw_apply R] at hr
    have hrCast := congrArg (fun x : Rat => (x : Real)) hr
    simpa only [Rat.cast_mul, Rat.cast_prod, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast]
      using hrCast
  have hnorm (R : Grass V c) :
      (∏ i : Fin k, (1 : Real) / Fintype.card (Extension R (c + s))) =
        (1 : Real) / Fintype.card (Fin k → Extension R (c + s)) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div_pow]
  have hpercenter (R : Grass V c) :
      (∑ Ls : Fin k → Extension R (c + s),
        (if centerMatchBit C f R then (1 : Real) else 0) *
          (∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) *
            ((1 : Real) / Fintype.card (Grass V c)) *
              ((1 : Real) / Fintype.card (Fin k → Extension R (c + s)))) =
        (if centerMatchBit C f R then (1 : Real) else 0) *
          ((∑ Ls : Fin k → Extension R (c + s),
              ∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) /
            Fintype.card (Fin k → Extension R (c + s))) /
            Fintype.card (Grass V c) := by
    by_cases hc : centerMatchBit C f R = true
    · simp only [if_pos hc, one_mul]
      calc
        (∑ Ls : Fin k → Extension R (c + s),
            (∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) *
              ((1 : Real) / Fintype.card (Grass V c)) *
                ((1 : Real) / Fintype.card (Fin k → Extension R (c + s)))) =
            ∑ Ls : Fin k → Extension R (c + s),
              (∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) *
                (((1 : Real) / Fintype.card (Grass V c)) *
                  ((1 : Real) / Fintype.card (Fin k → Extension R (c + s)))) := by
          apply Finset.sum_congr rfl
          intro Ls _
          ring
        _ = (∑ Ls : Fin k → Extension R (c + s),
              ∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) *
                (((1 : Real) / Fintype.card (Grass V c)) *
                  ((1 : Real) / Fintype.card (Fin k → Extension R (c + s)))) := by
          rw [Finset.sum_mul]
        _ = (∑ Ls : Fin k → Extension R (c + s),
              ∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) /
              Fintype.card (Fin k → Extension R (c + s)) /
              Fintype.card (Grass V c) := by ring
    · simp [hc]
  have hterm (R : Grass V c) (Ls : Fin k → Extension R (c + s)) :
      (if MatchesStar C T ⟨R, Ls⟩ f then
          ((1 : Real) / Fintype.card (Grass V c)) *
            ((1 : Real) / Fintype.card (Fin k → Extension R (c + s))) else 0) =
        (if centerMatchBit C f R then (1 : Real) else 0) *
          (∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) *
            ((1 : Real) / Fintype.card (Grass V c)) *
              ((1 : Real) / Fintype.card (Fin k → Extension R (c + s))) := by
    have hi := grassmann_integrand_eq_matchesStar_indicator C T ⟨R, Ls⟩ f
    by_cases hm : MatchesStar C T ⟨R, Ls⟩ f
    · simp [hm, hi]
    · simp [hm, hi]
  change (matchingStarMass (m := k) (Nat.le_add_right c s) hdV C T f : Real) = _
  rw [show matchingStarMass (m := k) (Nat.le_add_right c s) hdV C T f =
      eventMass mu (Finset.univ.filter fun z : StarTuple (V := V) c (c+s) k =>
        MatchesStar C T z f) by rfl]
  unfold eventMass
  push_cast
  rw [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  simp_rw [hmassCast]
  simp_rw [hnorm]
  simp_rw [hterm]
  unfold MatrixGrassmannIdentity.grassmannExperiment
  calc
    (∑ R : Grass V c, ∑ Ls : Fin k → Extension R (c + s),
        (if centerMatchBit C f R then (1 : Real) else 0) *
          (∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) *
            ((1 : Real) / Fintype.card (Grass V c)) *
              ((1 : Real) / Fintype.card (Fin k → Extension R (c + s)))) =
      (∑ R : Grass V c,
        (if centerMatchBit C f R then (1 : Real) else 0) *
          ((∑ Ls : Fin k → Extension R (c + s),
              ∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) /
              Fintype.card (Fin k → Extension R (c + s))) /
            Fintype.card (Grass V c)) := by
        apply Finset.sum_congr rfl
        intro R _
        exact hpercenter R
    _ = (∑ R : Grass V c,
        (if centerMatchBit C f R then (1 : Real) else 0) *
          ((∑ Ls : Fin k → Extension R (c + s),
              ∏ i : Fin k, if leafMatchBit T f (Ls i).val then (1 : Real) else 0) /
            Fintype.card (Fin k → Extension R (c + s)))) /
            Fintype.card (Grass V c) := by rw [Finset.sum_div]
    _ = MatrixGrassmannIdentity.grassmannExperiment
        (fun R : Grass V c => centerMatchBit C f R)
        (fun W : Grass V (c + s) => leafMatchBit T f W) k := rfl

end
end PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
