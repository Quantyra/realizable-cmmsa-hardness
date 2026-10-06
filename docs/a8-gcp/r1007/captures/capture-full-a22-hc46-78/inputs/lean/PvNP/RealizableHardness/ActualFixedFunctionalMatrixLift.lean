import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary
import PvNP.RealizableHardness.MatrixLiftNominalDirectComparison

/-! The fixed-functional matrix step inside the ordinary all-ambient inverse. -/
namespace PvNP.RealizableHardness.ActualFixedFunctionalMatrixLift

open scoped BigOperators
open GrassmannCounting ActualMaximalPairLadder
open ActualChangedAmbient8SBoundary MatrixLiftExactBudgetZoom
open MatrixLiftNominalDirectComparison
open BinaryMatrixFourier
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Ambient (n : Nat) := Fin n → ZMod 2
instance ambientFintype (n : Nat) : Fintype (Ambient n) := inferInstance

def matchingLeafSet {n d : Nat} (T : Labels (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n))
    (L : Grass (Ambient n) d) : Bool :=
  decide (∀ x : L.val, T L x = f x.val)

private def pairOfGlobal {n q d w : Nat}
    (Q : Grass (Ambient n) q) (W : Grass (Ambient n) w)
    (hQW : Q.val ≤ W.val)
    (f : Module.Dual (ZMod 2) (Ambient n)) : DecodedPair Q d :=
  ⟨W.val, hQW, f.comp W.val.subtype⟩

private theorem sum_matching_eq_card_agreeing {n q d w : Nat}
    (T : Labels (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n))
    (Q : Grass (Ambient n) q) (W : Grass (Ambient n) w)
    (hQW : Q.val ≤ W.val) :
    (∑ L : Between Q.val W.val d, grassIndicator (matchingLeafSet T f) L.val) =
      (Nat.card (AgreeingZoom T Q (pairOfGlobal Q W hQW f)) : ℝ) := by
  classical
  let P := pairOfGlobal (d := d) Q W hQW f
  letI := agreeingZoomFintype T Q P
  have hmatch (L : Between Q.val W.val d) :
      (matchingLeafSet T f L.val = true) ↔
        AgreesOn T (P := P) L.val L.property.2 := by
    simp only [matchingLeafSet, decide_eq_true_eq]
    change (∀ x : L.val.val, T L.val x = f x.val) ↔
      (∀ x : L.val.val, T L.val x = f x.val)
    rfl
  simp only [grassIndicator]
  simp_rw [hmatch]
  have he : {L : Between Q.val W.val d // AgreesOn T (P := P) L.val L.property.2} ≃
      AgreeingZoom T Q P := Equiv.refl _
  have hc := Fintype.card_congr he
  simpa [Finset.sum_boole, Fintype.card_subtype, Nat.card_eq_fintype_card] using
    congrArg (fun x : Nat => (x : ℝ)) hc

theorem failed_zoom_gives_exact_bound {n d r : Nat}
    (T : Labels (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n))
    (e : ℚ)
    (hfail : ∀ (q : Nat) (Q : Grass (Ambient n) q)
      (P : DecodedPair Q d),
      q + codim P.W = r → Fintype.card (Zoom Q P) ≠ 0 →
        agreement T Q P ≤ e) :
    ExactBudgetZoomBound r d
      (grassIndicator (matchingLeafSet T f)) (e : ℝ) := by
  intro q w Q W hbudget hnonempty
  by_cases hQW : Q.val ≤ W.val
  · let P : DecodedPair Q d := pairOfGlobal Q W hQW f
    letI := agreeingZoomFintype T Q P
    have hpbudget : q + codim P.W = r := by
      change q + (Module.finrank (ZMod 2) (Ambient n) -
        Module.finrank (ZMod 2) W.val) = r
      rw [W.property]
      exact hbudget
    have hcard : Fintype.card (Zoom Q P) =
        Fintype.card (Between Q.val W.val d) := by
      exact Fintype.card_congr (Equiv.refl _)
    have hpos : Fintype.card (Zoom Q P) ≠ 0 := by
      have : Nonempty (Zoom Q P) := by
        change Nonempty (Between Q.val W.val d)
        exact hnonempty
      exact Fintype.card_ne_zero
    have hbound := hfail q Q P hpbudget hpos
    rw [agreement_eq_fraction_of_nonempty T Q P hpos] at hbound
    have hboundR : (Fintype.card (AgreeingZoom T Q P) : ℝ) ≤
        (e : ℝ) * (Fintype.card (Zoom Q P) : ℝ) := by
      have hcpos : (0 : ℚ) < Fintype.card (Zoom Q P) := by
        exact_mod_cast Nat.pos_of_ne_zero hpos
      have hmul := (div_le_iff₀ hcpos).mp hbound
      exact_mod_cast hmul
    rw [sum_matching_eq_card_agreeing T f Q W hQW,
      Nat.card_eq_fintype_card, ← hcard]
    exact hboundR
  · exfalso
    obtain ⟨L⟩ := hnonempty
    exact hQW (le_trans L.property.1 L.property.2)

theorem failed_zoom_gives_nominal_pseudorandom {n d r : Nat}
    (hrd : r < d)
    (T : Labels (V := Ambient n) d)
    (f : Module.Dual (ZMod 2) (Ambient n))
    (e : ℚ) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : Grass (Ambient n) q)
      (P : DecodedPair Q d),
      q + codim P.W = r → Fintype.card (Zoom Q P) ≠ 0 →
        agreement T Q P ≤ e) :
    PseudorandomExact r (2 * (e : ℝ))
      (rankImageBoolean (matchingLeafSet T f)) := by
  apply exact_zoom_implies_nominal_pseudorandom hrd (matchingLeafSet T f)
    (e : ℝ) (by exact_mod_cast he)
  exact failed_zoom_gives_exact_bound T f e hfail

end
end PvNP.RealizableHardness.ActualFixedFunctionalMatrixLift
