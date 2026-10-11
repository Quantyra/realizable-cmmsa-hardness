import PvNP.RealizableHardness.ActualHSideFullZoom
import PvNP.RealizableHardness.ActualNumericRobustReal

/-! The actual H-side window pays its leaf charge at the same selected floor. -/
namespace PvNP.RealizableHardness.ActualSelectedHSideAgreement

open PvNP.RealizableHardness
open ActualHSideFullZoom ActualNumericSideExtension ActualMaximalPairLadder
open ActualTaggedComplementIncidence ActualTaggedMZSideDraw
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedOrderedSampleNonempty ActualTaggedPresentedSelection
open ActualStarSpanIntersection ActualNumericRobustReal ActualNumericRobustCutoffs
open ActualNumericExplicitHeight ActualNumericSourceHeight
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
private abbrev E {J : Nat} (U : TaggedGoodU I copies J) :=
  coordinateSpace (taggedSource I copies).support U.1
private abbrev H {J : Nat} (U : TaggedGoodU I copies J) :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

/-- The actual H-window witness retains agreement above e/3 after removing
leaf conditioning. All dimensional guards come from the same numeric selector. -/
theorem selected_actual_hside_full_agreement
    {L m samplerA a c : Nat}
    (base : Nat → Nat) (cutoff : Real → Nat) (hA : 1 ≤ samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) (g : Module.Dual (ZMod 2) W')
    (K : SideCenter I copies U a)
    (hKW : K.1.val ≤ sideWindow I copies U A W')
    (ha : a ≤ numericRankThreshold m) (hc : c ≤ numericRankThreshold m)
    (hcodim : Module.finrank (ZMod 2) A.1 = c + Module.finrank (ZMod 2) W')
    (T : TaggedRawVertexTable I copies (blocks samplerA (hBlock L m)) (hBlock L m))
    (s : TaggedRepresentativeChoice I copies (blocks samplerA (hBlock L m)) (hBlock L m))
    [Nonempty (SideLeaf I copies U (hBlock L m) K)]
    (hag : refreshThreshold m (hBlock L m) / 2 <
      (originalSideRestrictionRatio I copies U A W' g K T s : Real)) :
    refreshThreshold m (hBlock L m) / 3 <
      (agreement (totalHLeafTable I copies U T s) K.1
        (sideDecodedPair (h := hBlock L m) I copies U A W' g K hKW) : Real) := by
  let h := hBlock L m
  let J := blocks samplerA h
  let r := numericRankThreshold m
  let w := Module.finrank (ZMod 2) (sideWindow I copies U A W')
  have guards := selected_robust_dimension_guards base cutoff hA hsel
  change RobustDimensionGuards m h samplerA at guards
  rcases guards with ⟨_hbsq, h8r, _h16, _hquad, hdim, _hlarge, _hcoef⟩
  have hbudget : w + c = 3 * J :=
    sideWindow_finrank_budget I copies U A K W' hcodim
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    exact taggedEquationInCoordinate_finrank I copies
      (questionOf I copies U (sideToCenter I copies U K))
  have ha' : a ≤ r := ha
  have hc' : c ≤ r := hc
  have hdim' : 8 * h + 4 * r + 16 ≤ 2 * J := hdim
  have h8r' : 8 * (r + 1) ≤ h := h8r
  have had : a ≤ 2 * h := by omega
  have hd : 2 * h ≤ w := by omega
  have hbd : 1 ≤ 2 * h - a := by omega
  have hslack : Module.finrank (ZMod 2) (H I copies U) + (2 * h - a) + 1 ≤
      w - a := by rw [hHdim]; omega
  let exponent := w - a - Module.finrank (ZMod 2) (H I copies U) - (2 * h - a) - 1
  have hexp : 2 * h + 1 ≤ exponent := by
    dsimp [exponent]
    rw [hHdim]
    omega
  have hpow : (2 : Real) ^ (2 * h + 1) ≤ (2 : Real) ^ exponent :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hrecip : 1 / (2 : Real) ^ exponent ≤ 1 / (2 : Real) ^ (2 * h + 1) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hheight := selected_numeric_height (numericBase base) cutoff
    (by simpa only [numericSourceBase_eq, numericSourceFloor] using hsel)
  rcases hheight with ⟨hm, _, hbase, _, _⟩
  have hnum : numericHnum m ≤ h :=
    (Nat.le_max_right (base m) (numericHnum m)).trans hbase
  have hthreshold := (refresh_threshold_bounds hm hnum).2
  have hhalf : 1 / (2 : Real) ^ (2 * h + 1) =
      (2 / (2 : Real) ^ (2 * h)) / 4 := by
    rw [pow_succ, div_mul_eq_div_div]
    ring
  have hcharge : 1 / (2 : Real) ^ exponent ≤ refreshThreshold m h / 8 := by
    rw [hhalf] at hrecip
    linarith
  have hfull := full_agreement_ge_original_side_sub_dyadic I copies U A W' g K hKW T s
    had hd hbd hslack
  have hfullR :
      (originalSideRestrictionRatio I copies U A W' g K T s : Real) -
        1 / (2 : Real) ^ exponent ≤
      (agreement (totalHLeafTable I copies U T s) K.1
        (sideDecodedPair (h := h) I copies U A W' g K hKW) : Real) := by
    exact_mod_cast hfull
  have he : 0 < refreshThreshold m h := by
    unfold refreshThreshold
    positivity
  change refreshThreshold m h / 3 < _
  linarith

end
end PvNP.RealizableHardness.ActualSelectedHSideAgreement
