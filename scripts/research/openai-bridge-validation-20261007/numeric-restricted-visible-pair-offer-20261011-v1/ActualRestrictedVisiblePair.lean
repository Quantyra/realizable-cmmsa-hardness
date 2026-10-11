import PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss
import PvNP.RealizableHardness.TripleRestrictionDimension

/-! Restrict the original decoded pair to the actual retained space, keeping
its label. Derive the window dimension and instantiate the visible-table loss. -/
namespace PvNP.RealizableHardness.ActualRestrictedVisiblePair

open ActualOccurrenceAllocation ActualStarSpanIntersection ActualTaggedConcreteStarLaw
open ActualTaggedFixedCenterGeometry ActualTaggedRowDeletion ActualVisibleQuestionCompletion
open ActualTaggedPresentedSelection ActualTaggedSelectedDecoderBridge ActualHSideFullZoom
open ActualVisibleLeafAgreementLoss ActualMaximalPairLadder GrassmannCounting
open TripleRestrictionRank TripleRestrictionDimension

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1

/-- The first prover's original label restricted to W intersect actual V. -/
def restrictedPair {a d : Nat} (Q : Grass (E I copies U) a)
    (P : DecodedPair Q d) (s : ActualRowDraw I copies U)
    (hQV : Q.val ≤ actualRetained I copies U s) : DecodedPair Q d where
  W := P.W ⊓ actualRetained I copies U s
  hQW := le_inf P.hQW hQV
  g := P.g.comp (Submodule.inclusion inf_le_left)

/-- This pair keeps exactly the original functional values on the intersection. -/
theorem restrictedPair_apply {a d : Nat} (Q : Grass (E I copies U) a)
    (P : DecodedPair Q d) (s : ActualRowDraw I copies U)
    (hQV : Q.val ≤ actualRetained I copies U s)
    (x : (restrictedPair I copies U Q P s hQV).W) :
    (restrictedPair I copies U Q P s hQV).g x = P.g ⟨x.1, x.2.1⟩ := rfl

/-- The row-coordinate identity gives the exact actual retained dimension. -/
theorem actualRetained_finrank (s : ActualRowDraw I copies U) :
    Module.finrank (ZMod 2) (actualRetained I copies U s) =
      3 * J - 2 * dropCount (rowDrawEquiv I copies U s) := by
  have hmap := (actualRowCoordinateEquiv I copies U).finrank_map_eq
    (actualRetained I copies U s)
  rw [actualRetained_map_coordinates I copies U s] at hmap
  rw [← hmap]
  exact retained_finrank_eq (rowDrawEquiv I copies U s)

/-- Restriction can lose at most the original codimension. Rank stability
is not needed for this dimension lower bound. -/
theorem restrictedPair_finrank_lower {a d r T : Nat}
    (Q : Grass (E I copies U) a) (P : DecodedPair Q d)
    (s : ActualRowDraw I copies U)
    (hQV : Q.val ≤ actualRetained I copies U s)
    (hc : codim P.W ≤ r) (hdrop : dropCount (rowDrawEquiv I copies U s) ≤ T) :
    3 * J - 2 * T - r ≤
      Module.finrank (ZMod 2) (restrictedPair I copies U Q P s hQV).W := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P.W (actualRetained I copies U s)
  have hsup := (P.W ⊔ actualRetained I copies U s).finrank_le
  have hW := P.W.finrank_le
  have hV := actualRetained_finrank I copies U s
  unfold codim at hc
  change 3 * J - 2 * T - r ≤
    Module.finrank (ZMod 2) (P.W ⊓ actualRetained I copies U s)
  omega

/-- A single actual draw with bounded deletion count has the displayed
two-table error for the restricted original pair. No favorable draw is assumed
to exist, and the subsequent posterior calculation must pay for the guards. -/
theorem actual_restricted_visible_agreement_lower {a h r Tcut : Nat}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (Q : Grass (E I copies U) a) (P : DecodedPair Q (2 * h))
    (s : ActualRowDraw I copies U)
    (hQV : Q.val ≤ actualRetained I copies U s)
    (hc : codim P.W ≤ r)
    (hdrop : dropCount (rowDrawEquiv I copies U s) ≤ Tcut)
    (hQH : Q.val ⊓ originalSideSpace I copies U = ⊥)
    (hQ0 : Q.val ⊓ visibleSideSpace I copies U
      (retainedVariables I copies J U s) (retainedVariables_reachable I copies J U s) = ⊥)
    (had : a ≤ 2 * h) (hbd : 1 ≤ 2 * h - a)
    (hslack : J + 2 * h + 1 ≤ 3 * J - 2 * Tcut - r) :
    agreement (totalHLeafTable I copies U Traw choice) Q
        (restrictedPair I copies U Q P s hQV) -
      2 / (2 : Rat) ^ (2 * J - 2 * Tcut - 2 * h - r - 1) ≤
        agreement (visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s)) Q
            (restrictedPair I copies U Q P s hQV) := by
  let P' := restrictedPair I copies U Q P s hQV
  have hdim : 3 * J - 2 * Tcut - r ≤ Module.finrank (ZMod 2) P'.W :=
    restrictedPair_finrank_lower I copies U Q P s hQV hc hdrop
  have hd : 2 * h ≤ Module.finrank (ZMod 2) P'.W := by omega
  have hguard : J + (2 * h - a) + 1 ≤ Module.finrank (ZMod 2) P'.W - a := by omega
  have he : 2 * J - 2 * Tcut - 2 * h - r - 1 ≤
      Module.finrank (ZMod 2) P'.W - J - 2 * h - 1 := by omega
  have hp : (2 : Rat) ^ (2 * J - 2 * Tcut - 2 * h - r - 1) ≤
      (2 : Rat) ^ (Module.finrank (ZMod 2) P'.W - J - 2 * h - 1) :=
    pow_le_pow_right₀ (by norm_num) he
  have hrecip := one_div_le_one_div_of_le
    (show (0 : Rat) < (2 : Rat) ^ (2 * J - 2 * Tcut - 2 * h - r - 1) by positivity) hp
  have hcost : 2 / (2 : Rat) ^ (Module.finrank (ZMod 2) P'.W - J - 2 * h - 1) ≤
      2 / (2 : Rat) ^ (2 * J - 2 * Tcut - 2 * h - r - 1) := by
    have hh := mul_le_mul_of_nonneg_left hrecip (show (0 : Rat) ≤ 2 by norm_num)
    simpa only [div_eq_mul_inv, one_mul] using hh
  have hle := actual_draw_visible_agreement_ge_original_sub_dyadic
    I copies U Traw choice s Q P' inf_le_right hQH hQ0 had hd hbd hguard
  linarith

end
end PvNP.RealizableHardness.ActualRestrictedVisiblePair
