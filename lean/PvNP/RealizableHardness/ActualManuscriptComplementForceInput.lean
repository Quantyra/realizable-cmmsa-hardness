import PvNP.RealizableHardness.ActualManuscriptComplementMargin
import PvNP.RealizableHardness.ActualTaggedComplementInverseInput
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector

/-! The exact manuscript margin discharges the threshold hypothesis of the
actual fixed-U complement consumer. The density threshold q remains an
independent rational input; only the manuscript's lower bound `4S ≤ q` is
used to derive the selector's success-margin comparison. -/

namespace PvNP.RealizableHardness.ActualManuscriptComplementForceInput

open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.ActualManuscriptComplementMargin
open PvNP.RealizableHardness.ActualTaggedComplementInverseInput
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualTaggedComplementHighDensityInput
open PvNP.RealizableHardness.ActualTaggedComplementIncidence
open PvNP.RealizableHardness.ActualTaggedMZSideDraw

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
variable (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J)

/-- The full actual conclusion shared by the arbitrary-q, admissible, and
selector-specialized manuscript callers below. -/
def actualManuscriptQOutput
    {t h k : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) : Prop :=
    q / 2 ≤ goodComplementMass (k := k) I copies U ht hh C T' q ∧
      ∀ A : SideComplement I copies U,
        q / 2 ≤ complementStarDensity (k := k) I copies U A ht hh C T' →
        ∃ f : Module.Dual (ZMod 2) A.1,
          let Cₐ := transportedCenterTable I copies U A C
          let Tₐ := transportedLeafTable I copies U A T'
          let X := matchingStarMass (m := k) ht
            (by
              calc
                2 * h ≤ 2 * J := by omega
                _ = Module.finrank (ZMod 2) A.1 :=
                  (sideComplement_finrank I copies U A).symm) Cₐ Tₐ f
          let β := matchingCenterMass (m := k) ht
            (by
              calc
                2 * h ≤ 2 * J := by omega
                _ = Module.finrank (ZMod 2) A.1 :=
                  (sideComplement_finrank I copies U A).symm) Cₐ f
          let M : Rat :=
            2 ^ (Module.finrank (ZMod 2) A.1 - (t + k * (2 * h - t)))
          let B : Rat := 2 ^ (Module.finrank (ZMod 2) A.1 - t)
          let F : Rat := 2 ^ Module.finrank (ZMod 2) A.1
          (q / 8) * (1 / (2 : Rat) ^ (k * (2 * h - t))) * β +
            (q / 8) * (1 / (2 : Rat) ^ (t + k * (2 * h - t))) ≤ X ∧ X ≤ β

/-- With rho fixed to the manuscript reciprocal and h divisible by bOf m,
any arbitrary rational q at least 4S can be fed into the actual fixed-U
complement density/weighted-functional theorem. The result retains its q/2
good-complement mass and q/8 reciprocal-weight conclusion. -/
theorem actual_manuscript_q_complement_input
    {t h k : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hk : 1 ≤ 2 * h - t)
    (hguard : k * (2 * h - t) + badExponent m h + 2 ≤ 2 * J - t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) (hqpos : 0 < q)
    (hq : q ≤ sideConditionalDensity I copies U t h k C T')
    (hdiv : bOf m ∣ h) (hm : 0 < m)
    (hscale : 4 * manuscriptSuccessScale (manuscriptRho m) m h ≤ (q : ℝ)) :
    actualManuscriptQOutput I copies U ht hh C T' q := by
  have hmarginReal :
      (successMargin (badExponent m h) : ℝ) ≤ (q : ℝ) / 2 :=
    margin_le_half_of_four_scale_le hm hdiv hscale
  have hmargin : successMargin (badExponent m h) ≤ q / 2 := by
    exact_mod_cast hmarginReal
  exact actual_density_positive_mass_with_q_functionals
    (I := I) (copies := copies) (U := U) ht hh hk hguard C T'
    q hqpos hq hmargin

/-- Admissibility supplies the genuine reciprocal-divisibility condition and
positive m required by the arithmetic bridge; they are not caller-supplied
surrogates. The dimension and density hypotheses remain explicit inputs. -/
theorem admissible_manuscript_q_complement_input
    {sourceHMin : Nat → Nat} {L : Nat}
    (hAd : Admissible sourceHMin L m)
    {t k : Nat} (ht : t ≤ 2 * hBlock L m) (hh : hBlock L m ≤ J)
    (hk : 1 ≤ 2 * hBlock L m - t)
    (hguard : k * (2 * hBlock L m - t) + badExponent m (hBlock L m) + 2 ≤
      2 * J - t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (q : Rat) (hqpos : 0 < q)
    (hq : q ≤ sideConditionalDensity I copies U t (hBlock L m) k C T')
    (hscale : 4 * manuscriptSuccessScale (manuscriptRho m) m (hBlock L m) ≤
      (q : ℝ)) :
    actualManuscriptQOutput I copies U ht hh C T' q := by
  have hm : 0 < m := by omega
  exact actual_manuscript_q_complement_input
    (I := I) (copies := copies) (U := U)
    (ht := ht) (hh := hh) (hk := hk) (hguard := hguard)
    (C := C) (T' := T') (q := q) (hqpos := hqpos) (hq := hq)
    (hdiv := hAd.2.2.2.2.2.1) hm hscale

end
end PvNP.RealizableHardness.ActualManuscriptComplementForceInput
