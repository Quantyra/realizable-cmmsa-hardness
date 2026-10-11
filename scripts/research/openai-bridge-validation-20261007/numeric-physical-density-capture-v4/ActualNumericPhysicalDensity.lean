import Mathlib.Tactic
import PvNP.RealizableHardness.ActualOccurrenceAllocation
import PvNP.RealizableHardness.ActualNumericSourceHeight
import PvNP.RealizableHardness.ActualNumericExplicitHeight
import PvNP.RealizableHardness.ActualTaggedFixedUDensityForce
import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
import PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
import PvNP.RealizableHardness.ActualTaggedPresentedSelection
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
import PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound
import PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
import PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
import PvNP.RealizableHardness.ActualQuestionMassBridge
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import PvNP.RealizableHardness.SamplerParameters

/-! Same-selector physical-density consequence with the selected star count
separate from the source occurrence-row count. The high physical-mass input
is still conditional on the same fixed source instance and fixed tables. -/
namespace PvNP.RealizableHardness.ActualNumericPhysicalDensity

open scoped BigOperators
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualNumericSourceHeight
open PvNP.RealizableHardness.ActualNumericExplicitHeight
open PvNP.RealizableHardness.ActualQuestionMassBridge
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualTaggedFixedUDensityForce
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedOrderedClassCollisionBound
open PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
open PvNP.RealizableHardness.ActualTaggedOrderedSampleNonempty
open PvNP.RealizableHardness.SamplerParameters

set_option autoImplicit false
noncomputable section

/-- The repetition exponent in the physical-score threshold at the selected
fixed-rho quotient. -/
def physicalScoreExponent (m h : Nat) : Nat :=
  2 * m * (h - 4000 * (h / bOf m))

private theorem nat_le_two_pow (n : Nat) : n <= 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      cases n with
      | zero => norm_num
      | succ n =>
          have hn : 1 <= 2 ^ (n + 1) := by positivity
          nlinarith

private theorem selected_explicit_parameters
    (base : Nat -> Nat) (cutoff : Real -> Nat) {L m : Nat}
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat)) :
    256 <= m /\ numericHnum m <= hBlock L m /\ bOf m | hBlock L m := by
  have hselSource : selector (fun j =>
      max (analyticSourceHeightFloor
        (numericSourceBase (numericBase base)) cutoff j) (j + 2)) L =
        (m : WithBot Nat) := by
    simpa [numericSourceFloor, numericSourceBase_eq] using hsel
  rcases selected_numeric_height (numericBase base) cutoff hselSource with
    ⟨hm, _, hbase, _, hdiv⟩
  have hbase' : numericBase base m <= hBlock L m := by
    simpa [numericSourceBase_eq] using hbase
  have hnum : numericHnum m <= hBlock L m :=
    (Nat.le_max_right (base m) (numericHnum m)).trans hbase'
  exact ⟨hm, hnum, hdiv⟩

/-- The numeric selector floor supplies every geometric and exponent guard
needed by the fixed-table physical-to-canonical density theorem. -/
private theorem numeric_selected_guards {m h A : Nat}
    (hm : 256 <= m)
    (hnum : numericHnum m <= h)
    (hdiv : bOf m | h)
    (hA : 1 <= A) :
    leafT m h <= 2 * h /\
    h <= blocks A h /\
    2 * blocks A h <= (2 * h - leafT m h) * (2 * blocks A h - 2 * h) /\
    m ^ 2 <= 2 ^ blocks A h /\
    physicalScoreExponent m h + 2 <= blocks A h /\
    physicalScoreExponent m h + 6 <= badExponent m h := by
  let b := bOf m
  let q := h / bOf m
  have hrank : numericRankThreshold m <= h :=
    (numericRank_le_Hnum m).trans hnum
  have hmpos : 0 < m := by omega
  have hb4000 : 4000 <= b := by
    dsimp [b, bOf]
    have hm2 : 1 <= m ^ 2 := by nlinarith
    nlinarith
  have hbpos : 0 < b := by omega
  have hrank' : 10 * m * b <= h := by
    simpa [numericRankThreshold, b] using hrank
  have hmod : h % b = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hdecomp : b * q = h := by
    dsimp [q]
    have hd := Nat.mod_add_div h b
    rw [hmod] at hd
    simpa using hd
  have hq : 10 * m <= q := by
    by_contra hbad
    have hqbad : q + 1 <= 10 * m := by omega
    have hprod := Nat.mul_le_mul_left b hqbad
    nlinarith [hprod, hdecomp, hrank']
  have hqpos : 0 < q := by omega
  have hmle : m <= h := by
    have hmleBase : m <= 10 * m * b := by
      have hm10 : m <= 10 * m := by omega
      have hb1 : 1 <= b := by omega
      have hprod := Nat.mul_le_mul_left (10 * m) hb1
      nlinarith [hm10, hprod]
    exact hmleBase.trans hrank'
  have h4000q : 4000 * q <= h := by
    calc
      4000 * q <= b * q := Nat.mul_le_mul_right q hb4000
      _ = h := hdecomp
  have ht : leafT m h <= 2 * h := by
    dsimp [leafT]
    omega
  have hsmall : 2 * m + 2 <= h := by
    have hm10 : 2 * m + 2 <= 10 * m := by omega
    have hb1 : 1 <= b := by omega
    have hprod := Nat.mul_le_mul_left (10 * m) hb1
    have hlarge : 10 * m <= 10 * m * b := by nlinarith [hprod]
    exact (hm10.trans hlarge).trans hrank'
  have hhsq : 2 * m * h + 2 <= h ^ 2 := by
    have hmul := Nat.mul_le_mul_right h hsmall
    nlinarith [hmpos]
  have hblocks : h ^ 2 < blocks A h := by
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ <= A * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < blocks A h := numerator_lt_blocks A h
  have hmh : h <= m * h := Nat.mul_le_mul_right h (by omega : 1 <= m)
  have h2hsq : 2 * h <= h ^ 2 := by nlinarith [hhsq, hmh]
  have hleJ : h <= blocks A h := by omega
  have h2hJ : 2 * h <= blocks A h := by omega
  have hQle : physicalScoreExponent m h <= 2 * m * h := by
    change 2 * m * (h - 4000 * q) <= 2 * m * h
    exact Nat.mul_le_mul_left (2 * m) (Nat.sub_le _ _)
  have hQJ : physicalScoreExponent m h + 2 <= blocks A h := by
    have hQle' : physicalScoreExponent m h <= 2 * m * h := hQle
    have hQsq : physicalScoreExponent m h + 2 <= h ^ 2 := by
      nlinarith [hhsq, hQle']
    omega
  have hmsq : m ^ 2 <= h ^ 2 := Nat.pow_le_pow_left hmle 2
  have hMpow : m ^ 2 <= 2 ^ blocks A h := by
    have hpow : blocks A h <= 2 ^ blocks A h := nat_le_two_pow (blocks A h)
    exact le_trans (le_trans hmsq hblocks.le) hpow
  have hgap : physicalScoreExponent m h + 6 <= badExponent m h := by
    have hE : badExponent m h = 2 * m * (h - 1000 * q) := by
      rfl
    have hQ : physicalScoreExponent m h = 2 * m * (h - 4000 * q) := by
      rfl
    rw [hE, hQ]
    have hsplit : h - 1000 * q = (h - 4000 * q) + 3000 * q := by omega
    rw [hsplit]
    have hfactor : 6 <= 6000 * m * q := by nlinarith [hmpos, hq]
    have hdist : 2 * m * ((h - 4000 * q) + 3000 * q) =
        2 * m * (h - 4000 * q) + 6000 * m * q := by ring
    rw [hdist]
    omega
  have hs : 2 * h - leafT m h = leafK m h := by
    have hsplit := leaf_split_total (m := m) (h := h)
    omega
  have hkq : leafK m h = 2 * q := leafK_eq_two_mul_quotient hdiv
  have hgeom : 2 * blocks A h <=
      (2 * h - leafT m h) * (2 * blocks A h - 2 * h) := by
    rw [hs, hkq]
    have htail : blocks A h <= 2 * blocks A h - 2 * h := by omega
    have htwoq : 2 <= 2 * q := by omega
    have hmul0 := Nat.mul_le_mul_right (blocks A h) htwoq
    have hmul : 2 * blocks A h <= 2 * q * blocks A h := by
      simpa [Nat.mul_assoc] using hmul0
    exact hmul.trans (Nat.mul_le_mul_left (2 * q) htail)
  exact ⟨ht, hleJ, hgeom, hMpow, hQJ, hgap⟩

private theorem numeric_selected_slack {m h A : Nat}
    (hm : 256 <= m)
    (hnum : numericHnum m <= h)
    (hdiv : bOf m | h)
    (hA : 1 <= A) :
    (1 / 2 : Rat) ^ blocks A h +
      16 * successMargin (badExponent m h) <=
        (1 / 2 : Rat) ^ (physicalScoreExponent m h + 1) := by
  have hg := numeric_selected_guards hm hnum hdiv hA
  have hgap := hg.2.2.2.2.2
  have hpowE : (1 / 2 : Rat) ^ (badExponent m h) <=
      (1 / 2 : Rat) ^ (physicalScoreExponent m h + 6) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap
  have hpowJ : (1 / 2 : Rat) ^ blocks A h <=
      (1 / 2 : Rat) ^ (physicalScoreExponent m h + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hg.2.2.2.2.1
  have hS : successMargin (badExponent m h) =
      (1 / 2 : Rat) ^ badExponent m h := by
    simp [successMargin, one_div]
  have hfactor : 16 * (1 / 2 : Rat) ^ (physicalScoreExponent m h + 6) =
      (1 / 2 : Rat) ^ (physicalScoreExponent m h + 2) := by
    rw [show physicalScoreExponent m h + 6 =
      (physicalScoreExponent m h + 2) + 4 by omega, pow_add]
    norm_num
  have hhalf : (1 / 2 : Rat) ^ (physicalScoreExponent m h + 2) =
      (1 / 2 : Rat) ^ (physicalScoreExponent m h + 1) / 2 := by
    rw [show physicalScoreExponent m h + 2 =
      (physicalScoreExponent m h + 1) + 1 by omega, pow_add]
    norm_num
  rw [hS]
  calc
    (1 / 2 : Rat) ^ blocks A h +
        16 * (1 / 2 : Rat) ^ badExponent m h <=
      (1 / 2 : Rat) ^ (physicalScoreExponent m h + 2) +
        16 * (1 / 2 : Rat) ^ (physicalScoreExponent m h + 6) := by
          exact add_le_add hpowJ (mul_le_mul_of_nonneg_left hpowE (by norm_num))
    _ = (1 / 2 : Rat) ^ (physicalScoreExponent m h + 1) := by
          rw [hfactor]
          linarith [hhalf]

/-- Numeric selection, source-row positivity, and padding construct the
eligible U carrier and every center/leaf fiber used by the ordered law. -/
theorem selected_ordered_carriers_nonempty
    {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (base : Nat -> Nat) (cutoff : Real -> Nat) (A Tpad L m : Nat)
    (hA : 1 <= A) (hpad : 4 <= Tpad) (hrows : 0 < rows)
    (hsel : selector (numericSourceFloor base cutoff) L =
        (m : WithBot Nat)) :
    Nonempty (TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
      (blocks A (hBlock L m))) /\
    (forall U : TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (leafT m (hBlock L m)) U)) /\
    (forall U : TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (blocks A (hBlock L m)),
      forall K : TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (leafT m (hBlock L m)) U,
      Nonempty (TaggedLeafOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (hBlock L m) (questionOf I (actualPaddingCopies (blocks A (hBlock L m)) Tpad) U K))) := by
  rcases selected_explicit_parameters base cutoff hsel with ⟨hm, hnum, hdiv⟩
  have hgeom := numeric_selected_guards hm hnum hdiv hA
  let J := blocks A (hBlock L m)
  let copies := actualPaddingCopies J Tpad
  have hU : Nonempty (TaggedGoodU I copies J) :=
    taggedGoodU_nonempty_of_padding I J Tpad hpad hrows
  have hc : forall U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies (leafT m (hBlock L m)) U) := by
    intro U
    exact taggedCenterOver_nonempty I copies U (by omega)
  have hl : forall U : TaggedGoodU I copies J,
      forall K : TaggedCenterOver I copies (leafT m (hBlock L m)) U,
      Nonempty (TaggedLeafOver I copies (hBlock L m) (questionOf I copies U K)) := by
    intro U K
    exact taggedLeafOver_nonempty I copies U K hgeom.1 hgeom.2.1
  exact ⟨hU, hc, hl⟩

/-- Fixed selected instance and fixed global tables with a high unconditioned
physical score yield one canonical leaf table for which the same selected
star-count U mass is at least `8*S` at density at least `8*S`. The source-row
count is independent from the selector output m. -/
theorem selected_physical_density
    {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (base : Nat -> Nat) (cutoff : Real -> Nat) (A Tpad L m : Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L =
        (m : WithBot Nat))
    [hGood : Nonempty (TaggedGoodU I
      (actualPaddingCopies (blocks A (hBlock L m)) Tpad) (blocks A (hBlock L m)))]
    (hcenter : forall U : TaggedGoodU I
        (actualPaddingCopies (blocks A (hBlock L m)) Tpad) (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (leafT m (hBlock L m)) U))
    (hleaf : forall U : TaggedGoodU I
        (actualPaddingCopies (blocks A (hBlock L m)) Tpad) (blocks A (hBlock L m)),
      forall K : TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (leafT m (hBlock L m)) U,
      Nonempty (TaggedLeafOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (hBlock L m) (questionOf I (actualPaddingCopies (blocks A (hBlock L m)) Tpad) U K)))
    (C : TaggedCenterTable I (actualPaddingCopies (blocks A (hBlock L m)) Tpad))
    (raw : TaggedRawVertexTable I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
      (blocks A (hBlock L m)) (hBlock L m))
    (hphysical : (1 / 2 : Rat) ^
        physicalScoreExponent m (hBlock L m) <
      taggedPhysicalMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (orderedStarLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m) hcenter hleaf).mass
        (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m)) C raw) :
    exists canonical : TaggedLeafTable I
        (actualPaddingCopies (blocks A (hBlock L m)) Tpad),
      8 * successMargin (badExponent m (hBlock L m)) <=
        ∑ U : TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (blocks A (hBlock L m)),
          uniformLaw (TaggedGoodU I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (blocks A (hBlock L m))).mass U *
            (if 8 * successMargin (badExponent m (hBlock L m)) <=
                conditionalCanonicalDensity I
                  (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
                  (k := m) hcenter hleaf C canonical U then (1 : Rat) else 0) := by
  rcases selected_explicit_parameters base cutoff hsel with ⟨hm, hnum, hdiv⟩
  have hgeom := numeric_selected_guards hm hnum hdiv hA
  have hslack := numeric_selected_slack hm hnum hdiv hA
  have hAlpha : (1 / 2 : Rat) ^
      (physicalScoreExponent m (hBlock L m) + 1) <=
        (1 / 2 : Rat) ^ physicalScoreExponent m (hBlock L m) := by
    rw [pow_succ]
    have hp : 0 <= (1 / 2 : Rat) ^ physicalScoreExponent m (hBlock L m) := by positivity
    nlinarith
  have hphysicalLe : (1 / 2 : Rat) ^
      (physicalScoreExponent m (hBlock L m) + 1) <=
        taggedPhysicalMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (orderedStarLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (blocks A (hBlock L m)) (t := leafT m (hBlock L m))
            (h := hBlock L m) (k := m) hcenter hleaf).mass
          (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
            (h := hBlock L m) (k := m)) C raw :=
    le_trans hAlpha (le_of_lt hphysical)
  have hS : 0 <= successMargin (badExponent m (hBlock L m)) := by positivity
  exact ordered_physical_forces_MZ_threshold_U I
    (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
    hcenter hleaf hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
    C raw (successMargin (badExponent m (hBlock L m)))
    ((1 / 2 : Rat) ^ (physicalScoreExponent m (hBlock L m) + 1))
    hS hslack hphysicalLe


/-- A fixed selected instance and fixed global tables with a high unconditioned
physical score yield the selected representative choice, its source-row-valid
canonical table, and the same full eligible-U mass bound. The source-row count
is independent from the selector output m. -/
theorem selected_physical_density_with_rows
    {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
    (base : Nat -> Nat) (cutoff : Real -> Nat) (A Tpad L m : Nat)
    (hA : 1 <= A)
    (hsel : selector (numericSourceFloor base cutoff) L =
        (m : WithBot Nat))
    [hGood : Nonempty (TaggedGoodU I
      (actualPaddingCopies (blocks A (hBlock L m)) Tpad) (blocks A (hBlock L m)))]
    (hcenter : forall U : TaggedGoodU I
        (actualPaddingCopies (blocks A (hBlock L m)) Tpad) (blocks A (hBlock L m)),
      Nonempty (TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (leafT m (hBlock L m)) U))
    (hleaf : forall U : TaggedGoodU I
        (actualPaddingCopies (blocks A (hBlock L m)) Tpad) (blocks A (hBlock L m)),
      forall K : TaggedCenterOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (leafT m (hBlock L m)) U,
      Nonempty (TaggedLeafOver I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (hBlock L m) (questionOf I (actualPaddingCopies (blocks A (hBlock L m)) Tpad) U K)))
    (C : TaggedCenterTable I (actualPaddingCopies (blocks A (hBlock L m)) Tpad))
    (raw : TaggedRawVertexTable I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
      (blocks A (hBlock L m)) (hBlock L m))
    (hphysical : (1 / 2 : Rat) ^
        physicalScoreExponent m (hBlock L m) <
      taggedPhysicalMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (orderedStarLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m) hcenter hleaf).mass
        (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m)) C raw) :
    exists s : TaggedRepresentativeChoice I
        (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (blocks A (hBlock L m)) (hBlock L m),
      And
        (forall P : TaggedPresentedLeaf I
            (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (blocks A (hBlock L m)) (hBlock L m),
          P.respectsRows I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            ((taggedSelectedDomainTable I
              (actualPaddingCopies (blocks A (hBlock L m)) Tpad) raw s)
              (P.domain I (actualPaddingCopies (blocks A (hBlock L m)) Tpad))))
        (8 * successMargin (badExponent m (hBlock L m)) <=
          ∑ U : TaggedGoodU I
            (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (blocks A (hBlock L m)),
            uniformLaw (TaggedGoodU I
              (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
              (blocks A (hBlock L m))).mass U *
              (if 8 * successMargin (badExponent m (hBlock L m)) <=
                  conditionalCanonicalDensity I
                    (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
                    (k := m) hcenter hleaf C
                    (taggedSelectedDomainTable I
                      (actualPaddingCopies (blocks A (hBlock L m)) Tpad) raw s) U
               then (1 : Rat) else 0)) := by
  classical
  have hparams := selected_explicit_parameters base cutoff hsel
  have hm := hparams.1
  have hnum := hparams.2.1
  have hdiv := hparams.2.2
  have hgeom := numeric_selected_guards hm hnum hdiv hA
  have hslack := numeric_selected_slack hm hnum hdiv hA
  have hAlpha : (1 / 2 : Rat) ^
      (physicalScoreExponent m (hBlock L m) + 1) <=
        (1 / 2 : Rat) ^ physicalScoreExponent m (hBlock L m) := by
    rw [pow_succ]
    have hp : 0 <= (1 / 2 : Rat) ^ physicalScoreExponent m (hBlock L m) := by positivity
    nlinarith
  have hphysicalLe : (1 / 2 : Rat) ^
      (physicalScoreExponent m (hBlock L m) + 1) <=
        taggedPhysicalMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (orderedStarLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (blocks A (hBlock L m)) (t := leafT m (hBlock L m))
            (h := hBlock L m) (k := m) hcenter hleaf).mass
          (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
            (h := hBlock L m) (k := m)) C raw :=
    le_trans hAlpha (le_of_lt hphysical)
  have hchoice := tagged_sample_exists_selected_le_twoNegJ I
      (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
      hcenter hleaf hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 C raw
  let s := Classical.choose hchoice
  have hcompare := Classical.choose_spec hchoice
  have hcompareOrdered :
      taggedPhysicalMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (orderedStarLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m) hcenter hleaf).mass
        (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m)) C raw <=
      taggedSelectedMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
        (taggedSampleLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          hcenter hleaf).mass
        (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
          (h := hBlock L m) (k := m)) C raw s +
        (1 / 2 : Rat) ^ blocks A (hBlock L m) := by
    simpa only [orderedStarLaw_eq_taggedSampleLaw I
      (actualPaddingCopies (blocks A (hBlock L m)) Tpad) hcenter hleaf] using hcompare
  have hselected :
      16 * successMargin (badExponent m (hBlock L m)) <=
        taggedSelectedMass I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
          (taggedSampleLaw I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            hcenter hleaf).mass
          (sampledStar I (actualPaddingCopies (blocks A (hBlock L m)) Tpad)
            (J := blocks A (hBlock L m)) (t := leafT m (hBlock L m))
            (h := hBlock L m) (k := m)) C raw s := by
    linarith [hphysicalLe, hcompareOrdered, hslack]
  let copies := actualPaddingCopies (blocks A (hBlock L m)) Tpad
  let J := blocks A (hBlock L m)
  let h := hBlock L m
  let Tsel := taggedSelectedDomainTable I copies raw s
  have hselectedMean :
      taggedSelectedMass I copies (taggedSampleLaw I copies hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := leafT m h) (h := h) (k := m))
        C raw s =
      ∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U *
          conditionalCanonicalDensity I copies (k := m) hcenter hleaf C Tsel U := by
    calc
      _ = ∑ ω : TaggedSample I copies J (leafT m h) h m,
            (taggedSampleLaw I copies hcenter hleaf).mass ω *
              (if taggedAccepts I copies C Tsel
                  (sampledStar I copies ω).q
                  (taggedConvertedLeaves I copies (sampledStar I copies ω))
               then (1 : Rat) else 0) := by
        unfold taggedSelectedMass
        apply Finset.sum_congr rfl
        intro ω hω
        rw [taggedSelectedAccepts_iff_taggedAccepts I copies C raw s
          (sampledStar I copies ω)]
      _ = ∑ ω : TaggedSample I copies J (leafT m h) h m,
            (orderedStarLaw I copies J (t := leafT m h) (h := h) (k := m)
              hcenter hleaf).mass ω *
              (if taggedAccepts I copies C Tsel
                  (sampledStar I copies ω).q
                  (taggedConvertedLeaves I copies (sampledStar I copies ω))
               then (1 : Rat) else 0) := by
        simp_rw [← orderedStarLaw_eq_taggedSampleLaw I copies hcenter hleaf]
      _ = ∑ U : TaggedGoodU I copies J,
            (uniformLaw (TaggedGoodU I copies J)).mass U *
              conditionalCanonicalDensity I copies (k := m) hcenter hleaf C Tsel U :=
        ordered_canonical_eq_uniformU_mean I copies hcenter hleaf C Tsel
  have hmean : 16 * successMargin (badExponent m h) <=
      ∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U *
          conditionalCanonicalDensity I copies (k := m) hcenter hleaf C Tsel U := by
    rw [← hselectedMean]
    simpa [copies, J, h] using hselected
  let delta : TaggedGoodU I copies J -> Rat := fun U =>
    conditionalCanonicalDensity I copies (k := m) hcenter hleaf C Tsel U
  have hdelta (U : TaggedGoodU I copies J) : And (0 <= delta U) (delta U <= 1) :=
    conditionalCanonicalDensity_nonneg_le_one I copies hcenter hleaf C Tsel U
  let mu := uniformLaw (TaggedGoodU I copies J)
  let beta : Rat := 16 * successMargin (badExponent m h)
  have hbeta : 0 <= beta := by
    dsimp [beta]
    positivity
  have hpoint (U : TaggedGoodU I copies J) :
      mu.mass U * delta U <=
        mu.mass U * (beta / 2 + if beta / 2 <= delta U then (1 : Rat) else 0) := by
    apply mul_le_mul_of_nonneg_left _ (mu.nonneg U)
    by_cases hu : beta / 2 <= delta U
    · simp only [hu, if_true]
      linarith [hbeta, (hdelta U).2]
    · simp only [hu, if_false, add_zero]
      exact le_of_lt (lt_of_not_ge hu)
  have hsum := Finset.sum_le_sum
    (fun U (_ : U ∈ (Finset.univ : Finset (TaggedGoodU I copies J))) => hpoint U)
  have hnorm := mu.normalized
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul] at hsum
  have hmeanMu : beta <=
      ∑ U : TaggedGoodU I copies J, mu.mass U * delta U := by
    simpa [beta, mu, delta] using hmean
  have hmassHalf : beta / 2 <=
      ∑ U : TaggedGoodU I copies J,
        mu.mass U * (if beta / 2 <= delta U then (1 : Rat) else 0) := by
    linarith [hmeanMu, hsum]
  have hhalf : beta / 2 = 8 * successMargin (badExponent m h) := by
    dsimp [beta]
    ring
  have hmass : 8 * successMargin (badExponent m h) <=
      ∑ U : TaggedGoodU I copies J,
        (uniformLaw (TaggedGoodU I copies J)).mass U *
          (if 8 * successMargin (badExponent m h) <= delta U then (1 : Rat) else 0) := by
    simpa [mu, hhalf] using hmassHalf
  have hrows : forall P : TaggedPresentedLeaf I copies J h,
      P.respectsRows I copies (Tsel (P.domain I copies)) := by
    intro P
    change P.respectsRows I copies
      ((taggedSelectedDomainTable I copies raw s) (P.domain I copies))
    rw [taggedSelectedDomainTable_apply I copies raw s P]
    exact taggedSelectedLeafLabel_respectsRows I copies raw s P
  exact Exists.intro s (And.intro
    (by simpa [copies, J, h, Tsel] using hrows)
    (by simpa [copies, J, h, Tsel, delta] using hmass))

end
end PvNP.RealizableHardness.ActualNumericPhysicalDensity