import PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
import PvNP.RealizableHardness.ActualMZ24D3c5Precomposition
import PvNP.RealizableHardness.VectorAdvice

/-! Join of many-W extraction, the fixed-score decoder, and the repeated game.

The list bound is the existing D3b2 multiplicity `16 / beta^2`, not a looser
constant. The exponent budget is the existing guarded ledger
`50*c*h*D^5 + L6 ≤ Ecap`. The repeated-game score is
`ZoomOutJoint.jointSuccess` after the vector-advice dependence error.
-/

namespace PvNP.RealizableHardness.ActualManyWDecoderGameJoin

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
open PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
open PvNP.RealizableHardness.ActualMZ24D3c5Precomposition
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.GrassmannIncidence
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ZoomOutJoint
open PvNP.RealizableHardness.VectorAdvice
open PvNP.RealizableHardness.GoodAdvice
open PvNP.RealizableHardness.PosteriorReweighting
open PvNP.RealizableHardness.PosteriorDensity
open PvNP.RealizableHardness.AdviceExceptions
open PvNP.RealizableHardness.ZoomOutPosterior

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A list no larger than `16 / beta^2` gives uniform hit probability at least
`beta^2 / 16`. The constant is the D3b2 multiplicity. -/
theorem sixteen_factor_of_list_card {N : Nat} {beta : ℚ}
    (hbeta : 0 < beta) (hN : 0 < N)
    (hlist : (N : ℚ) ≤ 16 / beta ^ 2) :
    beta ^ 2 / 16 ≤ 1 / (N : ℚ) := by
  have hb2 : 0 < beta ^ 2 := sq_pos_of_pos hbeta
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have h16 : (0 : ℚ) < 16 := by norm_num
  have hmul : beta ^ 2 * (N : ℚ) ≤ 16 := by
    have hNmul : (N : ℚ) * beta ^ 2 ≤ 16 := (le_div_iff₀ hb2).mp hlist
    simpa [mul_comm] using hNmul
  have hdiv : beta ^ 2 ≤ 16 / (N : ℚ) := (le_div_iff₀ hNpos).mpr hmul
  rw [div_le_iff₀ h16]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat} {Q : Grass V a}
variable {I : Type*} [Fintype I]

variable {Aof budget totalHMin : Nat → Nat}
variable {Lsrc m D a0 : Nat}
variable {K : Type*} [Fintype K]
variable {H : DominatingSamplingCutoff Aof budget totalHMin}
variable {hsel : selector totalHMin Lsrc = (m : WithBot Nat)}
variable {draw : Draw (blocks (Aof m) (hBlock Lsrc m))}
variable {Q0 : Grass (retained draw) a0}
variable {T0 : (L : Grass (retained draw) (2 * hBlock Lsrc m)) →
  Module.Dual (ZMod 2) L.val}
variable {Pext : K → DecodedPair Q0 (2 * hBlock Lsrc m)} {betaExt : Rat}
variable {hPext : Function.Injective Pext}
variable {had_gap : a0 < 2 * hBlock Lsrc m}
variable {hagr : ∀ i, betaExt ≤ agreement T0 Q0 (Pext i)}

/-- Many-W fibres stay at `16 / beta^2`, the guarded ledger still bounds
`L6` by `Ecap`, and the repeated game pays only the vector-advice error
on top of the decoder margin `C/8`. -/
theorem manyW_decoder_repeatedGame_join
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (hP : Function.Injective P) (betaList : Rat)
    (had : a ≤ d) (hgap : a < d)
    (hlarge : ∀ i, 10 * d ≤ Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < betaList) (hthreshold : 4 / (2 ^ (d - a) : Rat) < betaList)
    (hagrees : ∀ i, betaList ≤ agreement T Q (P i))
    (W : PairSubspaceIndex P)
    (hFibre : 0 < Fintype.card (PairWFiber P W))
    (O : RetainedGenericExtractionOutput H Lsrc m D a0 hsel draw Q0 T0
      Pext betaExt hPext had_gap hagr)
    (hD : 0 < D) (hR : 2 ≤ budget m)
    (hreserve : 3 * budget m + 1000 * (budget m + 1) * D ^ 5 + a0 + 5 ≤
      10 * hBlock Lsrc m)
    {A r h adv : ℕ}
    (hReady : SamplerProximity.Ready A r h) (hh : r < h) (ha : adv ≤ r)
    (hBlocks : r ≤ blocks A h)
    (F : Advice (blocks A h) adv → Bool)
    (Wdec : Advice (blocks A h) adv → Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) adv → Advice (blocks A h) (2 * h) → ℚ)
    (C : ℚ) (hC : 0 < C) (hC1 : C ≤ 1)
    (hdelta : 2 * qdecay 10 h ≤ C) (hrank : 16 * zeta h ≤ C)
    (hdecoder : ∀ Qadv, F Qadv = true → Qadv.val ≤ Wdec Qadv ∧
      SubspaceRestriction.codim (Wdec Qadv) ≤ r ∧
      (∀ L, 0 ≤ f Qadv L ∧ f Qadv L ≤ 1) ∧
      C ≤ mean (ZoomOutTransfer.ambientW Qadv (Wdec Qadv)) (f Qadv)) :
    (Fintype.card (PairWFiber P W) : ℚ) ≤ 16 / betaList ^ 2 ∧
      betaList ^ 2 * (Fintype.card I : ℚ) ≤ 16 * (pairSubspaces P).card ∧
      betaList ^ 2 / 16 ≤ 1 / (Fintype.card (PairWFiber P W) : ℚ) ∧
      50 * O.c * hBlock Lsrc m * D ^ 5 +
          L6 O.c (hBlock Lsrc m) O.T.r D a0 ≤
        Ecap D (budget m) O.c (hBlock Lsrc m) ∧
      2 ^ Ecap D (budget m) O.c (hBlock Lsrc m) < O.J.card ∧
      (mass ambientMass F - mass ambientMass (bad (a := adv) A h) -
          adviceTV (beta A h) (blocks A h) adv) * (C / 8) ≤
        jointSuccess F Wdec f C ∧
      (jointSuccess F Wdec f C : ℝ) - error r (blocks A h) ≤
        actualJointScore (beta A h) (fun s Qadv =>
          if favorable F Qadv && succeeds Qadv (Wdec Qadv) (f Qadv) C s then
            1 else 0) := by
  have hW := pairWFiber_card_le_sixteen_div_sq T P hP betaList had hgap hlarge
    hbeta hthreshold hagrees W
  have hAgg := pairSubspaces_aggregate_division_free T P hP betaList had hgap
    hlarge hbeta hthreshold hagrees
  have hFactor := sixteen_factor_of_list_card hbeta hFibre hW
  have hr' : 1 ≤ O.T.r := by
    have hpos := O.T.residual_pos
    omega
  have hr'c : O.T.r ≤ O.c :=
    ActualMZ24PhaseATypedStep.PhaseAGeometry.r_le_c
      (fun U : ActualMZ24GenericSubfamilyRepresentative.PositiveBucketIndex Pext O.c =>
        (U : Submodule (ZMod 2) (retained draw)))
      Q0 O.T.toPhaseAGeometry
  have hLedger := guarded_loss_ledger (O := O) hD hR O.c_pos O.c_le_budget
    hr' hr'c hreserve
  have hCap := cap_sensitive_J_count (O := O) hD
  have hGame := ready_joint_success hReady hh ha F Wdec f C hC hC1 hdelta
    hrank hdecoder
  have hVec := decoder_event_transfer ha hBlocks F Wdec f C
  exact ⟨hW, hAgg, hFactor, hLedger, hCap, hGame, hVec⟩

end
end PvNP.RealizableHardness.ActualManyWDecoderGameJoin
