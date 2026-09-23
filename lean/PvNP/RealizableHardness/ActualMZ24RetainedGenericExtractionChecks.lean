import PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
import PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransportChecks
import Mathlib.Tactic

/-! B2b API and seam checks.  These exercise the exact positive-bucket
representative/functional bridge and the actual Zoom/component-law bridge;
they are not a B2b source-instance or a D3c5 conclusion. -/

namespace PvNP.RealizableHardness.ActualMZ24RetainedGenericExtractionChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
open PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction.RetainedGenericExtractionOutput
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check positiveBucketRootPair
#check positiveBucketRootPair_W
#check positiveBucketRootPair_eq_representative
#check positiveBucketRootPair_agreement
#check zoomToPointedEquiv
#check zoomToPointed_uniformLaw
#check outputSelectedFamily
#check RetainedGenericExtractionOutput.rootPair_eq_representative
#check RetainedGenericExtractionOutput.localPair_W_eq
#check RetainedGenericExtractionOutput.localAgreement_eq_source
#check RetainedGenericExtractionOutput.complementAgreement_ge
#check RetainedGenericExtractionOutput.selectedFamily
#check RetainedGenericExtractionOutput.adapterLocalPair_W_eq
#check RetainedGenericExtractionOutput.adapterTable
#check RetainedGenericExtractionOutput.adapterComponentLaw
#check RetainedGenericExtractionOutput.adapterAgreementEventMass
#check RetainedGenericExtractionOutput.adapterAgreementEventMass_ge
#check retainedGenericExtraction
#check RetainedGenericExtractionOutput.bucket_lower
#check RetainedGenericExtractionOutput.terminal_card
#check RetainedGenericExtractionOutput.fixed_ambient_card
#check RetainedGenericExtractionOutput.QE_map_recovery
#check RetainedGenericExtractionOutput.selectedFamily
#check RetainedGenericExtractionOutput.sampling
#check RetainedGenericExtractionOutput.final_E1

section DerivedAdapterIdentity

variable {Aof budget totalHMin : Nat → Nat}
variable (H : DominatingSamplingCutoff Aof budget totalHMin)
variable (Lsrc m D a0 : Nat)
variable (hsel : selector totalHMin Lsrc = (m : WithBot Nat))
variable (draw : Draw (blocks (Aof m) (hBlock Lsrc m)))
variable (Q0 : Grass (retained draw) a0)
variable (T0 : (L : Grass (retained draw) (2 * hBlock Lsrc m)) →
  Module.Dual (ZMod 2) L.val)
variable {K : Type*} [Fintype K]
variable (P : K → DecodedPair Q0 (2 * hBlock Lsrc m)) (beta : Rat)
variable (hP : Function.Injective P)
variable (had_gap : a0 < 2 * hBlock Lsrc m)
variable (hagr : ∀ i, beta ≤ agreement T0 Q0 (P i))
variable (O : RetainedGenericExtractionOutput H Lsrc m D a0 hsel draw
  Q0 T0 P beta hP had_gap hagr)

theorem selectedFamily_scalar_and_data_identity :
    let F := selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O
    F.E = O.T.E ∧ F.a = a0 ∧ F.h = hBlock Lsrc m ∧
      F.r = budget m ∧ F.r' = O.T.r ∧ F.c = O.c ∧ F.t = tD D ∧
      F.Q = PhaseAGeometry.QE
        (fun U : PositiveBucketIndex P O.c => U.1)
        Q0 O.T.toPhaseAGeometry ∧ F.C = O.C ∧ F.W = O.WJ := by
  dsimp [selectedFamily, outputSelectedFamily]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem selected_component_eventMass_ge (j : FinalIndex (O := O)) :
    letI : Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) :=
      adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j
    beta ≤ eventMass (componentLaw
          (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O).regularIncidence j)
        (pointedAgreementEvent
          (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O) j
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j)
          (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j)
          (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O)) :=
  adapterAgreementEventMass_ge H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP had_gap hagr O j

theorem selected_final_stage_strict_E1 :
    2 ^ geometricOutputExponent D O.c (hBlock Lsrc m) <
      Fintype.card {j : O.T.Index // j ∈ O.J} := by
  rw [O.final_index_card]
  exact O.final_E1

theorem selected_family_W_injective :
    Function.Injective
      (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O).W :=
  (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP had_gap hagr O).injective

theorem distinct_final_indices_have_distinct_W
    (j k : FinalIndex (O := O)) (hjk : j ≠ k) :
    (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).W j ≠
    (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).W k := by
  intro hW
  exact hjk ((selected_family_W_injective H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP had_gap hagr O) hW)

end DerivedAdapterIdentity

section ActualProducerStageRegression

variable {Aof budget totalHMin : Nat -> Nat}
variable (H : DominatingSamplingCutoff Aof budget totalHMin)
variable (Lsrc m D a0 : Nat)
variable (hsel : selector totalHMin Lsrc = (m : WithBot Nat))
variable (draw : Draw (blocks (Aof m) (hBlock Lsrc m)))
variable (Q0 : Grass (retained draw) a0)
variable (T0 : (L : Grass (retained draw) (2 * hBlock Lsrc m)) ->
  Module.Dual (ZMod 2) L.val)
variable {K : Type*} [Fintype K]
variable (P : K -> DecodedPair Q0 (2 * hBlock Lsrc m)) (beta : Rat)
variable (hP : Function.Injective P)
variable (hD : 0 < D) (had_gap : a0 < 2 * hBlock Lsrc m)
variable (hlarge : forall i, 10 * (2 * hBlock Lsrc m) <=
  Module.finrank (ZMod 2) (P i).W)
variable (hbeta : 0 < beta)
variable (hthreshold : 4 / (2 : Rat) ^ (2 * hBlock Lsrc m - a0) < beta)
variable (hagr : forall i, beta <= agreement T0 Q0 (P i))
variable (hcodim : forall i, codim (P i).W <= budget m)
variable (hforce : (16 : Rat) *
  (1 + (budget m : Rat) * (2 : Rat) ^
    inputExponent D (budget m) (hBlock Lsrc m)) <
  beta ^ 2 * (Fintype.card K : Rat))

theorem actual_producer_stage_card_and_E1 :
    let O := retainedGenericExtraction H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP hD had_gap hlarge hbeta hthreshold hagr hcodim hforce
    Fintype.card (PositiveBucketIndex P O.c) = O.B.card ∧
      Fintype.card O.T.Index = O.T.C.card ∧
      Fintype.card {j : O.T.Index // j ∈ O.J} = O.J.card ∧
      2 ^ geometricOutputExponent D O.c (hBlock Lsrc m) <
        Fintype.card {j : O.T.Index // j ∈ O.J} := by
  let O := retainedGenericExtraction H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP hD had_gap hlarge hbeta hthreshold hagr hcodim hforce
  change Fintype.card (PositiveBucketIndex P O.c) = O.B.card ∧
    Fintype.card O.T.Index = O.T.C.card ∧
    Fintype.card {j : O.T.Index // j ∈ O.J} = O.J.card ∧
    2 ^ geometricOutputExponent D O.c (hBlock Lsrc m) <
      Fintype.card {j : O.T.Index // j ∈ O.J}
  exact ⟨O.bucket_index_card, O.T.index_card, O.final_index_card, by
    rw [O.final_index_card]
    exact O.final_E1⟩

end ActualProducerStageRegression

#check selectedFamily_scalar_and_data_identity

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} {Q : Grass V a} {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) :
    positiveBucketRootPair P c U =
      P (positiveBucketRepresentative P c U) :=
  positiveBucketRootPair_eq_representative P c U

/-- A concrete F₂² fixture isolates pair-count from distinct-W count. -/
abbrev DuplicateV := Fin 2 → ZMod 2

def duplicateQ : Grass DuplicateV 0 := ⟨⊥, by simp⟩

def duplicateCoordinateForm1 : Module.Dual (ZMod 2) DuplicateV :=
  LinearMap.proj 1

def duplicateCoordinateForm0 : Module.Dual (ZMod 2) DuplicateV :=
  LinearMap.proj 0

def duplicateE0 : DuplicateV := fun i => if i = 0 then 1 else 0

def duplicateE1 : DuplicateV := fun i => if i = 1 then 1 else 0

theorem duplicateCoordinateForm1_ne_zero :
    duplicateCoordinateForm1 ≠ 0 := by
  intro h
  have he : duplicateCoordinateForm1 duplicateE1 = 1 := by
    simp [duplicateCoordinateForm1, duplicateE1]
  have hzero := congrArg (fun f : Module.Dual (ZMod 2) DuplicateV =>
    f duplicateE1) h
  rw [hzero] at he
  norm_num at he

def duplicateW : Submodule (ZMod 2) DuplicateV :=
  LinearMap.ker duplicateCoordinateForm1

theorem duplicateW_finrank :
    Module.finrank (ZMod 2) duplicateW = 1 := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero
    duplicateCoordinateForm1_ne_zero
  have hV : Module.finrank (ZMod 2) DuplicateV = 2 := by
    simp [DuplicateV, Module.finrank_pi]
  rw [hV] at hk
  change Module.finrank (ZMod 2)
    (LinearMap.ker duplicateCoordinateForm1) = 1
  omega

theorem duplicateW_codim : codim duplicateW = 1 := by
  have hV : Module.finrank (ZMod 2) DuplicateV = 2 := by
    simp [DuplicateV, Module.finrank_pi]
  unfold codim
  rw [hV, duplicateW_finrank]

theorem duplicateE0_mem_W : duplicateE0 ∈ duplicateW := by
  change duplicateCoordinateForm1 duplicateE0 = 0
  simp [duplicateCoordinateForm1, duplicateE0]

def duplicateG1 : Module.Dual (ZMod 2) duplicateW :=
  duplicateCoordinateForm0.comp duplicateW.subtype

theorem duplicateG1_eval :
    duplicateG1 ⟨duplicateE0, duplicateE0_mem_W⟩ = 1 := by
  change duplicateCoordinateForm0 duplicateE0 = 1
  simp [duplicateCoordinateForm0, duplicateE0]

theorem duplicateG1_ne_zero : duplicateG1 ≠ 0 := by
  intro h
  have hval := congrArg
    (fun f : Module.Dual (ZMod 2) duplicateW =>
      f ⟨duplicateE0, duplicateE0_mem_W⟩) h
  have heval := duplicateG1_eval
  rw [hval] at heval
  norm_num at heval

def duplicatePair0 : DecodedPair duplicateQ 1 :=
  { W := duplicateW, hQW := bot_le, g := 0 }

def duplicatePair1 : DecodedPair duplicateQ 1 :=
  { W := duplicateW, hQW := bot_le, g := duplicateG1 }

theorem duplicatePair0_ne_pair1 : duplicatePair0 ≠ duplicatePair1 := by
  intro h
  have hp := congrArg
    (fun p : DecodedPair duplicateQ 1 => p.g = 0) h
  have hz : duplicatePair1.g = 0 :=
    Eq.mp hp (show duplicatePair0.g = 0 from rfl)
  exact duplicateG1_ne_zero hz

def duplicatePairs : Fin 2 → DecodedPair duplicateQ 1 :=
  fun i => if i = 0 then duplicatePair0 else duplicatePair1

theorem duplicatePairs_injective : Function.Injective duplicatePairs := by
  intro i j hij
  have h10 : duplicatePair1 ≠ duplicatePair0 := fun h =>
    duplicatePair0_ne_pair1 h.symm
  fin_cases i <;> fin_cases j <;>
    simp_all [duplicatePairs, duplicatePair0_ne_pair1, h10]

theorem duplicatePairs_same_W :
    (duplicatePairs 0).W = (duplicatePairs 1).W := by
  rfl

theorem duplicatePairCodimBucket_card :
    Fintype.card (PairCodimBucket duplicatePairs 1) = 2 := by
  have hall (i : Fin 2) :
      codim (duplicatePairs i).W = 1 := by
    fin_cases i <;> simp [duplicatePairs, duplicatePair0, duplicatePair1,
      duplicateW_codim]
  let e : PairCodimBucket duplicatePairs 1 ≃ Fin 2 :=
    { toFun := fun i => i.1
      invFun := fun i => ⟨i, hall i⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; rfl }
  exact Fintype.card_congr e

theorem duplicateWSubspaceBucket_card :
    (codimSubspaceBucket duplicatePairs 1).card = 1 := by
  have hsub : pairSubspaces duplicatePairs = {duplicateW} := by
    classical
    ext W
    simp [pairSubspaces, duplicatePairs, duplicatePair0, duplicatePair1,
      eq_comm]
  have hfilter :
      ({duplicateW} : Finset (Submodule (ZMod 2) DuplicateV)).filter
          (fun W => codim W = 1) = {duplicateW} := by
    apply Finset.filter_eq_self.mpr
    intro W hW
    rw [Finset.mem_singleton] at hW
    subst W
    exact duplicateW_codim
  unfold codimSubspaceBucket
  rw [hsub, hfilter]
  simp

theorem duplicatePositiveBucketIndex_card :
    Fintype.card (PositiveBucketIndex duplicatePairs 1) = 1 := by
  change Fintype.card
    {U : Submodule (ZMod 2) DuplicateV //
      U ∈ codimSubspaceBucket duplicatePairs 1} = 1
  rw [Fintype.card_coe]
  exact duplicateWSubspaceBucket_card

#check selected_final_stage_strict_E1
#check E1_47
#check E1_not_75
#check selected_family_W_injective
#check distinct_final_indices_have_distinct_W
#check actual_producer_stage_card_and_E1
#check duplicatePairCodimBucket_card
#check duplicatePairs_injective
#check duplicatePairs_same_W
#check duplicateG1_ne_zero
#check duplicateWSubspaceBucket_card
#check duplicatePositiveBucketIndex_card

#print axioms positiveBucketRootPair_eq_representative
#print axioms zoomToPointed_uniformLaw
#print axioms RetainedGenericExtractionOutput.adapterComponentLaw
#print axioms RetainedGenericExtractionOutput.adapterAgreementEventMass
#print axioms outputSelectedFamily
#print axioms selectedFamily_scalar_and_data_identity
#print axioms RetainedGenericExtractionOutput.adapterAgreementEventMass_ge
#print axioms selected_component_eventMass_ge
#print axioms selected_final_stage_strict_E1
#print axioms selected_family_W_injective
#print axioms distinct_final_indices_have_distinct_W
#print axioms actual_producer_stage_card_and_E1
#print axioms duplicatePairCodimBucket_card
#print axioms duplicateWSubspaceBucket_card
#print axioms duplicatePositiveBucketIndex_card
#print axioms retainedGenericExtraction

end
end PvNP.RealizableHardness.ActualMZ24RetainedGenericExtractionChecks
