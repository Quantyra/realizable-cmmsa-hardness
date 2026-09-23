import PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
import PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
import PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
import PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducer
import PvNP.RealizableHardness.ActualMZ24GenericArityIteration
import PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
import PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
import PvNP.RealizableHardness.ActualFiniteIncidenceSampling
import Mathlib.Tactic

/-! B2b: retained many-W extraction assembled from the actual distinct-W
bucket, the B1 terminal producer, fixed-ambient arity closure, and the
accepted retained sampling adapter.  The component agreement event remains
candidate-dependent; this module makes no common-functional or decoder claim.
-/

namespace PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24HyperplaneSupport
open PvNP.RealizableHardness.ActualMZ24DistinctPairAggregation
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
open PvNP.RealizableHardness.ActualMZ24PhaseAStopping
open PvNP.RealizableHardness.ActualMZ24PhaseATypedStep
open PvNP.RealizableHardness.ActualMZ24PhaseATerminalProducer
open PvNP.RealizableHardness.ActualMZ24GenericArityIteration
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open PvNP.RealizableHardness.ActualMZ24TerminalAgreementTransport
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.TripleRestrictionRank

set_option maxRecDepth 1000000
set_option exponentiation.threshold 100000
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

universe uV uI
variable {V : Type uV} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {a d : Nat} {Q : Grass V a}

private theorem dependentTransport_back
    {A B : Submodule (ZMod 2) V} (h : A = B)
    (g : Module.Dual (ZMod 2) A) : h.symm ▸ (h ▸ g) = g := by
  cases h
  rfl

/-- The unique decoded functional attached to a distinct positive-bucket
subspace is the one transported from its canonical representative. -/
noncomputable def positiveBucketRootPair {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) : DecodedPair Q d := by
  have hcontains : Q.val ≤ U.1 := by
    obtain ⟨hmem, _⟩ := Finset.mem_filter.mp U.2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    rw [← hi]
    exact (P i).hQW
  exact ⟨U.1, hcontains, positiveBucketFunctional P c U⟩

theorem positiveBucketRootPair_W {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) :
    (positiveBucketRootPair P c U).W = U.1 := rfl

theorem positiveBucketRootPair_eq_representative {I : Type*} [Fintype I]
    (P : I → DecodedPair Q d) (c : Nat)
    (U : PositiveBucketIndex P c) :
    positiveBucketRootPair P c U =
      P (positiveBucketRepresentative P c U) := by
  apply decodedPair_ext_of_transport
    ((positiveBucketRootPair_W P c U).trans
      (positiveBucketRepresentative_W_eq P c U).symm)
  dsimp [positiveBucketRootPair, positiveBucketFunctional]
  exact dependentTransport_back (positiveBucketRepresentative_W_eq P c U)
    (P (positiveBucketRepresentative P c U)).g

theorem positiveBucketRootPair_agreement {I : Type*} [Fintype I]
    (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (P : I → DecodedPair Q d) (c : Nat) (beta : Rat)
    (hagr : ∀ i, beta ≤ agreement T Q (P i))
    (U : PositiveBucketIndex P c) :
    beta ≤ agreement T Q (positiveBucketRootPair P c U) := by
  rw [positiveBucketRootPair_eq_representative]
  exact positiveBucketRepresentative_agreement T P c beta hagr U

/-- A selected component Zoom is exactly the fibre of the actual pointed
incidence relation.  This is the typed bridge needed before transporting its
agreement event; it does not identify events across different components. -/
noncomputable def zoomToPointedEquiv
    {I : Type*} [Fintype I]
    (F : EnlargedPointedFamily (V := V) (I := I)) (i : I)
    (P : DecodedPair F.Q (2 * F.h))
    (hPW : P.W = F.W i) :
    Zoom F.Q P ≃ {L : F.pointedCarrier //
      F.regularIncidence.rel i L} := by
  classical
  refine
    { toFun := fun z =>
        ⟨⟨z.1, z.2.1⟩, ?_⟩
      invFun := fun z =>
        ⟨z.1.1, z.1.2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change z.1.val ≤ F.W i
    simpa [hPW] using z.2.2
  · change z.1.1.val ≤ P.W
    have hz := z.property
    change z.1.1.val ≤ F.W i at hz
    simpa [hPW] using hz
  · intro z
    apply Subtype.ext
    rfl
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem uniformFiber_pushforward
    {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty Ω]
    (R : RegularIncidence I Ω) (i : I)
    [Nonempty {y : Ω // R.rel i y}] :
    pushforward (fun x : {y : Ω // R.rel i y} => x.1)
      (uniformLaw {y : Ω // R.rel i y}) = componentLaw R i := by
  classical
  have hcard := R.regular i
  apply FiniteLaw.ext
  intro x
  rw [pushforward_apply, componentLaw_apply]
  by_cases hx : R.rel i x
  · rw [if_pos hx]
    rw [Finset.sum_eq_single ⟨x, hx⟩]
    · simp [uniformLaw_apply, hcard]
    · intro y hy hne
      have hyx : y.1 ≠ x := by
        intro heq
        apply hne
        exact Subtype.ext heq
      simp [uniformLaw_apply, hyx]
    · simp
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y hy
    have hyx : y.1 ≠ x := by
      intro heq
      exact hx (heq ▸ y.2)
    simp [uniformLaw_apply, hyx]

/-- The actual component law is the pushforward of the uniform selected Zoom
law whenever the selected decoded pair has the component's W. -/
theorem zoomToPointed_uniformLaw
    {I : Type*} [Fintype I]
    (F : EnlargedPointedFamily (V := V) (I := I))
    (i : I) (P : DecodedPair F.Q (2 * F.h))
    (hPW : P.W = F.W i) [Nonempty (Zoom F.Q P)] :
    pushforward (fun z : Zoom F.Q P => (zoomToPointedEquiv F i P hPW z).1)
      (uniformLaw (Zoom F.Q P)) = componentLaw F.regularIncidence i := by
  classical
  let e := zoomToPointedEquiv F i P hPW
  let fiber := {L : F.pointedCarrier // F.regularIncidence.rel i L}
  have hcard : Fintype.card fiber = F.regularIncidence.fibreCard :=
    F.regularIncidence.regular i
  have hfiber : Nonempty fiber := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact F.regularIncidence.fibreCard_pos
  letI : Nonempty fiber := hfiber
  calc
    pushforward (fun z : Zoom F.Q P => (e z).1) (uniformLaw (Zoom F.Q P)) =
        pushforward Subtype.val
          (pushforward e (uniformLaw (Zoom F.Q P))) := by
            exact (pushforward_comp e Subtype.val
              (uniformLaw (Zoom F.Q P))).symm
    _ = pushforward Subtype.val (uniformLaw fiber) := by
          rw [pushforward_uniformLaw_equiv e]
    _ = componentLaw F.regularIncidence i :=
          uniformFiber_pushforward F.regularIncidence i

noncomputable def zoom_nonempty_of_component
    {I : Type*} [Fintype I]
    (F : EnlargedPointedFamily (V := V) (I := I))
    (i : I) (P : DecodedPair F.Q (2 * F.h))
    (hPW : P.W = F.W i) : Nonempty (Zoom F.Q P) := by
  classical
  let e := zoomToPointedEquiv F i P hPW
  let fiber := {L : F.pointedCarrier // F.regularIncidence.rel i L}
  have hcard : Fintype.card fiber = F.regularIncidence.fibreCard :=
    F.regularIncidence.regular i
  have hfiber : Nonempty fiber := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact F.regularIncidence.fibreCard_pos
  exact ⟨e.symm (Classical.choice hfiber)⟩

/-- The event transported to a pointed query is indexed by this particular
decoded pair and component.  It is not a single mixture event shared across
different functionals. -/
def pointedAgreementEvent
    {I : Type*} [Fintype I]
    (F : EnlargedPointedFamily (V := V) (I := I)) (i : I)
    (P : DecodedPair F.Q (2 * F.h)) (hPW : P.W = F.W i)
    (T : (L : Grass F.E (2 * F.h)) → Module.Dual (ZMod 2) L.val) :
    Finset F.pointedCarrier :=
  Finset.univ.filter (fun x => ∃ z : Zoom F.Q P,
    (zoomToPointedEquiv F i P hPW z).1 = x ∧
      z ∈ agreeingEvent T F.Q P)

theorem zoomAgreement_component_eventMass
    {I : Type*} [Fintype I]
    (F : EnlargedPointedFamily (V := V) (I := I))
    (i : I) (P : DecodedPair F.Q (2 * F.h)) (hPW : P.W = F.W i)
    (T : (L : Grass F.E (2 * F.h)) → Module.Dual (ZMod 2) L.val)
    [Nonempty (Zoom F.Q P)] :
    eventMass (componentLaw F.regularIncidence i)
        (pointedAgreementEvent F i P hPW T) =
      eventMass (uniformLaw (Zoom F.Q P)) (agreeingEvent T F.Q P) := by
  classical
  let f : Zoom F.Q P → F.pointedCarrier :=
    fun z => (zoomToPointedEquiv F i P hPW z).1
  have hLaw := zoomToPointed_uniformLaw F i P hPW
  have hpre : preimageEvent f (pointedAgreementEvent F i P hPW T) =
      agreeingEvent T F.Q P := by
    apply Finset.ext
    intro z
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      pointedAgreementEvent]
    constructor
    · rintro ⟨z', hzz', hagree⟩
      have hz' : z' = z := by
        apply (zoomToPointedEquiv F i P hPW).injective
        apply Subtype.ext
        exact hzz'
      simpa [hz'] using hagree
    · intro hagree
      exact ⟨z, rfl, hagree⟩
  calc
    eventMass (componentLaw F.regularIncidence i)
        (pointedAgreementEvent F i P hPW T) =
        eventMass (pushforward f (uniformLaw (Zoom F.Q P)))
          (pointedAgreementEvent F i P hPW T) := by rw [hLaw]
    _ = eventMass (uniformLaw (Zoom F.Q P))
          (preimageEvent f (pointedAgreementEvent F i P hPW T)) :=
            eventMass_pushforward f _ _
    _ = eventMass (uniformLaw (Zoom F.Q P)) (agreeingEvent T F.Q P) := by
          rw [hpre]

/-- The retained adapter is a definition of the primitive terminal/final-index
data, not an independently stored family.  This keeps all scalar gates used
by its sampler definitionally tied to the produced terminal. -/
noncomputable def outputSelectedFamily
    {Aof budget totalHMin : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget totalHMin)
    (Lsrc m D a0 : Nat)
    (hsel : selector totalHMin Lsrc = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock Lsrc m)))
    (Q0 : Grass (retained draw) a0)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock Lsrc m))
    (had_gap : a0 < 2 * hBlock Lsrc m)
    (c : Nat) (hc : c ≤ budget m)
    (T : PhaseATerminal (fun U : PositiveBucketIndex P c => U.1) Q0 c
      (Fintype.card (PositiveBucketIndex P c))
      (phaseARoot (Fintype.card (PositiveBucketIndex P c)) c))
    (J : Finset T.Index)
    (C : AdviceComplement
      (PhaseAGeometry.QE (fun U : PositiveBucketIndex P c => U.1)
        Q0 T.toPhaseAGeometry))
    (WJ : {j : T.Index // j ∈ J} → Submodule (ZMod 2) T.E)
    (WJ_eq : ∀ j, WJ j =
      PhaseAGeometry.family (fun U : PositiveBucketIndex P c => U.1)
        Q0 T.toPhaseAGeometry j.1)
    (arity_generic : GenericUpTo
      (ActualMZ24MaximalGenericSubfamily.carrierFamily
        (PhaseAGeometry.family (fun U : PositiveBucketIndex P c => U.1)
          Q0 T.toPhaseAGeometry) J)
      (tD D) T.r) :
    EnlargedPointedFamily (V := retained draw)
      (I := {j : T.Index // j ∈ J}) := by
  classical
  let W0 : PositiveBucketIndex P c → Submodule (ZMod 2) (retained draw) :=
    fun U => U.1
  have hcodimW : ∀ U : PositiveBucketIndex P c,
      ActualMaximalPairLadder.codim (W0 U) = c := by
    intro U
    exact (Finset.mem_filter.mp U.2).2
  have hQW : ∀ U : PositiveBucketIndex P c, Q0.val ≤ W0 U := by
    intro U
    exact (positiveBucketRootPair P c U).hQW
  have hWJeq : WJ = ActualMZ24MaximalGenericSubfamily.carrierFamily
      (PhaseAGeometry.family W0 Q0 T.toPhaseAGeometry) J := by
    funext j
    exact WJ_eq j
  have hWJgeneric : GenericUpTo WJ (tD D) T.r := by
    rw [hWJeq]
    exact arity_generic
  have hWJinj : Function.Injective WJ := by
    intro i j hij
    apply Subtype.ext
    exact PhaseATerminal.family_injective W0 Q0 T
      ((WJ_eq i).symm.trans (hij.trans (WJ_eq j)))
  exact selectedRetainedEnlargedPointedFamily H Lsrc m hsel draw
    T.E a0 T.r c (tD D)
    (PhaseAGeometry.QE W0 Q0 T.toPhaseAGeometry) C WJ
    (PhaseATerminal.finrank_eq_sub_add W0 Q0 T hcodimW)
    (Nat.le_of_lt had_gap) hc T.residual_pos
    (PhaseAGeometry.r_le_c W0 Q0 T.toPhaseAGeometry)
    (two_le_tD D) (by
      intro j
      rw [WJ_eq j]
      exact PhaseAGeometry.QE_le_family W0 Q0 T.toPhaseAGeometry hQW j.1)
    hWJinj hWJgeneric

/-! The producer result keeps all four carrier counts distinct.  Its terminal
and final carriers are dependent on the actual selected subspaces; no bucket,
terminal, complement, arity family, or sampling law is accepted as input. -/

structure RetainedGenericExtractionOutput
    {Aof budget totalHMin : Nat → Nat}
    (H : DominatingSamplingCutoff Aof budget totalHMin)
    (Lsrc m D a0 : Nat)
    (hsel : selector totalHMin Lsrc = (m : WithBot Nat))
    (draw : Draw (blocks (Aof m) (hBlock Lsrc m)))
    (Q0 : Grass (retained draw) a0)
    (T0 : (L : Grass (retained draw) (2 * hBlock Lsrc m)) →
      Module.Dual (ZMod 2) L.val)
    {K : Type*} [Fintype K]
    (P : K → DecodedPair Q0 (2 * hBlock Lsrc m)) (beta : Rat)
    (hPinj : Function.Injective P)
    (had_gap : a0 < 2 * hBlock Lsrc m)
    (hagr : ∀ i, beta ≤ agreement T0 Q0 (P i)) where
  c : Nat
  c_pos : 1 ≤ c
  c_le_budget : c ≤ budget m
  B : Finset (Submodule (ZMod 2) (retained draw))
  B_eq : B = codimSubspaceBucket P c
  bucket_index_card : Fintype.card (PositiveBucketIndex P c) = B.card
  bucket_lower : 2 ^ inputExponent D (budget m) (hBlock Lsrc m) < B.card
  T : PhaseATerminal (fun U : PositiveBucketIndex P c => U.1) Q0 c
      (Fintype.card (PositiveBucketIndex P c))
      (phaseARoot (Fintype.card (PositiveBucketIndex P c)) c)
  terminal_root : IsPhaseARoot (Fintype.card (PositiveBucketIndex P c)) c
      (phaseARoot (Fintype.card (PositiveBucketIndex P c)) c)
  terminal_card : (Fintype.card (PositiveBucketIndex P c)) ≤
      phaseABudget c * T.C.card ^ (c + 1)
  J : Finset T.Index
  J_nonempty : J.Nonempty
  J_subset : J ⊆ Finset.univ
  arity_generic : GenericUpTo
      (ActualMZ24MaximalGenericSubfamily.carrierFamily
        (PhaseAGeometry.family
          (fun U : PositiveBucketIndex P c => U.1) Q0 T.toPhaseAGeometry) J)
      (tD D) T.r
  fixed_ambient_card : Fintype.card (PositiveBucketIndex P c) ≤
      2 ^ (3 * c * genericityPower D c) * J.card ^ genericityPower D c
  final_index_card : Fintype.card {j : T.Index // j ∈ J} = J.card
  C : AdviceComplement (PhaseAGeometry.QE
      (fun U : PositiveBucketIndex P c => U.1) Q0 T.toPhaseAGeometry)
  QE_map_recovery : (PhaseAGeometry.QE
      (fun U : PositiveBucketIndex P c => U.1) Q0 T.toPhaseAGeometry).val.map
        T.E.subtype = Q0.val
  WJ : {j : T.Index // j ∈ J} → Submodule (ZMod 2) T.E
  WJ_eq : ∀ j, WJ j = PhaseAGeometry.family
      (fun U : PositiveBucketIndex P c => U.1) Q0 T.toPhaseAGeometry j.1
  sampling :
    letI : Nonempty {j : T.Index // j ∈ J} := by
      apply Fintype.card_pos_iff.mp
      simpa using Finset.card_pos.mpr J_nonempty
    let F := outputSelectedFamily H Lsrc m D a0 hsel draw Q0 P
      had_gap c c_le_budget T J C WJ WJ_eq arity_generic
    letI : Nonempty F.pointedCarrier := F.pointed_nonempty
    SourceSamplingBounds F
  final_E1 : 2 ^ geometricOutputExponent D c (hBlock Lsrc m) < J.card

namespace RetainedGenericExtractionOutput

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

noncomputable def selectedFamily : EnlargedPointedFamily
    (V := retained draw) (I := {j : O.T.Index // j ∈ O.J}) :=
  outputSelectedFamily H Lsrc m D a0 hsel draw Q0 P had_gap O.c
    O.c_le_budget O.T O.J O.C O.WJ O.WJ_eq O.arity_generic

abbrev FinalIndex := {j : O.T.Index // j ∈ O.J}

def bucketIndex (j : FinalIndex (O := O)) : PositiveBucketIndex P O.c := j.1.1

def representative (j : FinalIndex (O := O)) : K :=
  positiveBucketRepresentative P O.c (bucketIndex (O := O) (j := j))

def rootPair (j : FinalIndex (O := O)) : DecodedPair Q0 (2 * hBlock Lsrc m) :=
  positiveBucketRootPair P O.c (bucketIndex (O := O) (j := j))

theorem rootPair_eq_representative (j : FinalIndex (O := O)) :
    rootPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j =
      P (representative H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) :=
  positiveBucketRootPair_eq_representative P O.c
    (bucketIndex (O := O) (j := j))

def localPair (j : FinalIndex (O := O)) :
    DecodedPair
      (PhaseAGeometry.QE (fun U : PositiveBucketIndex P O.c => U.1)
        Q0 O.T.toPhaseAGeometry)
      (2 * hBlock Lsrc m) :=
  localDecodedPair O.T.E Q0 (rootPair H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)
    O.T.advice_le
    (by
      rw [rootPair, positiveBucketRootPair_W]
      exact O.T.member_le j.1.1 j.1.2)

theorem localPair_W_eq (j : FinalIndex (O := O)) :
    (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j).W =
      O.WJ j := by
  rw [O.WJ_eq j]
  apply Submodule.ext
  intro x
  rfl

/-- Transport the canonical terminal-local pair into the exact query type of
the selected retained adapter. -/
def adapterLocalPair (j : FinalIndex (O := O)) :
    DecodedPair (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (2 * (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O).h) :=
  localPair H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP had_gap hagr O j

theorem adapterLocalPair_W_eq (j : FinalIndex (O := O)) :
    (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j).W =
      (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O).W j := by
  change (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP had_gap hagr O j).W = O.WJ j
  exact localPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta
    hP had_gap hagr O j

theorem adapterZoom_nonempty (j : FinalIndex (O := O)) :
    Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) := by
  exact zoom_nonempty_of_component
    (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O) j
    (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)
    (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)

/-- The per-index local Zoom law is the actual selected adapter component law.
No common functional or common event is asserted across indices. -/
theorem adapterComponentLaw (j : FinalIndex (O := O)) :
    letI : Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) :=
      adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j
    pushforward (fun z : Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j) =>
          (zoomToPointedEquiv
            (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
              hP had_gap hagr O) j
            (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
              hP had_gap hagr O j)
            (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta
              hP had_gap hagr O j) z).1)
        (uniformLaw (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O).Q
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j))) = componentLaw
              (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
                hP had_gap hagr O).regularIncidence j := by
  letI : Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) :=
    adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j
  exact zoomToPointed_uniformLaw
    (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O) j
    (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)
    (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)

/-- The agreement event remains selected by the original representative at
this index, and its mass is exactly the component-law mass. -/
def adapterTable : (L : Grass
    (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O).E
    (2 * (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).h)) →
    Module.Dual (ZMod 2) L.val :=
  restrictedTable O.T.E T0

theorem adapterAgreementEventMass (j : FinalIndex (O := O)) :
    letI : Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) :=
      adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j
    eventMass (componentLaw
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
            hP had_gap hagr O)) =
      eventMass (uniformLaw (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O).Q
        (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O j)))
        (agreeingEvent (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O)
          (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O).Q
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j)) := by
  letI : Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) :=
    adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j
  exact zoomAgreement_component_eventMass
    (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O) j
    (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)
    (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j)
    (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O)

theorem localAgreement_eq_source (j : FinalIndex (O := O)) :
    agreement T0 Q0
        (rootPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) =
      agreement
        (restrictedTable O.T.E T0)
        (PhaseAGeometry.QE (fun U : PositiveBucketIndex P O.c => U.1)
          Q0 O.T.toPhaseAGeometry)
        (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) := by
  exact agreement_restrict_eq O.T.E Q0 T0
    (rootPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
    O.T.advice_le
    (by
      rw [rootPair, positiveBucketRootPair_W]
      exact O.T.member_le j.1.1 j.1.2)

theorem localAgreement_ge (j : FinalIndex (O := O)) :
    beta ≤ agreement
      (restrictedTable O.T.E T0)
      (PhaseAGeometry.QE (fun U : PositiveBucketIndex P O.c => U.1)
        Q0 O.T.toPhaseAGeometry)
      (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) := by
  calc
    beta ≤ agreement T0 Q0
        (rootPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) :=
          positiveBucketRootPair_agreement T0 P O.c beta hagr
            (bucketIndex (O := O) (j := j))
    _ = agreement (restrictedTable O.T.E T0)
        (PhaseAGeometry.QE (fun U : PositiveBucketIndex P O.c => U.1)
          Q0 O.T.toPhaseAGeometry)
        (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) :=
          localAgreement_eq_source H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j

/-- The actual per-index retained-adapter event inherits the source agreement
lower bound.  The event remains indexed by `j`; this makes no assertion about
a common event or a mixture over the final carrier. -/
theorem adapterAgreementEventMass_ge (j : FinalIndex (O := O)) :
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
            hP had_gap hagr O)) := by
  letI : Nonempty (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O).Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j)) :=
    adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr O j
  calc
    beta ≤ agreement
        (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O)
        (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O).Q
        (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O j) := by
      change beta ≤ agreement (restrictedTable O.T.E T0)
        (PhaseAGeometry.QE (fun U : PositiveBucketIndex P O.c => U.1)
          Q0 O.T.toPhaseAGeometry)
        (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O j)
      exact localAgreement_ge H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j
    _ = eventMass
        (uniformLaw (Zoom (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O).Q
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j)))
        (agreeingEvent
          (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O)
          (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O).Q
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j)) :=
      agreement_eq_uniform_eventMass
        (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O)
        (selectedFamily H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O).Q
        (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O j)
        (adapterZoom_nonempty H Lsrc m D a0 hsel draw Q0 T0 P beta
          hP had_gap hagr O j)
    _ = eventMass (componentLaw
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
      (adapterAgreementEventMass H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j).symm

theorem complementAgreement_ge (j : FinalIndex (O := O)) :
    beta ≤ agreement
      (complementTable (restrictedTable O.T.E T0) O.C
        (Nat.le_of_lt had_gap) (by omega))
      (bottomGrass O.C.A)
      (complementPair O.C
        (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)) := by
  calc
    beta ≤ agreement (restrictedTable O.T.E T0)
        (PhaseAGeometry.QE (fun U : PositiveBucketIndex P O.c => U.1)
          Q0 O.T.toPhaseAGeometry)
        (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) :=
          localAgreement_ge H Lsrc m D a0 hsel draw Q0 T0 P beta
            hP had_gap hagr O j
    _ ≤ agreement
        (complementTable (restrictedTable O.T.E T0) O.C
          (Nat.le_of_lt had_gap) (by omega))
        (bottomGrass O.C.A)
        (complementPair O.C
          (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)) :=
          complement_agreement_le (restrictedTable O.T.E T0) O.C
            (localPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
            (Nat.le_of_lt had_gap) (by omega)

end RetainedGenericExtractionOutput

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

/-- The actual retained producer: codimension is selected from the proved
noncircular distinct-subspace threshold, Phase A sees only that W-index, and
Phase B closes full arity in the fixed terminal ambient. -/
noncomputable def retainedGenericExtraction
    (hP : Function.Injective P)
    (hD : 0 < D) (had_gap : a0 < 2 * hBlock Lsrc m)
    (hlarge : ∀ i, 10 * (2 * hBlock Lsrc m) ≤
      Module.finrank (ZMod 2) (P i).W)
    (hbeta : 0 < beta)
    (hthreshold : 4 / (2 : Rat) ^ (2 * hBlock Lsrc m - a0) < beta)
    (hagr : ∀ i, beta ≤ agreement T0 Q0 (P i))
    (hcodim : ∀ i, codim (P i).W ≤ budget m)
    (hforce : (16 : Rat) *
      (1 + (budget m : Rat) * (2 : Rat) ^
        inputExponent D (budget m) (hBlock Lsrc m)) <
      beta ^ 2 * (Fintype.card K : Rat)) :
    RetainedGenericExtractionOutput H Lsrc m D a0 hsel draw Q0 T0 P beta
      hP had_gap hagr := by
  classical
  let h0 := hBlock Lsrc m
  let d0 := 2 * h0
  let rCap := budget m
  let EinCap := inputExponent D rCap h0
  have hgate := selector_retained_height_gates H hsel draw
  have hbudgetlt := hgate.2.1
  have hh0 : 0 < h0 := by omega
  have had : a0 ≤ d0 := by omega
  have hthresholdExists :=
    noncircular_bucket_threshold T0 P hP
      beta rCap EinCap had had_gap hlarge hbeta hthreshold hagr hcodim hforce
  let c := Classical.choose hthresholdExists
  have hthresholdSpec := Classical.choose_spec hthresholdExists
  obtain ⟨hcpos, hcr, hbucket⟩ := hthresholdSpec
  let B : Finset (Submodule (ZMod 2) (retained draw)) := codimSubspaceBucket P c
  let IB := PositiveBucketIndex P c
  have hcardIB : Fintype.card IB = B.card := by
    simp [IB, B, PositiveBucketIndex]
  have hIBpos : 0 < Fintype.card IB := by
    rw [hcardIB]
    exact Nat.lt_of_lt_of_le (by positivity) (le_of_lt hbucket)
  letI : Nonempty IB := (Fintype.card_pos_iff.mp hIBpos)
  let W0 : IB → Submodule (ZMod 2) (retained draw) := fun U => U.1
  have hQW : ∀ U, Q0.val ≤ W0 U := by
    intro U
    exact (positiveBucketRootPair P c U).hQW
  have hinj : Function.Injective W0 := by
    intro U U' h
    exact Subtype.ext h
  have hcodimW : ∀ U, codim (W0 U) = c := by
    intro U
    exact (Finset.mem_filter.mp U.2).2
  let Tterm := phaseATerminalProducerOfCard W0 Q0 hQW hcodimW hinj hcpos
  have hroot : IsPhaseARoot (Fintype.card IB) c
      (phaseARoot (Fintype.card IB) c) := phaseARoot_spec _ _
  have hseed := PhaseATerminal.phaseA_seed_univ W0 Q0 Tterm hroot
  have htermpos := Tterm.residual_pos
  have hrc := PhaseAGeometry.r_le_c W0 Q0 Tterm.toPhaseAGeometry
  let WT : Tterm.Index → Submodule (ZMod 2) Tterm.E :=
    PhaseAGeometry.family W0 Q0 Tterm.toPhaseAGeometry
  have hTgeneric := PhaseATerminal.genericOn_univ W0 Q0 Tterm
  have hTne := PhaseATerminal.universe_nonempty W0 Q0 Tterm
  have hclosure := fixedAmbient_tD_closure_subtype WT
    (Finset.univ : Finset Tterm.Index) D c Tterm.r (Fintype.card IB)
    htermpos hrc hTne hTgeneric hseed
  let J := arityCarrier WT (Finset.univ : Finset Tterm.Index) Tterm.r (tD D - 2)
  have hJsub : J ⊆ Finset.univ := by
    exact (arityCarrier_subset_initial WT Finset.univ Tterm.r (tD D - 2))
  have hJne : J.Nonempty := by
    simpa [J] using hclosure.2.1
  have hJgeneric : GenericUpTo
      (ActualMZ24MaximalGenericSubfamily.carrierFamily WT J) (tD D) Tterm.r := by
    simpa [J] using hclosure.2.2.1
  have hJbound : Fintype.card IB ≤
      2 ^ (3 * c * genericityPower D c) * J.card ^ genericityPower D c := by
    simpa [J] using hclosure.2.2.2
  let IJ := {j : Tterm.Index // j ∈ J}
  have hcardIJ : Fintype.card IJ = J.card := by
    simpa only [IJ, Fintype.card_coe]
  have hIJne : Nonempty IJ := by
    apply Fintype.card_pos_iff.mp
    rw [hcardIJ]
    exact Finset.card_pos.mpr hJne
  let WJ : IJ → Submodule (ZMod 2) Tterm.E := fun j => WT j.1
  let Ccomp : AdviceComplement (PhaseAGeometry.QE W0 Q0 Tterm.toPhaseAGeometry) :=
    ⟨Classical.choose (Submodule.exists_isCompl
        (PhaseAGeometry.QE W0 Q0 Tterm.toPhaseAGeometry).val),
      Classical.choose_spec (Submodule.exists_isCompl
        (PhaseAGeometry.QE W0 Q0 Tterm.toPhaseAGeometry).val)⟩
  have hWJeq : ∀ j, WJ j = PhaseAGeometry.family W0 Q0 Tterm.toPhaseAGeometry j.1 :=
    fun j => rfl
  let F := outputSelectedFamily H Lsrc m D a0 hsel draw Q0 P had_gap
    c hcr Tterm J Ccomp WJ hWJeq hJgeneric
  letI : Nonempty IJ := hIJne
  let sample := actual_enlarged_pointed_sampling F
  have hp : 0 < genericityPower D c := by
    unfold genericityPower
    positivity
  have hEinMono : inputExponent D c h0 ≤ EinCap := by
    exact inputExponent_mono_codim hcr
  have hendpoint := E1_weighted_endpoint hD hcpos hh0
  have htotal : genericityPower D c *
      (geometricOutputExponent D c h0 + 3 * c) ≤ EinCap :=
    hendpoint.trans hEinMono
  have hpowle : 2 ^ (genericityPower D c *
      (geometricOutputExponent D c h0 + 3 * c)) ≤ 2 ^ EinCap :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) htotal
  have hBbound : B.card ≤ 2 ^ (3 * c * genericityPower D c) *
      J.card ^ genericityPower D c := by
    simpa [hcardIB] using hJbound
  have hprod : 2 ^ EinCap < 2 ^ (3 * c * genericityPower D c) * J.card ^
      genericityPower D c := hbucket.trans_le hBbound
  have hpowstrict : 2 ^ (genericityPower D c *
      (geometricOutputExponent D c h0 + 3 * c)) <
      2 ^ (3 * c * genericityPower D c) * J.card ^ genericityPower D c :=
    hpowle.trans_lt hprod
  have hcancel : 2 ^ (genericityPower D c * geometricOutputExponent D c h0) <
      J.card ^ genericityPower D c := by
    have hfactor : 2 ^ (3 * c * genericityPower D c) *
        2 ^ (genericityPower D c * geometricOutputExponent D c h0) =
        2 ^ (genericityPower D c *
          (geometricOutputExponent D c h0 + 3 * c)) := by
      rw [← pow_add]
      congr 1 <;> ring
    apply (Nat.mul_lt_mul_left
      (by positivity : 0 < 2 ^ (3 * c * genericityPower D c))).mp
    rw [hfactor]
    exact hpowstrict
  have hE1 : 2 ^ geometricOutputExponent D c h0 < J.card := by
    by_contra hnot
    have hle : J.card ≤ 2 ^ geometricOutputExponent D c h0 := Nat.le_of_not_gt hnot
    have hpow : J.card ^ genericityPower D c ≤
        (2 ^ geometricOutputExponent D c h0) ^ genericityPower D c := by
      gcongr
    have hpow' : J.card ^ genericityPower D c ≤
        2 ^ (geometricOutputExponent D c h0 * genericityPower D c) := by
      simpa only [pow_mul] using hpow
    have hcancel' : 2 ^ (geometricOutputExponent D c h0 *
        genericityPower D c) < J.card ^ genericityPower D c := by
      simpa [Nat.mul_comm] using hcancel
    omega
  refine {
    c := c
    c_pos := hcpos
    c_le_budget := hcr
    B := B
    B_eq := rfl
    bucket_index_card := hcardIB
    bucket_lower := by simpa [EinCap, rCap, B] using hbucket
    T := Tterm
    terminal_root := hroot
    terminal_card := by
      simpa only [Finset.card_univ, PhaseATerminal.index_card] using hseed
    J := J
    J_nonempty := hJne
    J_subset := hJsub
    arity_generic := hJgeneric
    fixed_ambient_card := hJbound
    final_index_card := hcardIJ
    C := Ccomp
    QE_map_recovery := PhaseAGeometry.QE_map_recovery W0 Q0 Tterm.toPhaseAGeometry
    WJ := WJ
    WJ_eq := hWJeq
    sampling := sample
    final_E1 := hE1 }
