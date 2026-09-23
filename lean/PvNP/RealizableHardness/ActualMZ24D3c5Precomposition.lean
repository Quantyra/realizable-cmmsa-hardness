import PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction

/-! Bounded D3c5 arithmetic and same-complement indexed-event transport.
This module makes no common-mixture or final D3c5 claim. -/

namespace PvNP.RealizableHardness.ActualMZ24D3c5Precomposition

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24RetainedSamplingProducer
open PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
open PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.TripleRestrictionRank
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualMZ24GenericSubfamilyRepresentative
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction
open PvNP.RealizableHardness.ActualMZ24RetainedGenericExtraction.RetainedGenericExtractionOutput
open PvNP.RealizableHardness.ActualMZ24PointedSamplingJoin
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {Aof budget totalHMin : Nat → Nat}
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable {Lsrc m D a0 : Nat}
variable {K : Type*} [Fintype K]
variable {H : DominatingSamplingCutoff Aof budget totalHMin}
variable {hsel : selector totalHMin Lsrc = (m : WithBot Nat)}
variable {draw : Draw (blocks (Aof m) (hBlock Lsrc m))}
variable {Q0 : Grass (retained draw) a0}
variable {T0 : (L : Grass (retained draw) (2 * hBlock Lsrc m)) → Module.Dual (ZMod 2) L.val}
variable {P : K → DecodedPair Q0 (2 * hBlock Lsrc m)} {beta : Rat}
variable {hP : Function.Injective P} {had_gap : a0 < 2 * hBlock Lsrc m}
variable {hagr : ∀ i, beta ≤ agreement T0 Q0 (P i)}
variable (O : RetainedGenericExtractionOutput H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr)

def Ecap (D R c h : Nat) : Nat := 100 * R^2 * h * D^5 / (c + 1) - 3*c

def L5 (c h r' D : Nat) : Nat :=
  10*c*h + (1000*r'*D^5+1) + 3 + 1000*D^5

def L6 (c h r' D a0 : Nat) : Nat := L5 c h r' D + a0

theorem Ecap_addback (D R c h : Nat)
    (hguard : 3*c ≤ 100*R^2*h*D^5/(c+1)) :
    Ecap D R c h + 3*c = 100*R^2*h*D^5/(c+1) :=
  Nat.sub_add_cancel hguard

theorem L6_addback (c h r' D a0 : Nat) :
    L6 c h r' D a0 = L5 c h r' D + a0 := rfl

/-- The retained gate forces positive height: c is positive and lies below
the selector budget, which is strictly below hBlock. -/
theorem height_pos (O : RetainedGenericExtractionOutput H Lsrc m D a0 hsel draw
    Q0 T0 P beta hP had_gap hagr) (hD : 0 < D) : 0 < hBlock Lsrc m := by
  have gates := ActualMZ24RetainedSamplingProducer.selector_retained_height_gates
    H hsel draw
  have hc : 1 ≤ O.c := O.c_pos
  have hcb : O.c ≤ budget m := O.c_le_budget
  omega

/-- The exponent count is derived from this output's cap bucket and fixed
ambient arity bound. -/
theorem cap_sensitive_J_count (hD : 0 < D) :
    2 ^ Ecap D (budget m) O.c (hBlock Lsrc m) < O.J.card := by
  have hh : 0 < hBlock Lsrc m := height_pos O hD
  let F := Nat.factorial (tD D - 1)
  let k := genericityPower D O.c
  have hF : 0 < F := Nat.factorial_pos _
  have hk : 0 < k := by dsimp [k, genericityPower]; positivity
  have hbucket := O.bucket_lower
  have hambient := O.fixed_ambient_card
  have hbase :
      k * (Ecap D (budget m) O.c (hBlock Lsrc m) + 3*O.c) ≤
        inputExponent D (budget m) (hBlock Lsrc m) := by
    let A := 100 * budget m^2 * hBlock Lsrc m * D^5
    have hdiv := Nat.div_mul_le_self A (O.c+1)
    have hcpos : 0 < O.c := Nat.succ_le_iff.mp O.c_pos
    have hc2 : O.c + 1 ≤ 2 * O.c := by omega
    have hsmall : 3 * O.c * (O.c+1) ≤ 6 * O.c^2 := by nlinarith
    have hsq : O.c^2 ≤ budget m^2 := Nat.pow_le_pow_left O.c_le_budget 2
    have hhDpos : 0 < hBlock Lsrc m * D^5 :=
      Nat.mul_pos hh (Nat.pow_pos hD)
    have hhd : 1 ≤ hBlock Lsrc m * D^5 := by omega
    have hprod : budget m^2 ≤ budget m^2 * (hBlock Lsrc m * D^5) := by
      simpa using Nat.mul_le_mul_left (budget m^2) hhd
    have hlarge : 6 * O.c^2 ≤ A := by
      dsimp [A]
      calc
        6 * O.c^2 ≤ 6 * budget m^2 := Nat.mul_le_mul_left 6 hsq
        _ ≤ 6 * (budget m^2 * (hBlock Lsrc m * D^5)) :=
          Nat.mul_le_mul_left 6 hprod
        _ ≤ 100 * (budget m^2 * (hBlock Lsrc m * D^5)) := by
          have h610 : 6 ≤ 100 := by norm_num
          exact Nat.mul_le_mul_right (budget m^2 * (hBlock Lsrc m * D^5)) h610
        _ = 100 * budget m^2 * hBlock Lsrc m * D^5 := by ring
    have hfloor : 3*O.c ≤ A / (O.c+1) := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < O.c+1)).2
      exact hsmall.trans hlarge
    have hadd : (A / (O.c+1) - 3*O.c) + 3*O.c = A / (O.c+1) :=
      Nat.sub_add_cancel hfloor
    calc
      k * (Ecap D (budget m) O.c (hBlock Lsrc m) + 3*O.c) =
          ((A / (O.c+1)) * (O.c+1)) * F := by
        simp [k, F, genericityPower, Ecap, A, hadd]
        ring
      _ ≤ A * F := Nat.mul_le_mul_right F hdiv
      _ = inputExponent D (budget m) (hBlock Lsrc m) := by
        simp [inputExponent, F, A]
        ring
  have hpowle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbase
  rw [← O.bucket_index_card] at hbucket
  have hprod := hbucket.trans_le hambient
  have hstrict := hpowle.trans_lt hprod
  have hfactor :
      2 ^ (3*O.c*k) * (2 ^ Ecap D (budget m) O.c (hBlock Lsrc m))^k =
        2 ^ (k * (Ecap D (budget m) O.c (hBlock Lsrc m) + 3*O.c)) := by
    rw [← pow_mul, ← pow_add]
    congr 1 <;> ring
  have hcancel : (2 ^ Ecap D (budget m) O.c (hBlock Lsrc m))^k < O.J.card^k := by
    apply (Nat.mul_lt_mul_left (by positivity : 0 < 2^(3*O.c*k))).mp
    rw [hfactor]
    simpa [mul_comm, mul_left_comm, mul_assoc, k, genericityPower] using hstrict
  by_contra hnot
  have hle : O.J.card ≤ 2 ^ Ecap D (budget m) O.c (hBlock Lsrc m) := Nat.le_of_not_gt hnot
  have hp : O.J.card^k ≤ (2 ^ Ecap D (budget m) O.c (hBlock Lsrc m))^k :=
    Nat.pow_le_pow_left hle k
  exact (not_lt_of_ge hp hcancel).elim

/-- Guarded prospective ledger; the reserve is an explicit numerical premise. -/
theorem guarded_loss_ledger (hD : 0 < D) (hR : 2 ≤ budget m)
    (hc : 1 ≤ O.c) (hcr : O.c ≤ budget m)
    (hr' : 1 ≤ O.T.r) (hr'c : O.T.r ≤ O.c)
    (hreserve : 3*budget m + 1000*(budget m+1)*D^5 + a0 + 5 ≤
      10*hBlock Lsrc m) :
    50*O.c*hBlock Lsrc m*D^5 + L6 O.c (hBlock Lsrc m) O.T.r D a0 ≤
      Ecap D (budget m) O.c (hBlock Lsrc m) := by
  let X := D^5
  have hXpos : 0 < X := by dsimp [X]; exact Nat.pow_pos hD
  have hX : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hXpos)
  have hR : 2 ≤ budget m := hR
  have hcr : O.c ≤ budget m := hcr
  have hr'c : O.T.r ≤ O.c := hr'c
  have htail :
      1000*(O.T.r+1)*X + a0 + 4 + 3*O.c ≤ 10*hBlock Lsrc m := by
    have hrplus : O.T.r+1 ≤ budget m+1 := by omega
    have hmul := Nat.mul_le_mul_right X hrplus
    calc
      1000*(O.T.r+1)*X + a0 + 4 + 3*O.c ≤
          1000*(budget m+1)*X + a0 + 5 + 3*budget m := by nlinarith
      _ ≤ 10*hBlock Lsrc m := by
        simpa [X, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hreserve
  have hcore :
      (5*O.c*X + O.c + 1)*(O.c+1) ≤ 10*budget m^2*X := by
    by_cases hcOne : O.c = 1
    · rw [hcOne]
      have hR2 : 4 ≤ budget m^2 := Nat.pow_le_pow_left hR 2
      have hR2X := Nat.mul_le_mul_right X hR2
      nlinarith
    · have hcTwo : 2 ≤ O.c := by omega
      have hpoly : (O.c+1)^2 ≤ 5*O.c*(O.c-1) := by
        let q := O.c-2
        have hdecomp : O.c = q+2 := by dsimp [q]; omega
        have hminus : O.c-1 = q+1 := by dsimp [q]; omega
        rw [hminus, hdecomp]
        nlinarith
      have hpolyX : (O.c+1)^2 ≤ 5*O.c*(O.c-1)*X := by
        calc
          (O.c+1)^2 ≤ 5*O.c*(O.c-1) := hpoly
          _ ≤ 5*O.c*(O.c-1)*X := Nat.le_mul_of_pos_right _ hXpos
      have hsq : O.c^2 ≤ budget m^2 := Nat.pow_le_pow_left hcr 2
      have hsub : O.c-1+1 = O.c := Nat.sub_add_cancel (by omega)
      calc
        (5*O.c*X + O.c + 1)*(O.c+1) =
            5*O.c^2*X + 5*O.c*X + (O.c+1)^2 := by ring
        _ ≤ 5*O.c^2*X + 5*O.c*X + 5*O.c*(O.c-1)*X := by
          exact Nat.add_le_add_left hpolyX _
        _ = 5*O.c^2*X + 5*O.c*((O.c-1)+1)*X := by ring
        _ = 10*O.c^2*X := by rw [hsub]; ring
        _ ≤ 10*budget m^2*X := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
            Nat.mul_le_mul_right (10*X) hsq
  have hfull :
      50*O.c*hBlock Lsrc m*X + L6 O.c (hBlock Lsrc m) O.T.r D a0 + 3*O.c ≤
        10*hBlock Lsrc m*(5*O.c*X + O.c + 1) := by
    unfold L6 L5
    dsimp [X] at htail ⊢
    nlinarith [htail]
  have hquot :
      50*O.c*hBlock Lsrc m*X + L6 O.c (hBlock Lsrc m) O.T.r D a0 + 3*O.c ≤
        (100*budget m^2*hBlock Lsrc m*X)/(O.c+1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < O.c+1)).2
    calc
      (50*O.c*hBlock Lsrc m*X + L6 O.c (hBlock Lsrc m) O.T.r D a0 + 3*O.c)*(O.c+1) ≤
          (10*hBlock Lsrc m*(5*O.c*X + O.c + 1))*(O.c+1) :=
        Nat.mul_le_mul_right (O.c+1) hfull
      _ ≤ (10*hBlock Lsrc m)*(10*budget m^2*X) := by
        simpa [Nat.mul_assoc] using
          Nat.mul_le_mul_left (10*hBlock Lsrc m) hcore
      _ = 100*budget m^2*hBlock Lsrc m*X := by ring
  unfold Ecap
  exact Nat.le_sub_of_add_le hquot

/-- The candidate-specific pointed event, transported to the actual
complement carrier with the one retained advice complement. -/
def complementCandidateEvent (j : O.FinalIndex) :
    Finset (O.selectedFamily.complementCarrier) :=
  Finset.image O.selectedFamily.pointed_carrier_equiv
    (pointedAgreementEvent O.selectedFamily j
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O))

/-- The transported candidate pair preserves the selected component's W
through the same retained advice complement. -/
theorem complementCandidatePair_W_eq (j : O.FinalIndex) :
    (complementPair O.C
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)).W =
      complementSubspace O.C (O.selectedFamily.W j) := by
  change complementSubspace O.C
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j).W =
    complementSubspace O.C (O.selectedFamily.W j)
  rw [adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j]

private theorem preimageEvent_image_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Finset α) :
    preimageEvent e (A.image e) = A := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    simp only [preimageEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hyx : y = x := e.injective hxy
    simpa [hyx] using hy
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

private theorem pointedMap_eq_complementZoom (j : O.FinalIndex)
    (z : Zoom O.selectedFamily.Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)) :
    (O.selectedFamily.pointed_carrier_equiv
        (zoomToPointedEquiv O.selectedFamily j
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
          (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) z).1).1 =
      ((complementZoomEquiv O.C
        (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
        (Nat.le_of_lt had_gap) z).1).1 := by
  rfl

/-- Carrier-level agreement event on the same retained complement.  It is
indexed by the candidate and consists of the query spaces arising from that
candidate's complement Zooms. -/
def complementAgreementCarrierEvent (j : O.FinalIndex) :
    Finset O.selectedFamily.complementCarrier :=
    Finset.univ.filter (fun X => ∃ z : Zoom O.selectedFamily.Q
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j),
    (complementZoomEquiv O.C
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (Nat.le_of_lt had_gap) z).1.1 = X.1 ∧
    (complementZoomEquiv O.C
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (Nat.le_of_lt had_gap) z) ∈ agreeingEvent
      (complementTable (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O)
        O.C (Nat.le_of_lt had_gap)
        (Nat.add_sub_of_le O.selectedFamily.advice_le_query))
      (bottomGrass O.C.A)
      (complementPair O.C
        (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)))

/-- Every image point from the candidate agreement event lies in the
complement-agreement event; the pointwise agreement transfer is exactly the
accepted `agreesOn_complement` theorem. -/
theorem complementCandidateEvent_subset_agreement (j : O.FinalIndex) :
    complementCandidateEvent O j ⊆ complementAgreementCarrierEvent O j := by
  intro X hX
  rcases Finset.mem_image.mp hX with ⟨q, hq, hqX⟩
  rcases Finset.mem_filter.mp hq with ⟨_, hz⟩
  rcases hz with ⟨z, hzq, hagree⟩
  have hb := Nat.add_sub_of_le O.selectedFamily.advice_le_query
  have hagree' : AgreesOn
      (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O)
      z.1 z.2.2 := by
    simpa only [agreeingEvent, Finset.mem_filter, Finset.mem_univ, true_and] using hagree
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ X, z, ?_, ?_⟩
  · change (O.selectedFamily.pointed_carrier_equiv
      (zoomToPointedEquiv O.selectedFamily j
        (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
        (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) z).1).1 = X.1
    have hmap : O.selectedFamily.pointed_carrier_equiv
        (zoomToPointedEquiv O.selectedFamily j
          (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
          (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j) z).1 = X :=
      (congrArg O.selectedFamily.pointed_carrier_equiv hzq).trans hqX
    exact congrArg Subtype.val hmap
  · have hcomp := agreesOn_complement
      (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O)
      O.C
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (Nat.le_of_lt had_gap) hb z hagree'
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hcomp⟩

/-- The image event keeps the same final index and its actual component law. -/
theorem complementCandidateEvent_mass_ge (j : O.FinalIndex) :
    beta ≤ eventMass
      (componentLaw
        (complementBottomRegularIncidence O.selectedFamily.C
          O.selectedFamily.W O.selectedFamily.contains
          O.selectedFamily.twoGeneric O.selectedFamily.pair_gate) j)
      (complementCandidateEvent O j) := by
  letI : Nonempty O.selectedFamily.pointedCarrier :=
    O.selectedFamily.pointed_nonempty
  letI : Nonempty O.selectedFamily.complementCarrier :=
    O.selectedFamily.complement_nonempty
  letI : Nonempty O.FinalIndex := ⟨j⟩
  let E := pointedAgreementEvent O.selectedFamily j
      (adapterLocalPair H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (adapterLocalPair_W_eq H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O j)
      (adapterTable H Lsrc m D a0 hsel draw Q0 T0 P beta hP had_gap hagr O)
  let f : O.selectedFamily.pointedCarrier ≃ O.selectedFamily.complementCarrier :=
    O.selectedFamily.pointed_carrier_equiv
  let mu := componentLaw O.selectedFamily.regularIncidence j
  let nu := componentLaw
    (complementBottomRegularIncidence O.selectedFamily.C O.selectedFamily.W
      O.selectedFamily.contains O.selectedFamily.twoGeneric O.selectedFamily.pair_gate) j
  have hLaw : pushforward f mu = nu := by
    simpa [f, mu, nu] using same_complement_component_pushforward O.selectedFamily j
  have hmass' :
      eventMass (pushforward f mu) (Finset.image f E) = eventMass mu E := by
    calc
      eventMass (pushforward f mu) (Finset.image f E) =
          eventMass mu (preimageEvent f (Finset.image f E)) :=
        eventMass_pushforward f mu _
      _ = eventMass mu E := congrArg (eventMass mu)
        (preimageEvent_image_equiv f E)
  have hmass : eventMass nu (complementCandidateEvent O j) = eventMass mu E := by
    change eventMass nu (Finset.image f E) = eventMass mu E
    rw [← hLaw]
    exact hmass'
  calc
    beta ≤ eventMass mu E := by
      simpa [mu] using adapterAgreementEventMass_ge H Lsrc m D a0 hsel draw Q0 T0 P beta
        hP had_gap hagr O j
    _ = eventMass nu (complementCandidateEvent O j) := hmass.symm

end
end PvNP.RealizableHardness.ActualMZ24D3c5Precomposition
