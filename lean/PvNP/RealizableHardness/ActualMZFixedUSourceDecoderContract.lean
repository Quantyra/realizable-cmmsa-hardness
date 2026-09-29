import PvNP.RealizableHardness.ActualTaggedMZSideDraw
import PvNP.RealizableHardness.ActualMaximalPairLadder
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
A visibly external, fixed-first-question interface to MZ arXiv:2510.23991v1,
Theorem 4.2. The test input is the exact transverse fixed-`U` law in
`ActualTaggedMZSideDraw`, not the manuscript's changed-ambient `8S` law.
This file constructs no inhabitant of `ExternalMZFixedUSourceDecoder`.
-/

namespace PvNP.RealizableHardness.ActualMZFixedUSourceDecoderContract

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedMZSideDraw
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.GrassmannCounting
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N degree : Nat} (I : ActualOccurrenceAllocation.Instance N degree)
  (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

/-- The source's conditioned `2h`-Grassmann domain: transverse leaves
containing the advice `Q` and whose full leaf domain is contained in `W`. -/
def SourceZoom (a d : Nat)
    (Q : Grass (coordinateSpace (taggedSource I copies).support U.1) a)
    (W : Submodule (ZMod 2) (TaggedAmbient I copies)) :=
  {L : Grass (coordinateSpace (taggedSource I copies).support U.1) d //
    (L.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype) ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥ ∧
    Q.val ≤ L.val ∧
    (L.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype) ⊔
      equationSpan (taggedSource I copies).support U.1 ≤ W}

instance sourceZoomFintype (a d : Nat)
    (Q : Grass (coordinateSpace (taggedSource I copies).support U.1) a)
    (W : Submodule (ZMod 2) (TaggedAmbient I copies)) :
    Fintype (SourceZoom I copies U a d Q W) := by
  unfold SourceZoom
  infer_instance

/-- The full side-conditioned vertex corresponding to one transverse leaf. -/
def sourceLeafDomain {d : Nat}
    (L : Grass (coordinateSpace (taggedSource I copies).support U.1) d) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  L.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype ⊔
    equationSpan (taggedSource I copies).support U.1

/-- The table agrees with the decoder on the *full* domain `L+H_U`. -/
def SourceAgrees {a d : Nat}
    (Q : Grass (coordinateSpace (taggedSource I copies).support U.1) a)
    (W : Submodule (ZMod 2) (TaggedAmbient I copies))
    (g : Module.Dual (ZMod 2) W)
    (T : TaggedLeafTable I copies)
    (L : SourceZoom I copies U a d Q W) : Prop :=
  T (sourceLeafDomain I copies U L.1) =
    g.comp (Submodule.inclusion
      (show sourceLeafDomain I copies U L.1 ≤ W from L.2.2.2))

/-- Exact conditioned Grassmann agreement; an empty conditioned fibre has
agreement zero and cannot satisfy the positive source conclusion. -/
def sourceAgreement {a d : Nat}
    (Q : Grass (coordinateSpace (taggedSource I copies).support U.1) a)
    (W : Submodule (ZMod 2) (TaggedAmbient I copies))
    (g : Module.Dual (ZMod 2) W)
    (T : TaggedLeafTable I copies) : ℚ :=
  if Fintype.card (SourceZoom I copies U a d Q W) = 0 then 0 else
    ((Finset.univ.filter (SourceAgrees I copies U (d := d) Q W g T)).card : ℚ) /
      (Fintype.card (SourceZoom I copies U a d Q W) : ℚ)

/-- A decoded `W,g` at one fixed advice space. The equality on every copied
row is the source side condition on `H_U`. -/
def SourceDecodedAt (a d c : Nat)
    (Q : Grass (coordinateSpace (taggedSource I copies).support U.1) a)
    (T : TaggedLeafTable I copies) (C : ℝ) : Prop :=
  ∃ (W : Submodule (ZMod 2) (TaggedAmbient I copies))
      (g : Module.Dual (ZMod 2) W),
    Module.finrank (ZMod 2) (coordinateSpace (taggedSource I copies).support U.1) -
      Module.finrank (ZMod 2) W = c ∧
    W ≤ coordinateSpace (taggedSource I copies).support U.1 ∧
    Q.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype ≤ W ∧
    equationSpan (taggedSource I copies).support U.1 ≤ W ∧
    (∀ e (he : e ∈ U.1)
      (hmem : equationVector (taggedSource I copies).support e ∈ W),
      g ⟨equationVector (taggedSource I copies).support e, hmem⟩ =
        (taggedSource I copies).rhs e) ∧
    C ≤ (sourceAgreement I copies U (d := d) Q W g T : ℝ)

/-- The source table's alphabet requirement is quantified over every
transverse leaf domain, before the test draw. -/
def SourceLeafTableLegal (d : Nat) (T : TaggedLeafTable I copies) : Prop :=
  ∀ L : Grass (coordinateSpace (taggedSource I copies).support U.1) d,
    L.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥ →
    ∀ e (he : e ∈ U.1),
      T (sourceLeafDomain I copies U L)
        ⟨equationVector (taggedSource I copies).support e,
          (show equationVector (taggedSource I copies).support e ∈
            sourceLeafDomain I copies U L from
            (le_sup_right : equationSpan (taggedSource I copies).support U.1 ≤
              sourceLeafDomain I copies U L)
              (equationVector_mem_equationSpan
                (taggedSource I copies).support U.1 e he))⟩ =
        (taggedSource I copies).rhs e

/-- A representative table selected once for all classes obeys the source
side conditions at every transverse full leaf domain of this fixed `U`. -/
theorem selectedDomainTable_sourceLegal {h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h) :
    SourceLeafTableLegal I copies U (2 * h)
      (taggedSelectedDomainTable I copies T s) := by
  intro L htrans e he
  let E := coordinateSpace (taggedSource I copies).support U.1
  let P : TaggedPresentedLeaf I copies J h := {
    U := U.1
    goodU := U.2.1
    card_U := U.2.2
    L := L.val.map E.subtype
    L_le := E.map_subtype_le L.val
    finrank_L := by rw [Submodule.finrank_map_subtype_eq, L.property]
    transverse := htrans }
  have hdomain : sourceLeafDomain I copies U L = P.domain I copies := rfl
  have hvalid := taggedSelectedLeafLabel_respectsRows I copies T s P e he
  have heval := taggedSelectedDomainTable_eval I copies T s P
    (sourceLeafDomain I copies U L) hdomain
    ⟨equationVector (taggedSource I copies).support e,
      (le_sup_right : equationSpan (taggedSource I copies).support U.1 ≤
        sourceLeafDomain I copies U L)
        (equationVector_mem_equationSpan
          (taggedSource I copies).support U.1 e he)⟩
  exact heval.trans hvalid

/-- Uniform, visibly external fixed-`U` MZ Theorem 4.2 interface. The cutoff
is selected from fixed `k,ρ` before `h`, the eligible source question `U`,
  and both tables. This interface is conservatively restricted to the
  source PCP schedule `J = 2^(100*h^2)` in MZ v1, Section 5.1, equation (8);
  Theorem 4.2 itself does not state this equality. Thus this interface cannot be applied
  at the manuscript's changed `J = 2^(2^(A*h^2))`. This concerns the source
  fixed-`U` transverse test law; it supplies no changed-ambient inverse or
  robust `8S` application. Exact
real powers avoid an unwarranted `ρ²h` integrality premise. -/
structure ExternalMZFixedUSourceDecoder
    (k r : Nat) (rho : ℚ) where
  k_ge_two : 2 ≤ k
  rho_pos : 0 < rho
  rho_le_small : rho ≤ 1 / 4000
  heightCutoff : Nat
  budget : (r : ℚ) * rho = 10 * k
  decode : ∀ {N degree : Nat}
      (I : ActualOccurrenceAllocation.Instance N degree) (copies h t J : Nat),
    heightCutoff ≤ h →
    J = 2 ^ (100 * h ^ 2) →
    (t : ℚ) = 2 * (1 - rho) * h →
    ∀ (U : TaggedGoodU I copies J),
    Nonempty (SideCenter I copies U t) →
    (∀ K : SideCenter I copies U t, Nonempty (SideLeaf I copies U h K)) →
    ∀
      (C : TaggedCenterTable I copies)
      (T : TaggedLeafTable I copies),
    SourceLeafTableLegal I copies U (2 * h) T →
    (2 : ℝ) ^ (-(2 * (1 - (1000 : ℝ) * (rho : ℝ)) * h * k)) ≤
      (sideConditionalDensity I copies U t h k C T : ℝ) →
    ∃ (a c : Nat), a + c ≤ r ∧
      (2 : ℝ) ^ (-(6 * (h : ℝ) ^ 2)) ≤
        ∑ Q : Grass (coordinateSpace (taggedSource I copies).support U.1) a,
          ((1 : ℝ) / Fintype.card
            (Grass (coordinateSpace (taggedSource I copies).support U.1) a)) *
            (if SourceDecodedAt I copies U a (2 * h) c Q T
                ((2 : ℝ) ^ (-(2 * (1 - (1000 : ℝ) * (rho : ℝ) ^ 2) * h)) / 5)
              then (1 : ℝ) else 0)

end
end PvNP.RealizableHardness.ActualMZFixedUSourceDecoderContract
