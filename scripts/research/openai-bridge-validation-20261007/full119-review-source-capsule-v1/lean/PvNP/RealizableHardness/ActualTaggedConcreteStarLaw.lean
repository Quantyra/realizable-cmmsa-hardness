import PvNP.RealizableHardness.ActualTaggedPresentedSelection
import PvNP.RealizableHardness.ActualFiniteLaw

/-! A finite tagged star sampler: uniform legitimate row sets, conditional
transverse centers, then independent rank-`2*h` presented leaves containing
the stored center. The representative draw is the independent uniform choice
already inside `taggedPhysicalMass`. The ordered tagged row-tuple marginal and
the manuscript's numerical nonemptiness and collision estimates still require
separate proofs. -/

namespace PvNP.RealizableHardness.ActualTaggedConcreteStarLaw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

def TaggedGoodU (J : Nat) :=
  {U : Finset (TaggedRow I copies) //
    GoodQuestion (taggedSource I copies).support U ∧ U.card = J}

instance (J : Nat) : Fintype (TaggedGoodU I copies J) := by
  letI : Finite (TaggedGoodU I copies J) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def TaggedCenterOver {J : Nat} (t : Nat) (U : TaggedGoodU I copies J) :=
  {K : Submodule (ZMod 2) (TaggedAmbient I copies) //
    K ≤ coordinateSpace (taggedSource I copies).support U.1 ∧
    Module.finrank (ZMod 2) K = t ∧
    K ⊓ equationSpan (taggedSource I copies).support U.1 = ⊥}

instance {J : Nat} (t : Nat) (U : TaggedGoodU I copies J) :
    Fintype (TaggedCenterOver I copies t U) := by
  letI : Finite (Submodule (ZMod 2) (TaggedAmbient I copies)) :=
    Finite.of_injective (fun K => (K : Set (TaggedAmbient I copies)))
      SetLike.coe_injective
  letI : Finite (TaggedCenterOver I copies t U) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def questionOf {J t : Nat} (U : TaggedGoodU I copies J)
    (K : TaggedCenterOver I copies t U) : TaggedQuestionCenter I copies J t :=
  { U := U.1
    goodU := U.2.1
    card_U := U.2.2
    K := K.1
    K_le := K.2.1
    finrank_K := K.2.2.1
    transverse := K.2.2.2 }

/-- Exactly the conditional rank-`2*h` transverse presented leaves over the
stored center. The leaves share `U`; the sampled representative is separate. -/
def TaggedLeafOver {J t : Nat} (h : Nat)
    (q : TaggedQuestionCenter I copies J t) :=
  {P : TaggedPresentedLeaf I copies J h //
    P.U = q.U ∧ q.K ≤ P.L}

instance {J t : Nat} (h : Nat) (q : TaggedQuestionCenter I copies J t) :
    Fintype (TaggedLeafOver I copies h q) := by
  letI : Finite (TaggedLeafOver I copies h q) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def TaggedSample (J t h k : Nat) :=
  Σ U : TaggedGoodU I copies J,
    Σ K : TaggedCenterOver I copies t U,
      Fin k → TaggedLeafOver I copies h (questionOf I copies U K)

noncomputable instance taggedSampleFintype (J t h k : Nat) :
    Fintype (TaggedSample I copies J t h k) := by
  unfold TaggedSample
  infer_instance

def sampledStar {J t h k : Nat} (p : TaggedSample I copies J t h k) :
    TaggedPresentedStar I copies J t h k :=
  { q := questionOf I copies p.1 p.2.1
    leaves := fun i => (p.2.2 i).1
    sameRows := fun i => (p.2.2 i).2.1
    center_le := fun i =>
      le_trans (p.2.2 i).2.2
        (le_sup_left : (p.2.2 i).1.L ≤ (p.2.2 i).1.domain I copies) }

/-- Uniform eligible tagged U, uniform K in its own transverse fiber, then
independent uniform leaves in their common conditional fiber. -/
def taggedSampleLaw {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J) (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (TaggedSample I copies J t h k) := by
  classical
  let muU := uniformLaw (TaggedGoodU I copies J)
  let muK (U : TaggedGoodU I copies J) :
      FiniteLaw (TaggedCenterOver I copies t U) :=
    @uniformLaw _ inferInstance (hcenter U)
  let muL (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U) :
      FiniteLaw (Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :=
    @uniformLaw _ inferInstance ⟨fun _ => Classical.choice (hleaf U K)⟩
  refine
    { mass := fun p => muU.mass p.1 * (muK p.1).mass p.2.1 *
        (muL p.1 p.2.1).mass p.2.2
      nonneg := ?_
      normalized := ?_ }
  · intro p
    exact mul_nonneg (mul_nonneg (muU.nonneg p.1)
      ((muK p.1).nonneg p.2.1)) ((muL p.1 p.2.1).nonneg p.2.2)
  · have hsum :
        (∑ U : TaggedGoodU I copies J,
          ∑ K : TaggedCenterOver I copies t U,
            ∑ Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K),
              muU.mass U * (muK U).mass K * (muL U K).mass Ls) = 1 := by
      calc
        _ = ∑ U : TaggedGoodU I copies J,
              ∑ K : TaggedCenterOver I copies t U,
                muU.mass U * (muK U).mass K := by
              apply Finset.sum_congr rfl
              intro U _
              apply Finset.sum_congr rfl
              intro K _
              calc
                _ = (muU.mass U * (muK U).mass K) *
                      (∑ Ls : Fin k → TaggedLeafOver I copies h
                        (questionOf I copies U K), (muL U K).mass Ls) := by
                      rw [Finset.mul_sum]
                _ = _ := by rw [(muL U K).normalized, mul_one]
        _ = ∑ U : TaggedGoodU I copies J, muU.mass U := by
              apply Finset.sum_congr rfl
              intro U _
              calc
                _ = muU.mass U *
                      (∑ K : TaggedCenterOver I copies t U, (muK U).mass K) := by
                      rw [Finset.mul_sum]
                _ = _ := by rw [(muK U).normalized, mul_one]
        _ = 1 := muU.normalized
    simpa only [TaggedSample, Fintype.sum_sigma] using hsum

/-- This normalized tagged U/K/leaf law, rather than arbitrary supplied
weights, instantiates the arbitrary-fixed-table representative comparison. -/
theorem tagged_sample_exists_selected
    {J t h k : Nat} [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J) (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    ∃ s : TaggedRepresentativeChoice I copies J h,
      taggedPhysicalMass I copies
        (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T ≤
        taggedSelectedMass I copies
          (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
            hcenter hleaf).mass
          (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T s +
        taggedClassCollisionMass I copies
          (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
            hcenter hleaf).mass
          (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) := by
  exact tagged_exists_selected_mass_ge_physical_sub_collision I copies
    (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
      hcenter hleaf).mass
    (taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
      hcenter hleaf).nonneg
    (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T

end
end PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
