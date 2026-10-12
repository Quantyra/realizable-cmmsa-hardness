import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
import PvNP.RealizableHardness.ActualQuestionMassBridge
import PvNP.RealizableHardness.ActualTaggedQuestionRetainedMass
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm

/-! The eligible ordered tagged row sampler has the same uniform `TaggedGoodU`
marginal used by the fixed-table tagged star law. Each eligible set has exactly
`J!` orderings. This is the first-marginal identity only; center and leaf
nonemptiness and collision estimates are handled separately. -/

namespace PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualQuestionMassBridge
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedPresentedSelection

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies J : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

def TaggedOrderedGood :=
  {u : Fin J → TaggedRow I copies //
    GoodOrderedQuestion (taggedSource I copies).support u}

instance : Fintype (TaggedOrderedGood I copies J) := by
  classical
  letI : Finite (TaggedOrderedGood I copies J) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def orderedToGoodU (u : TaggedOrderedGood I copies J) :
    TaggedGoodU I copies J := by
  refine ⟨Finset.univ.image u.1, u.2.2, ?_⟩
  simpa using Finset.card_image_of_injective
    (Finset.univ : Finset (Fin J)) u.2.1

def TaggedOrderedFiber (U : TaggedGoodU I copies J) :=
  {u : TaggedOrderedGood I copies J // orderedToGoodU I copies J u = U}

instance (U : TaggedGoodU I copies J) :
    Fintype (TaggedOrderedFiber I copies J U) := by
  classical
  letI : Finite (TaggedOrderedFiber I copies J U) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def canonicalOrder (U : TaggedGoodU I copies J) : Fin J ≃ U.1 :=
  (Finset.equivFinOfCardEq U.2.2).symm

def permutationToFiber (U : TaggedGoodU I copies J)
    (p : Equiv.Perm (Fin J)) : TaggedOrderedFiber I copies J U := by
  let e := canonicalOrder I copies J U
  let u : Fin J → TaggedRow I copies := fun i => (e (p i)).1
  have hinj : Function.Injective u := by
    intro i j hij
    have h : e (p i) = e (p j) := Subtype.ext hij
    exact p.injective (e.injective h)
  have himage : Finset.univ.image u = U.1 := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact (e (p i)).2
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine Finset.mem_image.mpr ⟨p.symm i, Finset.mem_univ _, ?_⟩
      simp [u, hi]
  let good : TaggedOrderedGood I copies J :=
    ⟨u, hinj, by simpa [himage] using U.2.1⟩
  exact ⟨good, Subtype.ext himage⟩

def fiberToPermutation (U : TaggedGoodU I copies J)
    (u : TaggedOrderedFiber I copies J U) : Equiv.Perm (Fin J) := by
  have himage : Finset.univ.image u.1.1 = U.1 :=
    congrArg Subtype.val u.2
  let f : Fin J → U.1 := fun i => ⟨u.1.1 i, by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact u.1.2.1 (congrArg Subtype.val h)
    · intro x
      have hx : x.1 ∈ Finset.univ.image u.1.1 := by
        rw [himage]
        exact x.2
      rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  exact (Equiv.ofBijective f hf).trans (canonicalOrder I copies J U).symm

def fiberPermEquiv (U : TaggedGoodU I copies J) :
    TaggedOrderedFiber I copies J U ≃ Equiv.Perm (Fin J) where
  toFun := fiberToPermutation I copies J U
  invFun := permutationToFiber I copies J U
  left_inv := by
    intro u
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [permutationToFiber, fiberToPermutation, Equiv.trans_apply,
      Equiv.ofBijective]
  right_inv := by
    intro p
    apply Equiv.ext
    intro i
    exact (canonicalOrder I copies J U).symm_apply_apply _

theorem orderedFiber_card (U : TaggedGoodU I copies J) :
    Fintype.card (TaggedOrderedFiber I copies J U) = J.factorial := by
  rw [Fintype.card_congr (fiberPermEquiv I copies J U), Fintype.card_perm,
    Fintype.card_fin]

def orderedFiberSigmaEquiv :
    (Σ U : TaggedGoodU I copies J, TaggedOrderedFiber I copies J U) ≃
      TaggedOrderedGood I copies J where
  toFun p := p.2.1
  invFun u := ⟨orderedToGoodU I copies J u, ⟨u, rfl⟩⟩
  left_inv := by
    intro p
    rcases p with ⟨U, u, hu⟩
    cases hu
    rfl
  right_inv := by intro u; rfl

theorem orderedGood_card [Nonempty (TaggedGoodU I copies J)] :
    Fintype.card (TaggedOrderedGood I copies J) =
      Fintype.card (TaggedGoodU I copies J) * J.factorial := by
  rw [← Fintype.card_congr (orderedFiberSigmaEquiv I copies J)]
  simp only [Fintype.card_sigma]
  simp_rw [orderedFiber_card I copies J]
  simp [Finset.sum_const, mul_comm]

instance orderedGoodNonempty [Nonempty (TaggedGoodU I copies J)] :
    Nonempty (TaggedOrderedGood I copies J) := by
  obtain ⟨U⟩ := ‹Nonempty (TaggedGoodU I copies J)›
  exact ⟨(permutationToFiber I copies J U 1).1⟩

def orderedGoodLaw [Nonempty (TaggedGoodU I copies J)] :
    FiniteLaw (TaggedOrderedGood I copies J) := uniformLaw _

/-- The uniform eligible ordered tagged row tuple has exactly the uniform
`TaggedGoodU` marginal used by `taggedSampleLaw`. -/
theorem orderedGood_pushforward [Nonempty (TaggedGoodU I copies J)] :
    pushforward (orderedToGoodU I copies J) (orderedGoodLaw I copies J) =
      uniformLaw (TaggedGoodU I copies J) := by
  classical
  apply FiniteLaw.ext
  intro U
  rw [pushforward_apply, uniformLaw_apply]
  simp only [orderedGoodLaw, uniformLaw_apply]
  have hsum :
      (∑ u : TaggedOrderedGood I copies J,
        if orderedToGoodU I copies J u = U then
          (1 : ℚ) / Fintype.card (TaggedOrderedGood I copies J) else 0) =
        (Fintype.card (TaggedOrderedFiber I copies J U) : ℚ) /
          Fintype.card (TaggedOrderedGood I copies J) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [← Fintype.card_subtype
      (fun u : TaggedOrderedGood I copies J => orderedToGoodU I copies J u = U)]
    have hcard : Fintype.card
        {u : TaggedOrderedGood I copies J // orderedToGoodU I copies J u = U} =
        Fintype.card (TaggedOrderedFiber I copies J U) :=
      Fintype.card_congr (Equiv.refl _)
    rw [hcard]
    simp [div_eq_mul_inv]
  rw [hsum, orderedFiber_card I copies J U, orderedGood_card I copies J]
  have hJ : (J.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero J
  have hU : (Fintype.card (TaggedGoodU I copies J) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (TaggedGoodU I copies J) ≠ 0)
  field_simp
  simp [Nat.cast_mul, mul_comm]

/-- The manuscript padding choice supplies a genuine eligible tagged row set.
It removes the first nonemptiness premise from the tagged star law. -/
theorem taggedGoodU_nonempty_of_padding (T : Nat)
    (hT : 4 ≤ T) (hm : 0 < m) :
    Nonempty (TaggedGoodU I (ActualQuestionMassBridge.actualPaddingCopies J T) J) := by
  classical
  let copies := ActualQuestionMassBridge.actualPaddingCopies J T
  have hpos := ActualQuestionMassBridge.actual_tagged_good_card_pos I J T hT hm
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have hgood : GoodOrderedQuestion (taggedSource I copies).support u := by
    exact (Finset.mem_filter.mp hu).2
  exact ⟨orderedToGoodU I copies J ⟨u, hgood⟩⟩

/-- The complete dependent ordered tagged draw. The final independent
representative draw remains the uniform fiber average in `taggedPhysicalMass`. -/
def TaggedOrderedSample (t h k : Nat) :=
  Σ u : TaggedOrderedGood I copies J,
    Σ K : TaggedCenterOver I copies t (orderedToGoodU I copies J u),
      Fin k → TaggedLeafOver I copies h
        (questionOf I copies (orderedToGoodU I copies J u) K)

noncomputable instance taggedOrderedSampleFintype (t h k : Nat) :
    Fintype (TaggedOrderedSample I copies J t h k) := by
  unfold TaggedOrderedSample
  infer_instance

def orderedSampleToSample {t h k : Nat}
    (p : TaggedOrderedSample I copies J t h k) :
    TaggedSample I copies J t h k :=
  ⟨orderedToGoodU I copies J p.1, p.2.1, p.2.2⟩

/-- Uniform ordered eligible rows, then uniform transverse K in the U-fiber,
then independent uniform transverse rank-2h leaves containing K. -/
def taggedOrderedSampleLaw {t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
        (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (TaggedOrderedSample I copies J t h k) := by
  classical
  let muU := orderedGoodLaw I copies J
  let muK (u : TaggedOrderedGood I copies J) :
      FiniteLaw (TaggedCenterOver I copies t (orderedToGoodU I copies J u)) :=
    @uniformLaw _ inferInstance (hcenter (orderedToGoodU I copies J u))
  let muL (u : TaggedOrderedGood I copies J)
      (K : TaggedCenterOver I copies t (orderedToGoodU I copies J u)) :
      FiniteLaw (Fin k → TaggedLeafOver I copies h
        (questionOf I copies (orderedToGoodU I copies J u) K)) :=
    @uniformLaw _ inferInstance
      ⟨fun _ => Classical.choice (hleaf (orderedToGoodU I copies J u) K)⟩
  refine
    { mass := fun p => muU.mass p.1 * (muK p.1).mass p.2.1 *
        (muL p.1 p.2.1).mass p.2.2
      nonneg := ?_
      normalized := ?_ }
  · intro p
    exact mul_nonneg (mul_nonneg (muU.nonneg p.1)
      ((muK p.1).nonneg p.2.1)) ((muL p.1 p.2.1).nonneg p.2.2)
  · have hsum :
        (∑ u : TaggedOrderedGood I copies J,
          ∑ K : TaggedCenterOver I copies t (orderedToGoodU I copies J u),
            ∑ Ls : Fin k → TaggedLeafOver I copies h
                (questionOf I copies (orderedToGoodU I copies J u) K),
              muU.mass u * (muK u).mass K * (muL u K).mass Ls) = 1 := by
      calc
        _ = ∑ u : TaggedOrderedGood I copies J,
              ∑ K : TaggedCenterOver I copies t (orderedToGoodU I copies J u),
                muU.mass u * (muK u).mass K := by
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro K _
              calc
                _ = (muU.mass u * (muK u).mass K) *
                      (∑ Ls : Fin k → TaggedLeafOver I copies h
                        (questionOf I copies (orderedToGoodU I copies J u) K),
                        (muL u K).mass Ls) := by rw [Finset.mul_sum]
                _ = _ := by rw [(muL u K).normalized, mul_one]
        _ = ∑ u : TaggedOrderedGood I copies J, muU.mass u := by
              apply Finset.sum_congr rfl
              intro u _
              calc
                _ = muU.mass u *
                      (∑ K : TaggedCenterOver I copies t
                        (orderedToGoodU I copies J u), (muK u).mass K) := by
                        rw [Finset.mul_sum]
                _ = _ := by rw [(muK u).normalized, mul_one]
        _ = 1 := muU.normalized
    simpa only [TaggedOrderedSample, Fintype.sum_sigma] using hsum

/-- Exact pushforward of the full ordered U/K/leaf experiment to the
`TaggedSample` carrier used by the arbitrary-table inequality. -/
def orderedStarLaw {t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
        (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (TaggedSample I copies J t h k) :=
  pushforward (orderedSampleToSample I copies J)
    (taggedOrderedSampleLaw I copies J hcenter hleaf)

/-- The representative-selection comparison for the complete ordered
tagged U/K/leaf law and arbitrary fixed raw/center tables. -/
theorem ordered_sample_exists_selected
    {t h k : Nat} [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
        (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    ∃ s : TaggedRepresentativeChoice I copies J h,
      taggedPhysicalMass I copies
        (orderedStarLaw I copies J (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T ≤
        taggedSelectedMass I copies
          (orderedStarLaw I copies J (t := t) (h := h) (k := k)
            hcenter hleaf).mass
          (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T s +
        taggedClassCollisionMass I copies
          (orderedStarLaw I copies J (t := t) (h := h) (k := k)
            hcenter hleaf).mass
          (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) := by
  exact tagged_exists_selected_mass_ge_physical_sub_collision I copies
    (orderedStarLaw I copies J (t := t) (h := h) (k := k)
      hcenter hleaf).mass
    (orderedStarLaw I copies J (t := t) (h := h) (k := k)
      hcenter hleaf).nonneg
    (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T

end
end PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
