import PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant
import PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
import PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
import PvNP.RealizableHardness.ActualTaggedFixedUDensityForce

/-! An explicit full-domain carrier for the tagged composed verifier. The
eligible ordered U law has its exact uniform-set marginal upstream. Each
sample records the stored transverse center and k full queried domains;
the final independent uniform draw is over full vertices in their cliques. -/

namespace PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedVertexPhysicalLaw
open PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
open PvNP.RealizableHardness.ActualTaggedFixedUDensityForce

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

abbrev TaggedDomainSample (J t h k : Nat) :=
  Σ U : TaggedGoodU I copies J,
    Σ K : TaggedCenterOver I copies t U,
      Fin k → TaggedDomainDraw I copies (questionOf I copies U K) h

noncomputable instance taggedDomainSampleFintype (J t h k : Nat) :
    Fintype (TaggedDomainSample I copies J t h k) := by
  unfold TaggedDomainSample
  infer_instance

def sampleToDomains {J t h k : Nat}
    (p : TaggedSample I copies J t h k) :
    TaggedDomainSample I copies J t h k :=
  ⟨p.1, p.2.1, fun i => taggedLeaf_domainDraw I copies
    (questionOf I copies p.1 p.2.1) (p.2.2 i)⟩

noncomputable def domainsToSample {J t h k : Nat}
    (p : TaggedDomainSample I copies J t h k) :
    TaggedSample I copies J t h k :=
  ⟨p.1, p.2.1, fun i => taggedDomainDraw_leaf I copies
    (questionOf I copies p.1 p.2.1) (p.2.2 i)⟩

theorem sampleToDomains_domainsToSample {J t h k : Nat}
    (p : TaggedDomainSample I copies J t h k) :
    sampleToDomains I copies (domainsToSample I copies p) = p := by
  rcases p with ⟨U, K, Ds⟩
  dsimp [sampleToDomains, domainsToSample]
  have hfun : (fun i => taggedLeaf_domainDraw I copies
      (questionOf I copies U K)
      (taggedDomainDraw_leaf I copies (questionOf I copies U K) (Ds i))) = Ds := by
    funext i
    exact taggedLeaf_domainDraw_leaf I copies (questionOf I copies U K) (Ds i)
  rw [hfun]

private def leafTupleFiberEquiv {J t h k : Nat}
    (q : ActualTaggedFixedCenterGeometry.TaggedQuestionCenter I copies J t)
    (Ds : Fin k → TaggedDomainDraw I copies q h) :
    {Ls : Fin k → TaggedLeafOver I copies h q //
      (fun i => taggedLeaf_domainDraw I copies q (Ls i)) = Ds} ≃
      ((i : Fin k) → taggedLeafDomainFiber I copies q (Ds i)) where
  toFun Ls := fun i => ⟨Ls.1 i, congrFun Ls.2 i⟩
  invFun Ls := ⟨fun i => (Ls i).1, funext (fun i => (Ls i).2)⟩
  left_inv Ls := by apply Subtype.ext; funext i; rfl
  right_inv Ls := by funext i; apply Subtype.ext; rfl

private theorem leafTupleFiber_card {J t h k : Nat}
    (q : ActualTaggedFixedCenterGeometry.TaggedQuestionCenter I copies J t)
    (Ds : Fin k → TaggedDomainDraw I copies q h) :
    Fintype.card {Ls : Fin k → TaggedLeafOver I copies h q //
      (fun i => taggedLeaf_domainDraw I copies q (Ls i)) = Ds} =
        (2 ^ (J * (2 * h - t))) ^ k := by
  classical
  rw [Fintype.card_congr (leafTupleFiberEquiv I copies q Ds), Fintype.card_pi]
  simp_rw [taggedLeafDomainFiber_card I copies q]
  simp

private theorem leafOver_card_by_domains {J t h : Nat}
    (q : ActualTaggedFixedCenterGeometry.TaggedQuestionCenter I copies J t) :
    Fintype.card (TaggedLeafOver I copies h q) =
      Fintype.card (TaggedDomainDraw I copies q h) *
        2 ^ (J * (2 * h - t)) := by
  classical
  calc
    Fintype.card (TaggedLeafOver I copies h q) =
        Fintype.card (Σ D : TaggedDomainDraw I copies q h,
          taggedLeafDomainFiber I copies q D) :=
      (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (taggedLeaf_domainDraw I copies q))).symm
    _ = ∑ D : TaggedDomainDraw I copies q h,
          Fintype.card (taggedLeafDomainFiber I copies q D) := Fintype.card_sigma
    _ = ∑ _D : TaggedDomainDraw I copies q h,
          2 ^ (J * (2 * h - t)) := by
      apply Finset.sum_congr rfl
      intro D _
      exact taggedLeafDomainFiber_card I copies q D
    _ = _ := by simp [Finset.sum_const]

/-- Conditional independent uniform leaf presentations push forward to
independent uniform full-domain vertices at the same stored q.K. -/
theorem uniform_leafTuple_pushforward {J t h k : Nat}
    (q : ActualTaggedFixedCenterGeometry.TaggedQuestionCenter I copies J t)
    (ht : t ≤ 2 * h) (hh : h ≤ J) :
    letI : Nonempty (TaggedDomainDraw I copies q h) :=
      taggedDomainDraw_nonempty I copies q ht hh
    letI : Nonempty (TaggedLeafOver I copies h q) :=
      ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
    pushforward (fun Ls : Fin k → TaggedLeafOver I copies h q =>
        fun i => taggedLeaf_domainDraw I copies q (Ls i))
      (uniformLaw (Fin k → TaggedLeafOver I copies h q)) =
      uniformLaw (Fin k → TaggedDomainDraw I copies q h) := by
  classical
  letI : Nonempty (TaggedDomainDraw I copies q h) :=
    taggedDomainDraw_nonempty I copies q ht hh
  letI : Nonempty (TaggedLeafOver I copies h q) :=
    ⟨taggedDomainDraw_leaf I copies q (Classical.choice inferInstance)⟩
  apply FiniteLaw.ext
  intro Ds
  rw [pushforward_apply, uniformLaw_apply]
  simp_rw [uniformLaw_apply (Fin k → TaggedLeafOver I copies h q)]
  have hsum :
      (∑ Ls : Fin k → TaggedLeafOver I copies h q,
        if (fun i => taggedLeaf_domainDraw I copies q (Ls i)) = Ds then
          (1 : ℚ) / Fintype.card (Fin k → TaggedLeafOver I copies h q) else 0) =
      (Fintype.card {Ls : Fin k → TaggedLeafOver I copies h q //
        (fun i => taggedLeaf_domainDraw I copies q (Ls i)) = Ds} : ℚ) /
          Fintype.card (Fin k → TaggedLeafOver I copies h q) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul]
    rw [← Fintype.card_subtype
      (fun Ls : Fin k → TaggedLeafOver I copies h q =>
        (fun i => taggedLeaf_domainDraw I copies q (Ls i)) = Ds)]
    simp [div_eq_mul_inv]
  rw [hsum, leafTupleFiber_card I copies q Ds,
    Fintype.card_pi_const, Fintype.card_pi_const,
    leafOver_card_by_domains I copies q, mul_pow]
  have hc : (((2 ^ (J * (2 * h - t))) ^ k : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero _ (pow_ne_zero _ (by decide : (2 : Nat) ≠ 0)))
  have hd : ((Fintype.card (TaggedDomainDraw I copies q h) ^ k : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero _ (Fintype.card_ne_zero :
      Fintype.card (TaggedDomainDraw I copies q h) ≠ 0))
  field_simp
  simp [Nat.cast_mul, mul_comm]

/-- The physical event on full queried domains and independently uniform
full-vertex representatives, with the same fixed raw tables and stored K. -/
noncomputable def composedDomainScore {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (p : TaggedDomainSample I copies J t h k) : ℚ :=
  let z := sampledStar I copies (domainsToSample I copies p)
  uniformMean (TaggedIndependentVertexChoice I copies z.leaves)
    (fun v => if taggedVertexPhysicalAccepts I copies C T z v then 1 else 0)

/-- A full-domain probability law. Its conditional uniformity is proved by
the constant-fiber domain theorem, rather than postulated at the event. -/
noncomputable def composedDomainLaw {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (TaggedDomainSample I copies J t h k) :=
  pushforward (sampleToDomains I copies)
    (taggedSampleLaw I copies hcenter hleaf)

/-- The domain-carrier law is exactly the manuscript's conditional sampler:
uniform eligible U, uniform stored transverse K, then independent uniform
full domains containing that K. This is a pointwise atom identity, not merely
an equality of supports. -/
theorem composedDomainLaw_mass {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (p : TaggedDomainSample I copies J t h k) :
    (composedDomainLaw I copies hcenter hleaf).mass p =
      (uniformLaw (TaggedGoodU I copies J)).mass p.1 *
        (uniformLaw (TaggedCenterOver I copies t p.1)).mass p.2.1 *
        ((1 : ℚ) / Fintype.card (Fin k → TaggedDomainDraw I copies
          (questionOf I copies p.1 p.2.1) h)) := by
  classical
  unfold TaggedDomainSample at p
  rcases p with ⟨U, K, Ds⟩
  let q := questionOf I copies U K
  letI : Nonempty (TaggedDomainDraw I copies q h) :=
    taggedDomainDraw_nonempty I copies q ht hh
  have htuple := congrArg (fun μ : FiniteLaw (Fin k → TaggedDomainDraw I copies q h) =>
      μ.mass Ds) (uniform_leafTuple_pushforward I copies q ht hh (k := k))
  let d : TaggedDomainSample I copies J t h k := ⟨U, K, Ds⟩
  calc
    (composedDomainLaw I copies hcenter hleaf).mass
        d =
      (uniformLaw (TaggedGoodU I copies J)).mass U *
        (uniformLaw (TaggedCenterOver I copies t U)).mass K *
        (pushforward (fun Ls : Fin k → TaggedLeafOver I copies h q =>
            fun i => taggedLeaf_domainDraw I copies q (Ls i))
          (uniformLaw (Fin k → TaggedLeafOver I copies h q))).mass Ds := by
      unfold composedDomainLaw
      rw [pushforward_apply]
      simp only [TaggedSample, Fintype.sum_sigma]
      rw [Fintype.sum_eq_single U]
      · rw [Fintype.sum_eq_single K]
        · simp [sampleToDomains, taggedSampleLaw, d, q, uniformLaw_apply,
            pushforward_apply]
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        · intro K' hne
          apply Finset.sum_eq_zero
          intro Ls _
          have hf : sampleToDomains I copies
              (⟨U, K', Ls⟩ : TaggedSample I copies J t h k) ≠ d := by
            intro he
            simp only [sampleToDomains, d, Sigma.mk.inj_iff, heq_eq_eq,
              true_and] at he
            exact hne he.1
          simp [hf]
      · intro U' hne
        apply Finset.sum_eq_zero
        intro K' _
        apply Finset.sum_eq_zero
        intro Ls _
        have hf : sampleToDomains I copies
            (⟨U', K', Ls⟩ : TaggedSample I copies J t h k) ≠ d := by
          intro he
          exact hne (congrArg (fun x : TaggedDomainSample I copies J t h k => x.1) he)
        simp [hf]
    _ = _ := by rw [htuple, uniformLaw_apply]; simp [d, q, uniformLaw_apply]

noncomputable def composedTaggedScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) : ℚ :=
  ∑ p : TaggedDomainSample I copies J t h k,
    (composedDomainLaw I copies hcenter hleaf).mass p *
      composedDomainScore I copies C T p

private theorem sum_pushforward_pullback
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (μ : FiniteLaw A) (g : B → ℚ) :
    (∑ a, μ.mass a * g (f a)) =
      ∑ b, (pushforward f μ).mass b * g b := by
  classical
  change (∑ a, μ.mass a * g (f a)) =
    ∑ b, (∑ a, if f a = b then μ.mass a else 0) * g b
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

private theorem uniformMean_fintype_independent
    (α : Type*) [Nonempty α] (F G : Fintype α) (f : α → ℚ) :
    @uniformMean α F inferInstance f = @uniformMean α G inferInstance f := by
  classical
  have heq : F.elems = G.elems := by
    ext x
    exact ⟨fun _ => G.complete x, fun _ => F.complete x⟩
  change F.elems.sum f / F.elems.card = G.elems.sum f / G.elems.card
  rw [heq]

theorem physicalMean_eq_composedDomainScore {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (p : TaggedSample I copies J t h k) :
    uniformMean (TaggedIndependentChoice I copies
      (sampledStar I copies p).leaves)
      (fun r => if taggedPhysicalAccepts I copies C T
        (sampledStar I copies p) r then 1 else 0) =
      composedDomainScore I copies C T (sampleToDomains I copies p) := by
  let z := sampledStar I copies p
  let p' := domainsToSample I copies (sampleToDomains I copies p)
  let vs : Fin k → TaggedPresentedLeaf I copies J h :=
    (sampledStar I copies p').leaves
  have hrows : ∀ i, (vs i).U = z.q.U := by
    intro i
    exact (p'.2.2 i).2.1
  have hcenter : ∀ i, z.q.K ≤ (vs i).domain I copies := by
    intro i
    exact le_trans (p'.2.2 i).2.2 le_sup_left
  have hD : ∀ i, (z.leaves i).domain I copies = (vs i).domain I copies := by
    intro i
    change (p.2.2 i).1.domain I copies =
      (taggedDomainDraw_leaf I copies (questionOf I copies p.1 p.2.1)
        (taggedLeaf_domainDraw I copies
          (questionOf I copies p.1 p.2.1) (p.2.2 i))).1.domain I copies
    simpa only [taggedLeaf_domainDraw] using
      (taggedDomainDraw_leaf_domain I copies
        (questionOf I copies p.1 p.2.1)
        (taggedLeaf_domainDraw I copies
          (questionOf I copies p.1 p.2.1) (p.2.2 i))).symm
  calc
    _ = uniformMean (TaggedIndependentChoice I copies vs)
        (fun r => if taggedPhysicalAccepts I copies C T
          (sampledStar I copies p') r then 1 else 0) := by
      exact taggedPhysicalMean_replaceTargetLeaves I copies C T z vs
        hrows hcenter hD
    _ = composedDomainScore I copies C T (sampleToDomains I copies p) := by
      exact taggedPhysicalMean_eq_vertexMean I copies C T
        (sampledStar I copies p')

/-- The source full-domain/vertex-representative score equals the actual
ordered tagged physical score for every fixed raw leaf table and center
table. No representative is chosen after seeing the draw. -/
theorem composedTaggedScore_eq_orderedPhysicalMass {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    composedTaggedScore I copies (k := k) hcenter hleaf C T =
      taggedPhysicalMass I copies
        (orderedStarLaw I copies J (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T := by
  rw [orderedStarLaw_eq_taggedSampleLaw I copies hcenter hleaf]
  unfold composedTaggedScore composedDomainLaw taggedPhysicalMass
  rw [← sum_pushforward_pullback (sampleToDomains I copies)
    (taggedSampleLaw I copies hcenter hleaf)
    (composedDomainScore I copies C T)]
  apply Finset.sum_congr rfl
  intro p _
  rw [← physicalMean_eq_composedDomainScore I copies C T p]
  congr 1
  exact uniformMean_fintype_independent
    (TaggedIndependentChoice I copies (sampledStar I copies p).leaves) _ _ _

/-- An actual fixed-table composed score above the manuscript threshold
supplies the physical half-threshold required by the canonical selection and
MZ-density force theorem. The same pre-draw C and T occur on both sides. -/
theorem composedScore_gt_forces_MZ_threshold_U
    {J t h k p q : Nat} [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (ξ ρ : ℚ) (hξ : ξ = 4000 * ρ)
    (hp : (p : ℚ) = 2 * (1 - 1000 * ρ) * h * m)
    (hq : (q : ℚ) = 2 * (1 - ξ) * h * m)
    (hlarge : (6 : ℚ) ≤ 6000 * ρ * h * m)
    (hpJ : p ≤ J)
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (hscore : (1 / 2 : ℚ) ^ q <
      composedTaggedScore I copies (k := k) hcenter hleaf C T) :
    ∃ T' : TaggedLeafTable I copies,
      8 * (1 / 2 : ℚ) ^ p ≤
        ∑ U : TaggedGoodU I copies J,
          (uniformLaw (TaggedGoodU I copies J)).mass U *
            (if 8 * (1 / 2 : ℚ) ^ p ≤
              conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U
             then (1 : ℚ) else 0) := by
  have hphysical : (1 / 2 : ℚ) ^ (q + 1) ≤
      taggedPhysicalMass I copies
        (orderedStarLaw I copies J (t := t) (h := h) (k := k)
          hcenter hleaf).mass
        (sampledStar I copies (J := J) (t := t) (h := h) (k := k)) C T := by
    rw [← composedTaggedScore_eq_orderedPhysicalMass I copies
      hcenter hleaf C T]
    have hnonneg : 0 ≤ (1 / 2 : ℚ) ^ q := by positivity
    rw [pow_add]
    norm_num
    linarith
  exact ordered_manuscript_half_value_forces_MZ_threshold_U I copies
    hcenter hleaf ht hh hexp hk ξ ρ hξ hp hq hlarge hpJ C T hphysical

/-- The source's left assignment is a fixed legal label on every full
vertex. The right assignment is already typed as a linear center table. -/
def TaggedLegalRawTable {J h : Nat}
    (T : TaggedRawVertexTable I copies J h) : Prop :=
  ∀ P : TaggedPresentedLeaf I copies J h,
    P.respectsRows I copies (T (taggedCanonicalVertex I copies P))

abbrev TaggedLegalLeafAssignment (J h : Nat) :=
  {T : TaggedRawVertexTable I copies J h // TaggedLegalRawTable I copies T}

/-- For a legal source assignment, the physical verifier's raw-label
validity gate is automatic; its remaining test is exactly the transported
center comparison on the stored `q.K`. -/
theorem taggedPhysicalAccepts_iff_independentAccepts_of_legal
    {J t h k : Nat} (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (hlegal : TaggedLegalRawTable I copies T)
    (z : TaggedPresentedStar I copies J t h k)
    (r : TaggedIndependentChoice I copies z.leaves) :
    taggedPhysicalAccepts I copies C T z r ↔
      taggedIndependentAccepts I copies C T z r := by
  constructor
  · exact And.right
  · intro htest
    exact ⟨fun i => hlegal (r i).1, htest⟩

noncomputable instance rawTableFintype {J h : Nat} :
    Fintype (TaggedRawVertexTable I copies J h) := by
  letI : Finite (Submodule (ZMod 2) (TaggedAmbient I copies)) :=
    Finite.of_injective (fun D => (D : Set (TaggedAmbient I copies)))
      SetLike.coe_injective
  exact Fintype.ofFinite _

noncomputable instance centerTableFintype :
    Fintype (TaggedCenterTable I copies) := by
  letI : Finite (Submodule (ZMod 2) (TaggedAmbient I copies)) :=
    Finite.of_injective (fun D => (D : Set (TaggedAmbient I copies)))
      SetLike.coe_injective
  exact Fintype.ofFinite _

/-- A finite maximum over fixed pre-draw table pairs. An invalid left table
is assigned score zero, so any value above a positive threshold has a legal
source assignment witness. -/
noncomputable def composedLegalValue {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) : ℚ := by
  classical
  let F : TaggedCenterTable I copies × TaggedRawVertexTable I copies J h → ℚ :=
    fun CT => if TaggedLegalRawTable I copies CT.2 then
      composedTaggedScore I copies (k := k) hcenter hleaf CT.1 CT.2 else 0
  exact (Finset.univ : Finset
    (TaggedCenterTable I copies × TaggedRawVertexTable I copies J h)).sup'
      (by simp) F

theorem composedLegalValue_gt_forces_MZ_threshold_U
    {J t h k p q : Nat} [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (ξ ρ : ℚ) (hξ : ξ = 4000 * ρ)
    (hp : (p : ℚ) = 2 * (1 - 1000 * ρ) * h * m)
    (hq : (q : ℚ) = 2 * (1 - ξ) * h * m)
    (hlarge : (6 : ℚ) ≤ 6000 * ρ * h * m)
    (hpJ : p ≤ J)
    (hvalue : (1 / 2 : ℚ) ^ q <
      composedLegalValue I copies (k := k) hcenter hleaf) :
    ∃ (C : TaggedCenterTable I copies)
      (T : TaggedLegalLeafAssignment I copies J h)
      (T' : TaggedLeafTable I copies),
      8 * (1 / 2 : ℚ) ^ p ≤
        ∑ U : TaggedGoodU I copies J,
          (uniformLaw (TaggedGoodU I copies J)).mass U *
            (if 8 * (1 / 2 : ℚ) ^ p ≤
              conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U
             then (1 : ℚ) else 0) := by
  classical
  unfold composedLegalValue at hvalue
  rw [Finset.lt_sup'_iff] at hvalue
  obtain ⟨CT, _, hCT⟩ := hvalue
  have hlegal : TaggedLegalRawTable I copies CT.2 := by
    by_contra hbad
    simp [hbad] at hCT
    have hpos : 0 ≤ (2 : ℚ) ^ q := by positivity
    linarith
  have hscore : (1 / 2 : ℚ) ^ q <
      composedTaggedScore I copies (k := k) hcenter hleaf CT.1 CT.2 := by
    simpa [hlegal] using hCT
  obtain ⟨T', hT'⟩ := composedScore_gt_forces_MZ_threshold_U I copies
    hcenter hleaf ht hh hexp hk ξ ρ hξ hp hq hlarge hpJ CT.1 CT.2 hscore
  exact ⟨CT.1, ⟨CT.2, hlegal⟩, T', hT'⟩

end
end PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
