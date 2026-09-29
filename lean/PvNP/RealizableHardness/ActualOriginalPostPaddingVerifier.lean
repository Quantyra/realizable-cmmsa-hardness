import PvNP.RealizableHardness.ActualTaggedVerifierValueBridge

/-! The post-padding source experiment, stated with its sampled fields rather
than by aliasing the tagged verifier sample or acceptance predicate. -/

namespace PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.Finite3LinSource
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualTaggedOrderedFullLawForce
open PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
open PvNP.RealizableHardness.ActualTaggedVerifierValueBridge
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section

variable {N m : Nat} (I : Instance N m) (copies : Nat)
local instance (I : Instance N m) : DecidableEq I.RowId := Classical.decEq _
local instance (I : Instance N m) : DecidableEq I.GlobalVar := inferInstance

/-- The copied post-padding equation system used by the source verifier. -/
def copiedSource := (Finite3LinSource.ofActual I).taggedCopy copies

structure OriginalU (J : Nat) where
  rows : Finset (Fin copies × I.RowId)
  good : GoodQuestion (copiedSource I copies).support rows
  card_rows : rows.card = J

structure OriginalK {J : Nat} (t : Nat) (U : OriginalU I copies J) where
  space : Submodule (ZMod 2) (TaggedAmbient I copies)
  inside : space ≤ coordinateSpace (copiedSource I copies).support U.rows
  dim : Module.finrank (ZMod 2) space = t
  transverse : space ⊓ equationSpan (copiedSource I copies).support U.rows = ⊥

structure OriginalLeaf {J t : Nat} (h : Nat)
    (U : OriginalU I copies J) (K : OriginalK I copies t U) where
  presented : TaggedPresentedLeaf I copies J h
  same_rows : presented.U = U.rows
  contains_center : K.space ≤ presented.L

def OriginalU.toTagged {J : Nat} (U : OriginalU I copies J) :
    TaggedGoodU I copies J :=
  ⟨U.rows, U.good, U.card_rows⟩

def OriginalK.toTagged {J t : Nat} {U : OriginalU I copies J}
    (K : OriginalK I copies t U) :
    TaggedCenterOver I copies t (U.toTagged I copies) :=
  ⟨K.space, K.inside, K.dim, K.transverse⟩

def OriginalLeaf.toTagged {J t h : Nat} {U : OriginalU I copies J}
    {K : OriginalK I copies t U} (L : OriginalLeaf I copies h U K) :
    TaggedLeafOver I copies h (questionOf I copies
      (U.toTagged I copies) (K.toTagged I copies)) := by
  exact ⟨L.presented, L.same_rows, L.contains_center⟩

def originalUEquiv (J : Nat) :
    OriginalU I copies J ≃ TaggedGoodU I copies J where
  toFun := OriginalU.toTagged I copies
  invFun := fun U => ⟨U.1, U.2.1, U.2.2⟩
  left_inv := by rintro ⟨U, hU, hcard⟩; rfl
  right_inv := by rintro ⟨U, hU, hcard⟩; rfl

def originalKEquiv {J : Nat} (t : Nat) (U : OriginalU I copies J) :
    OriginalK I copies t U ≃
      TaggedCenterOver I copies t (U.toTagged I copies) where
  toFun := OriginalK.toTagged I copies
  invFun := fun K => ⟨K.1, K.2.1, K.2.2.1, K.2.2.2⟩
  left_inv := by rintro ⟨K, hK, hdim, htrans⟩; rfl
  right_inv := by rintro ⟨K, hK, hdim, htrans⟩; rfl

def originalLeafEquiv {J t : Nat} (h : Nat)
    (U : OriginalU I copies J) (K : OriginalK I copies t U) :
    OriginalLeaf I copies h U K ≃
      TaggedLeafOver I copies h
        (questionOf I copies (U.toTagged I copies) (K.toTagged I copies)) where
  toFun := OriginalLeaf.toTagged I copies
  invFun := fun L => ⟨L.1, L.2.1, L.2.2⟩
  left_inv := by rintro ⟨L, hsame, hK⟩; rfl
  right_inv := by rintro ⟨L, hsame, hK⟩; rfl

noncomputable instance originalUFintype (J : Nat) :
    Fintype (OriginalU I copies J) :=
  Fintype.ofEquiv _ (originalUEquiv I copies J).symm

noncomputable instance originalKFintype {J : Nat} (t : Nat)
    (U : OriginalU I copies J) : Fintype (OriginalK I copies t U) :=
  Fintype.ofEquiv _ (originalKEquiv I copies t U).symm

noncomputable instance originalLeafFintype {J t : Nat} (h : Nat)
    (U : OriginalU I copies J) (K : OriginalK I copies t U) :
    Fintype (OriginalLeaf I copies h U K) :=
  Fintype.ofEquiv _ (originalLeafEquiv I copies h U K).symm

structure OriginalDraw (J t h k : Nat) where
  U : OriginalU I copies J
  K : OriginalK I copies t U
  leaves : Fin k → OriginalLeaf I copies h U K
  representatives : (i : Fin k) →
    TaggedClassRepresentative I copies
      (taggedClassOf I copies ((leaves i).toTagged I copies).1)

def encodeDraw {J t h k : Nat}
    (x : OriginalDraw I copies J t h k) :
    Σ p : TaggedSample I copies J t h k,
      TaggedIndependentChoice I copies (sampledStar I copies p).leaves :=
  ⟨⟨x.U.toTagged I copies, x.K.toTagged I copies,
      fun i => (x.leaves i).toTagged I copies⟩,
    x.representatives⟩

def decodeDraw {J t h k : Nat}
    (x : Σ p : TaggedSample I copies J t h k,
      TaggedIndependentChoice I copies (sampledStar I copies p).leaves) :
    OriginalDraw I copies J t h k :=
  { U := ⟨x.1.1.1, x.1.1.2.1, x.1.1.2.2⟩
    K := ⟨x.1.2.1.1, x.1.2.1.2.1, x.1.2.1.2.2.1, x.1.2.1.2.2.2⟩
    leaves := fun i =>
      ⟨(x.1.2.2 i).1, (x.1.2.2 i).2.1, (x.1.2.2 i).2.2⟩
    representatives := x.2 }

def originalDrawEquiv {J t h k : Nat} :
    OriginalDraw I copies J t h k ≃
      Σ p : TaggedSample I copies J t h k,
        TaggedIndependentChoice I copies (sampledStar I copies p).leaves where
  toFun := encodeDraw I copies
  invFun := decodeDraw I copies
  left_inv := by
    intro x
    cases x with
    | mk U K leaves representatives =>
        cases U
        cases K
        rfl
  right_inv := by
    rintro ⟨⟨U, K, leaves⟩, representatives⟩
    cases U
    cases K
    rfl

noncomputable instance originalDrawFintype (J t h k : Nat) :
    Fintype (OriginalDraw I copies J t h k) :=
  Fintype.ofEquiv _ (originalDrawEquiv I copies).symm

abbrev OriginalFields (J t h k : Nat) :=
  Σ U : OriginalU I copies J,
    Σ K : OriginalK I copies t U,
      Σ Ls : Fin k → OriginalLeaf I copies h U K,
        (i : Fin k) → TaggedClassRepresentative I copies
          (taggedClassOf I copies ((Ls i).toTagged I copies).1)

def originalFieldsEquiv {J t h k : Nat} :
    OriginalDraw I copies J t h k ≃ OriginalFields I copies J t h k where
  toFun := fun x => ⟨x.U, x.K, x.leaves, x.representatives⟩
  invFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv := by rintro ⟨U, K, Ls, reps⟩; rfl
  right_inv := by rintro ⟨U, K, Ls, reps⟩; rfl

noncomputable instance originalFieldsFintype (J t h k : Nat) :
    Fintype (OriginalFields I copies J t h k) := by
  unfold OriginalFields
  infer_instance

/-- Direct sequential sampling: uniform copied eligible U, uniform K in its
transverse fiber, uniform ordered leaf tuple in its conditional fiber, and
independent uniform full-vertex representatives of each queried class. -/
def originalLaw {J t h k : Nat}
    [Nonempty (OriginalU I copies J)]
    (hcenter : ∀ U : OriginalU I copies J,
      Nonempty (OriginalK I copies t U))
    (hleaf : ∀ (U : OriginalU I copies J)
      (K : OriginalK I copies t U),
      Nonempty (OriginalLeaf I copies h U K)) :
    FiniteLaw (OriginalDraw I copies J t h k) := by
  classical
  let μU := uniformLaw (OriginalU I copies J)
  let μK (U : OriginalU I copies J) : FiniteLaw (OriginalK I copies t U) :=
    @uniformLaw _ inferInstance (hcenter U)
  let μL (U : OriginalU I copies J) (K : OriginalK I copies t U) :
      FiniteLaw (Fin k → OriginalLeaf I copies h U K) :=
    @uniformLaw _ inferInstance ⟨fun _ => Classical.choice (hleaf U K)⟩
  let μR (U : OriginalU I copies J) (K : OriginalK I copies t U)
      (Ls : Fin k → OriginalLeaf I copies h U K) :
      FiniteLaw ((i : Fin k) → TaggedClassRepresentative I copies
        (taggedClassOf I copies ((Ls i).toTagged I copies).1)) :=
    uniformLaw _
  refine ⟨fun x => μU.mass x.U * (μK x.U).mass x.K *
    (μL x.U x.K).mass x.leaves *
      (μR x.U x.K x.leaves).mass x.representatives, ?_, ?_⟩
  · intro x
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (μU.nonneg x.U) ((μK x.U).nonneg x.K))
        ((μL x.U x.K).nonneg x.leaves))
      ((μR x.U x.K x.leaves).nonneg x.representatives)
  · have hsum :
        (∑ U : OriginalU I copies J,
          ∑ K : OriginalK I copies t U,
            ∑ Ls : Fin k → OriginalLeaf I copies h U K,
              ∑ reps : (i : Fin k) → TaggedClassRepresentative I copies
                (taggedClassOf I copies ((Ls i).toTagged I copies).1),
                μU.mass U * (μK U).mass K * (μL U K).mass Ls *
                  (μR U K Ls).mass reps) = 1 := by
        calc
          _ = ∑ U : OriginalU I copies J,
                ∑ K : OriginalK I copies t U,
                  ∑ Ls : Fin k → OriginalLeaf I copies h U K,
                    μU.mass U * (μK U).mass K * (μL U K).mass Ls := by
              apply Finset.sum_congr rfl; intro U _
              apply Finset.sum_congr rfl; intro K _
              apply Finset.sum_congr rfl; intro Ls _
              rw [← Finset.mul_sum, (μR U K Ls).normalized, mul_one]
          _ = ∑ U : OriginalU I copies J,
                ∑ K : OriginalK I copies t U,
                  μU.mass U * (μK U).mass K := by
              apply Finset.sum_congr rfl; intro U _
              apply Finset.sum_congr rfl; intro K _
              rw [← Finset.mul_sum, (μL U K).normalized, mul_one]
          _ = ∑ U : OriginalU I copies J, μU.mass U := by
              apply Finset.sum_congr rfl; intro U _
              rw [← Finset.mul_sum, (μK U).normalized, mul_one]
          _ = 1 := μU.normalized
    have heq := Fintype.sum_equiv (originalFieldsEquiv I copies)
      (fun x : OriginalDraw I copies J t h k =>
        μU.mass x.U * (μK x.U).mass x.K *
          (μL x.U x.K).mass x.leaves *
            (μR x.U x.K x.leaves).mass x.representatives)
      (fun x : OriginalFields I copies J t h k =>
        μU.mass x.1 * (μK x.1).mass x.2.1 *
          (μL x.1 x.2.1).mass x.2.2.1 *
            (μR x.1 x.2.1 x.2.2.1).mass x.2.2.2)
      (by intro x; rfl)
    have hfields :
        (∑ x : OriginalFields I copies J t h k,
          μU.mass x.1 * (μK x.1).mass x.2.1 *
            (μL x.1 x.2.1).mass x.2.2.1 *
              (μR x.1 x.2.1 x.2.2.1).mass x.2.2.2) = 1 := by
      simpa only [OriginalFields, Fintype.sum_sigma] using hsum
    exact heq.trans hfields

/-- Both tables are fixed before any source draw. The leaf table is indexed by
full presented vertices and is legal at every such vertex. -/
structure OriginalAssignment (J h : Nat) where
  center : TaggedCenterTable I copies
  leaf : TaggedRawVertexTable I copies J h
  legal : TaggedLegalRawTable I copies leaf

def originalStar {J t h k : Nat} (x : OriginalDraw I copies J t h k) :
    TaggedPresentedStar I copies J t h k :=
  { q := questionOf I copies (x.U.toTagged I copies) (x.K.toTagged I copies)
    leaves := fun i => (x.leaves i).presented
    sameRows := fun i => (x.leaves i).same_rows
    center_le := fun i => le_trans (x.leaves i).contains_center le_sup_left }

theorem originalStar_eq_encoded {J t h k : Nat}
    (x : OriginalDraw I copies J t h k) :
    originalStar I copies x = sampledStar I copies (encodeDraw I copies x).1 := by
  rfl

/-- The original verifier's legal-table event: transport each sampled full
vertex label to its queried leaf and compare its restriction with the stored
center label. -/
def originalAccepts {J t h k : Nat}
    (A : OriginalAssignment I copies J h)
    (x : OriginalDraw I copies J t h k) : Prop :=
  ∀ i, ((taggedIndependentLabels I copies A.leaf
      (originalStar I copies x).leaves x.representatives i).1).comp
        (Submodule.inclusion ((originalStar I copies x).center_le i)) =
      A.center x.K.space

theorem originalAccepts_iff_taggedPhysical {J t h k : Nat}
    (A : OriginalAssignment I copies J h)
    (x : OriginalDraw I copies J t h k) :
    originalAccepts I copies A x ↔
      taggedPhysicalAccepts I copies A.center A.leaf
        (sampledStar I copies (encodeDraw I copies x).1)
        (encodeDraw I copies x).2 := by
  change taggedIndependentAccepts I copies A.center A.leaf
      (originalStar I copies x) x.representatives ↔
    taggedPhysicalAccepts I copies A.center A.leaf
      (originalStar I copies x) x.representatives
  exact (taggedPhysicalAccepts_iff_independentAccepts_of_legal
    I copies A.center A.leaf A.legal (originalStar I copies x)
      x.representatives).symm

def originalLawFromTagged {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (OriginalDraw I copies J t h k) := by
  letI : Nonempty (OriginalU I copies J) :=
    Nonempty.map (originalUEquiv I copies J).symm ‹_›
  exact originalLaw I copies
    (fun U => Nonempty.map (originalKEquiv I copies t U).symm
      (hcenter (U.toTagged I copies)))
    (fun U K => Nonempty.map (originalLeafEquiv I copies h U K).symm
      (hleaf (U.toTagged I copies) (K.toTagged I copies)))

def taggedJointLaw {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))) :
    FiniteLaw (Σ p : TaggedSample I copies J t h k,
      TaggedIndependentChoice I copies (sampledStar I copies p).leaves) := by
  classical
  let μ := taggedSampleLaw I copies (J := J) (t := t) (h := h) (k := k)
    hcenter hleaf
  let ν (p : TaggedSample I copies J t h k) :=
    uniformLaw (TaggedIndependentChoice I copies (sampledStar I copies p).leaves)
  refine ⟨fun x => μ.mass x.1 * (ν x.1).mass x.2, ?_, ?_⟩
  · intro x
    exact mul_nonneg (μ.nonneg x.1) ((ν x.1).nonneg x.2)
  · change ∑ x : Σ p : TaggedSample I copies J t h k,
        TaggedIndependentChoice I copies (sampledStar I copies p).leaves,
        μ.mass x.1 * (ν x.1).mass x.2 = 1
    simp only [Fintype.sum_sigma]
    calc
      _ = ∑ p : TaggedSample I copies J t h k,
          μ.mass p * (∑ r, (ν p).mass r) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.mul_sum]
      _ = ∑ p : TaggedSample I copies J t h k, μ.mass p := by
            simp [(ν _).normalized]
      _ = 1 := μ.normalized

theorem originalLaw_mass_encode {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (x : OriginalDraw I copies J t h k) :
    (originalLawFromTagged I copies hcenter hleaf).mass x =
      (taggedJointLaw I copies hcenter hleaf).mass (encodeDraw I copies x) := by
  classical
  letI : Nonempty (OriginalU I copies J) :=
    Nonempty.map (originalUEquiv I copies J).symm ‹_›
  letI : Nonempty (OriginalK I copies t x.U) :=
    Nonempty.map (originalKEquiv I copies t x.U).symm
      (hcenter (x.U.toTagged I copies))
  letI : Nonempty (Fin k → OriginalLeaf I copies h x.U x.K) :=
    ⟨fun _ => Classical.choice (Nonempty.map
      (originalLeafEquiv I copies h x.U x.K).symm
      (hleaf (x.U.toTagged I copies) (x.K.toTagged I copies)))⟩
  letI : Nonempty (TaggedCenterOver I copies t (x.U.toTagged I copies)) :=
    hcenter (x.U.toTagged I copies)
  letI : Nonempty (Fin k → TaggedLeafOver I copies h
      (questionOf I copies (x.U.toTagged I copies) (x.K.toTagged I copies))) :=
    ⟨fun _ => Classical.choice
      (hleaf (x.U.toTagged I copies) (x.K.toTagged I copies))⟩
  have hcU : Fintype.card (OriginalU I copies J) =
      Fintype.card (TaggedGoodU I copies J) :=
    Fintype.card_congr (originalUEquiv I copies J)
  have hcK : Fintype.card (OriginalK I copies t x.U) =
      Fintype.card (TaggedCenterOver I copies t (x.U.toTagged I copies)) :=
    Fintype.card_congr (originalKEquiv I copies t x.U)
  have hcL : Fintype.card (Fin k → OriginalLeaf I copies h x.U x.K) =
      Fintype.card (Fin k → TaggedLeafOver I copies h
        (questionOf I copies (x.U.toTagged I copies)
          (x.K.toTagged I copies))) :=
    Fintype.card_congr (Equiv.piCongrRight
      (fun _ : Fin k => originalLeafEquiv I copies h x.U x.K))
  change (uniformLaw (OriginalU I copies J)).mass x.U *
      (uniformLaw (OriginalK I copies t x.U)).mass x.K *
      (uniformLaw (Fin k → OriginalLeaf I copies h x.U x.K)).mass x.leaves *
      (uniformLaw ((i : Fin k) → TaggedClassRepresentative I copies
        (taggedClassOf I copies ((x.leaves i).toTagged I copies).1))).mass
        x.representatives =
    ((uniformLaw (TaggedGoodU I copies J)).mass (x.U.toTagged I copies) *
      (uniformLaw (TaggedCenterOver I copies t (x.U.toTagged I copies))).mass
        (x.K.toTagged I copies) *
      (uniformLaw (Fin k → TaggedLeafOver I copies h
        (questionOf I copies (x.U.toTagged I copies)
          (x.K.toTagged I copies)))).mass
        (fun i => (x.leaves i).toTagged I copies)) *
      (uniformLaw ((i : Fin k) → TaggedClassRepresentative I copies
        (taggedClassOf I copies ((x.leaves i).toTagged I copies).1))).mass
        x.representatives
  simp only [uniformLaw_apply, hcU, hcK, hcL]

def originalScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (A : OriginalAssignment I copies J h) : ℚ := by
  classical
  exact eventMass (originalLawFromTagged I copies (k := k) hcenter hleaf)
    (Finset.univ.filter (originalAccepts I copies A))

def taggedJointEventMass {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) : ℚ := by
  classical
  exact eventMass (taggedJointLaw I copies (k := k) hcenter hleaf)
    (Finset.univ.filter (fun x =>
      taggedPhysicalAccepts I copies C T (sampledStar I copies x.1) x.2))

theorem originalScore_eq_taggedJointEvent {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (A : OriginalAssignment I copies J h) :
    originalScore I copies (k := k) hcenter hleaf A =
      taggedJointEventMass I copies (k := k) hcenter hleaf A.center A.leaf := by
  classical
  unfold originalScore taggedJointEventMass eventMass
  simp only [Finset.sum_filter, Finset.mem_univ, true_and]
  apply Fintype.sum_equiv (originalDrawEquiv I copies)
  intro x
  change (if originalAccepts I copies A x then
      (originalLawFromTagged I copies hcenter hleaf).mass x else 0) =
    if taggedPhysicalAccepts I copies A.center A.leaf
        (sampledStar I copies (encodeDraw I copies x).1)
        (encodeDraw I copies x).2 then
      (taggedJointLaw I copies hcenter hleaf).mass (encodeDraw I copies x)
    else 0
  rw [← originalAccepts_iff_taggedPhysical I copies A x]
  rw [← originalLaw_mass_encode I copies hcenter hleaf x]

theorem taggedJointEvent_eq_taggedSourceVerifierScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h) :
    taggedJointEventMass I copies (k := k) hcenter hleaf C T =
      taggedSourceVerifierScore I copies (k := k) hcenter hleaf C T := by
  classical
  unfold taggedJointEventMass eventMass taggedSourceVerifierScore taggedPhysicalMass
  simp only [Finset.sum_filter, Finset.mem_univ, true_and,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp only [taggedJointLaw, FiniteLaw.mass]
  rw [orderedStarLaw_eq_taggedSampleLaw]
  simp only [uniformLaw_apply,
    ActualCliqueCollisionTransfer.uniformMean, div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.mul_sum]
  simp [mul_ite, ite_mul, mul_assoc]
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

theorem originalScore_eq_taggedSourceVerifierScore {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (A : OriginalAssignment I copies J h) :
    originalScore I copies (k := k) hcenter hleaf A =
      taggedSourceVerifierScore I copies (k := k) hcenter hleaf A.center A.leaf := by
  rw [originalScore_eq_taggedJointEvent,
    taggedJointEvent_eq_taggedSourceVerifierScore]

/-- For each arbitrary legal predraw table pair, one fixed class selector
recovers its original verifier score up to the explicit class-collision mass.
The selector is chosen after the tables and before the verifier draw. -/
theorem originalScore_le_selected_add_collision {J t h k : Nat}
    [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (A : OriginalAssignment I copies J h) :
    ∃ s : TaggedRepresentativeChoice I copies J h,
      originalScore I copies (k := k) hcenter hleaf A ≤
        taggedSelectedMass I copies
          (orderedStarLaw I copies J (t := t) (h := h) (k := k)
            hcenter hleaf).mass
          (sampledStar I copies (J := J) (t := t) (h := h) (k := k))
          A.center A.leaf s + (1 / 2 : ℚ) ^ J := by
  rw [originalScore_eq_taggedSourceVerifierScore]
  exact taggedSourceVerifierScore_le_selected_add_collision I copies
    hcenter hleaf ht hh hexp hk A.center A.leaf

end
end PvNP.RealizableHardness.ActualOriginalPostPaddingVerifier
