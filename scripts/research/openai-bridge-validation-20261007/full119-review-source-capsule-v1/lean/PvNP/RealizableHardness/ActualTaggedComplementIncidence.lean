import PvNP.RealizableHardness.ActualTaggedMZSideDraw
import PvNP.RealizableHardness.ActualTaggedConditionalDomainDraw

/-! The center/complement incidence count used by the fixed-U complement law. -/
namespace PvNP.RealizableHardness.ActualTaggedComplementIncidence

open PvNP.RealizableHardness
open ActualTaggedMZSideDraw
open ActualStarSpanIntersection
open ActualTaggedConcreteStarLaw
open ActualTaggedPresentedSelection
open ActualTaggedFixedCenterGeometry
open ActualTaggedOrderedSampleNonempty
open ActualTaggedConditionalGraphCount
open ActualTaggedPresentationFiberAudit
open ActualBinaryGrassmannSamplingBounds
open ActualTaggedFixedTableAcceptance
open ActualFiniteLaw
open ActualTaggedComposedPhysicalSampler
open GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

abbrev SideComplement :=
  {A : Submodule (ZMod 2) (E I copies U) // IsCompl (H I copies U) A}

abbrev SideComplementOver {t : Nat} (K : SideCenter I copies U t) :=
  {A : SideComplement I copies U // K.1.val ≤ A.1}

private def sideQuestion {t : Nat} (K : SideCenter I copies U t) :=
  questionOf I copies U (sideToCenter I copies U K)

private theorem equation_map_eq :
    (H I copies U).map (E I copies U).subtype =
      equationSpan (taggedSource I copies).support U.1 := by
  have hle : equationSpan (taggedSource I copies).support U.1 ≤
      E I copies U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    exact equationVector_mem_coordinateSpace
      (taggedSource I copies).support U.1 e he
  simp only [H, E, Submodule.map_comap_subtype]
  exact inf_of_le_right hle

/-- Ordinary complement leaf carrier. Its ambient full domain is the
equation space plus the image of this leaf under the complement inclusion. -/
def OrdinaryLeaf {t : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (_hKA : K.1.val ≤ A.1) (h : Nat) :=
  {L : Grass A.1 (2 * h) //
    K.1.val.comap A.1.subtype ≤ L.val}

instance {t : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1) (h : Nat) :
    Fintype (OrdinaryLeaf I copies U A K hKA h) := by
  classical
  unfold OrdinaryLeaf
  infer_instance

def SideFullDomain {t : Nat} (K : SideCenter I copies U t) (h : Nat) :=
  {D : Submodule (ZMod 2) (E I copies U) //
    H I copies U ≤ D ∧ K.1.val ≤ D ∧
      Module.finrank (ZMod 2) D = J + 2 * h}

instance {t : Nat} (K : SideCenter I copies U t) (h : Nat) :
    Fintype (SideFullDomain I copies U K h) := by
  classical
  unfold SideFullDomain
  infer_instance

def sideFullToTagged {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h) :
    ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
      (sideQuestion I copies U K) h := by
  let q := sideQuestion I copies U K
  have hqK : q.K = K.1.val.map (E I copies U).subtype := rfl
  have hqH : equationSpanOf I copies q =
      (H I copies U).map (E I copies U).subtype := by
    exact (equation_map_eq I copies U).symm
  refine ⟨D.1.map (E I copies U).subtype, ?_, ?_, ?_, ?_⟩
  · exact (E I copies U).map_subtype_le D.1
  · rw [hqK]
    exact Submodule.map_mono D.2.2.1
  · rw [hqH]
    exact Submodule.map_mono D.2.1
  · rw [Submodule.finrank_map_subtype_eq, D.2.2.2]

def taggedToSideFull {t h : Nat} (K : SideCenter I copies U t)
    (D : ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
      (sideQuestion I copies U K) h) : SideFullDomain I copies U K h := by
  let q := sideQuestion I copies U K
  have hqK : q.K = K.1.val.map (E I copies U).subtype := rfl
  have hqH : equationSpanOf I copies q =
      (H I copies U).map (E I copies U).subtype :=
    (equation_map_eq I copies U).symm
  refine ⟨D.1.comap (E I copies U).subtype, ?_, ?_, ?_⟩
  · intro x hx
    have : ((x : E I copies U) : TaggedAmbient I copies) ∈
        equationSpanOf I copies q := by
      rw [hqH]
      exact ⟨x, hx, rfl⟩
    exact D.2.2.2.1 this
  · intro x hx
    have : ((x : E I copies U) : TaggedAmbient I copies) ∈ q.K := by
      rw [hqK]
      exact ⟨x, hx, rfl⟩
    exact D.2.2.1 this
  · have hh := (Submodule.comapSubtypeEquivOfLe D.2.1).finrank_eq
    exact hh.trans D.2.2.2.2

def sideFullTaggedEquiv {t h : Nat} (K : SideCenter I copies U t) :
    SideFullDomain I copies U K h ≃
      ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
        (sideQuestion I copies U K) h where
  toFun := sideFullToTagged I copies U K
  invFun := taggedToSideFull I copies U K
  left_inv := by
    intro D
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective
      (E I copies U).injective_subtype D.1
  right_inv := by
    intro D
    apply Subtype.ext
    exact (Submodule.map_comap_subtype _ _).trans
      (inf_of_le_right D.2.1)

def sideLeafToFull {t h : Nat} (K : SideCenter I copies U t)
    (L : SideLeaf I copies U h K) : SideFullDomain I copies U K h := by
  have hdis : Disjoint (H I copies U) L.1.val := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxmap : ((x : E I copies U) : TaggedAmbient I copies) ∈
        (L.1.val.map (E I copies U).subtype) ⊓
          equationSpan (taggedSource I copies).support U.1 := by
      constructor
      · exact ⟨x, hx.2, rfl⟩
      · rw [← equation_map_eq I copies U]
        exact ⟨x, hx.1, rfl⟩
    rw [L.2.1] at hxmap
    exact Subtype.ext (by simpa using hxmap)
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    have hh := taggedEquationInCoordinate_finrank I copies (sideQuestion I copies U K)
    change Module.finrank (ZMod 2) (H I copies U) = J at hh
    exact hh
  have hDdim : Module.finrank (ZMod 2) ↥(H I copies U ⊔ L.1.val) =
      J + 2 * h := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (K := ZMod 2) (V := E I copies U) (H I copies U) L.1.val
    rw [hdis.eq_bot, finrank_bot, add_zero, hHdim, L.1.property] at hs
    omega
  exact ⟨H I copies U ⊔ L.1.val,
    (le_sup_left : H I copies U ≤ H I copies U ⊔ L.1.val),
    L.2.2.trans (le_sup_right : L.1.val ≤ H I copies U ⊔ L.1.val),
    hDdim⟩

private def taggedLeafEquivSideFixed {t h : Nat} (K : SideCenter I copies U t) :
    ActualTaggedConcreteStarLaw.TaggedLeafOver I copies h
      (sideQuestion I copies U K) ≃ SideLeaf I copies U h K := by
  let Ktag := sideToCenter I copies U K
  have hK : centerToSide I copies U Ktag = K :=
    (centerEquivSide I copies U t).right_inv K
  exact (leafEquivSide I copies U Ktag).trans
    (Equiv.cast (congrArg (fun K' : SideCenter I copies U t =>
      SideLeaf I copies U h K') hK))

private theorem castSideLeaf_val {t h : Nat}
    {K K' : SideCenter I copies U t} (hK : K = K')
    (L : SideLeaf I copies U h K) :
    ((Equiv.cast (congrArg (fun Q : SideCenter I copies U t =>
      SideLeaf I copies U h Q) hK)) L).1.val = L.1.val := by
  cases hK
  rfl

private theorem taggedLeafEquivSideFixed_val {t h : Nat}
    (K : SideCenter I copies U t)
    (P : ActualTaggedConcreteStarLaw.TaggedLeafOver I copies h
      (sideQuestion I copies U K)) :
    (taggedLeafEquivSideFixed I copies U K P).1.val =
      (leafToSide I copies U (sideToCenter I copies U K) P).1.val := by
  let Ktag := sideToCenter I copies U K
  have hK : centerToSide I copies U Ktag = K :=
    (centerEquivSide I copies U t).right_inv K
  change ((Equiv.cast (congrArg (fun Q : SideCenter I copies U t =>
    SideLeaf I copies U h Q) hK)
      (leafToSide I copies U Ktag P))).1.val =
        (leafToSide I copies U Ktag P).1.val
  exact castSideLeaf_val I copies U hK (leafToSide I copies U Ktag P)

theorem sideLeafToFull_domain {t h : Nat} (K : SideCenter I copies U t)
    (L : SideLeaf I copies U h K) :
    (sideLeafToFull I copies U K L).1.map (E I copies U).subtype =
      sideDomain I copies U L := by
  change (H I copies U ⊔ L.1.val).map (E I copies U).subtype =
    L.1.val.map (E I copies U).subtype ⊔
      equationSpan (taggedSource I copies).support U.1
  rw [Submodule.map_sup, equation_map_eq I copies U, sup_comm]

private theorem taggedLeaf_sideFull_commutes {t h : Nat}
    (K : SideCenter I copies U t)
    (P : ActualTaggedConcreteStarLaw.TaggedLeafOver I copies h
      (sideQuestion I copies U K)) :
    sideFullToTagged I copies U K
      (sideLeafToFull I copies U K (taggedLeafEquivSideFixed I copies U K P)) =
        ActualTaggedConditionalDomainDraw.taggedLeaf_domainDraw I copies
          (sideQuestion I copies U K) P := by
  apply Subtype.ext
  change (sideLeafToFull I copies U K
      (taggedLeafEquivSideFixed I copies U K P)).1.map
        (E I copies U).subtype = P.1.domain I copies
  rw [sideLeafToFull_domain I copies U K]
  let Ktag := sideToCenter I copies U K
  have hK : centerToSide I copies U Ktag = K :=
    (centerEquivSide I copies U t).right_inv K
  have hraw := sideDomain_leafToSide I copies U Ktag P
  change (taggedLeafEquivSideFixed I copies U K P).1.val.map
      (E I copies U).subtype ⊔
        equationSpan (taggedSource I copies).support U.1 = P.1.domain I copies
  rw [taggedLeafEquivSideFixed_val I copies U K P]
  exact hraw

/-- At a fixed observed center, the actual independent tagged leaf draw has
the uniform law on tuples of full domains containing that center. -/
theorem uniform_sideLeafTuple_pushforward {t h k : Nat}
    (K : SideCenter I copies U t) (ht : t ≤ 2 * h) (hh : h ≤ J) :
    letI : Nonempty (SideLeaf I copies U h K) := by
      letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
        (sideQuestion I copies U K) h) :=
        ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
          (sideQuestion I copies U K) ht hh
      exact ⟨taggedLeafEquivSideFixed I copies U K
        (ActualTaggedConditionalDomainDraw.taggedDomainDraw_leaf I copies
          (sideQuestion I copies U K) (Classical.choice inferInstance))⟩
    letI : Nonempty (SideFullDomain I copies U K h) := by
      letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
        (sideQuestion I copies U K) h) :=
        ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
          (sideQuestion I copies U K) ht hh
      exact ⟨(sideFullTaggedEquiv I copies U K).symm
        (Classical.choice inferInstance)⟩
    pushforward (fun Ls : Fin k → SideLeaf I copies U h K =>
        fun i => sideLeafToFull I copies U K (Ls i))
      (uniformLaw (Fin k → SideLeaf I copies U h K)) =
        uniformLaw (Fin k → SideFullDomain I copies U K h) := by
  classical
  let q := sideQuestion I copies U K
  letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies q h) :=
    ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies q ht hh
  letI : Nonempty (TaggedLeafOver I copies h q) :=
    ⟨ActualTaggedConditionalDomainDraw.taggedDomainDraw_leaf I copies q
      (Classical.choice inferInstance)⟩
  letI : Nonempty (SideLeaf I copies U h K) :=
    ⟨taggedLeafEquivSideFixed I copies U K (Classical.choice
      (show Nonempty (TaggedLeafOver I copies h q) from inferInstance))⟩
  letI : Nonempty (SideFullDomain I copies U K h) :=
    ⟨(sideFullTaggedEquiv I copies U K).symm
      (Classical.choice (show Nonempty
        (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies q h)
          from inferInstance))⟩
  let eL : (Fin k → TaggedLeafOver I copies h q) ≃
      (Fin k → SideLeaf I copies U h K) :=
    Equiv.piCongrRight (fun _ => taggedLeafEquivSideFixed I copies U K)
  let eD : (Fin k → ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies q h) ≃
      (Fin k → SideFullDomain I copies U K h) :=
    Equiv.piCongrRight (fun _ => (sideFullTaggedEquiv I copies U K).symm)
  let F : (Fin k → SideLeaf I copies U h K) →
      (Fin k → SideFullDomain I copies U K h) :=
    fun Ls i => sideLeafToFull I copies U K (Ls i)
  let G : (Fin k → TaggedLeafOver I copies h q) →
      (Fin k → ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies q h) :=
    fun Ls i => ActualTaggedConditionalDomainDraw.taggedLeaf_domainDraw
      I copies q (Ls i)
  have hcomm : F ∘ eL = eD ∘ G := by
    funext Ls
    funext i
    apply (sideFullTaggedEquiv I copies U K).injective
    change (sideFullTaggedEquiv I copies U K)
        (sideLeafToFull I copies U K
          (taggedLeafEquivSideFixed I copies U K (Ls i))) =
      (sideFullTaggedEquiv I copies U K)
        ((sideFullTaggedEquiv I copies U K).symm
          (ActualTaggedConditionalDomainDraw.taggedLeaf_domainDraw
            I copies q (Ls i)))
    rw [Equiv.apply_symm_apply]
    exact taggedLeaf_sideFull_commutes I copies U K (Ls i)
  have htag : pushforward G
      (uniformLaw (Fin k → TaggedLeafOver I copies h q)) =
      uniformLaw (Fin k → ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies q h) := by
    exact uniform_leafTuple_pushforward I copies q ht hh (k := k)
  change pushforward F (uniformLaw (Fin k → SideLeaf I copies U h K)) =
    uniformLaw (Fin k → SideFullDomain I copies U K h)
  calc
    _ = pushforward F (pushforward eL
          (uniformLaw (Fin k → TaggedLeafOver I copies h q))) := by
      rw [pushforward_uniformLaw_equiv eL]
    _ = pushforward (F ∘ eL)
          (uniformLaw (Fin k → TaggedLeafOver I copies h q)) :=
      pushforward_comp eL F _
    _ = pushforward (eD ∘ G)
          (uniformLaw (Fin k → TaggedLeafOver I copies h q)) := by rw [hcomm]
    _ = pushforward eD (pushforward G
          (uniformLaw (Fin k → TaggedLeafOver I copies h q))) :=
      (pushforward_comp G eD _).symm
    _ = pushforward eD
          (uniformLaw (Fin k → ActualTaggedConditionalDomainDraw.TaggedDomainDraw
            I copies q h)) := by rw [htag]
    _ = uniformLaw (Fin k → SideFullDomain I copies U K h) :=
      pushforward_uniformLaw_equiv eD

private def fullDomain {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  D.1.map (E I copies U).subtype

private theorem fullCenter_le {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h) :
    K.1.val.map (E I copies U).subtype ≤ fullDomain I copies U K D :=
  Submodule.map_mono D.2.2.1

private theorem fullEquation_mem {t h : Nat} (K : SideCenter I copies U t)
    (D : SideFullDomain I copies U K h)
    (e : TaggedRow I copies) (he : e ∈ U.1) :
    equationVector (taggedSource I copies).support e ∈
      fullDomain I copies U K D := by
  have hH := equationVector_mem_equationSpan
    (taggedSource I copies).support U.1 e he
  rw [← equation_map_eq I copies U] at hH
  exact (Submodule.map_mono D.2.1) hH

/-- The ordinary complement star event depends only on the observed full
domains. The center and full-domain tables are fixed before sampling. -/
def fullAccepts {t h k : Nat} (K : SideCenter I copies U t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (Ds : Fin k → SideFullDomain I copies U K h) : Prop :=
  ∀ i,
    (∀ e (he : e ∈ U.1),
      T' (fullDomain I copies U K (Ds i))
        ⟨equationVector (taggedSource I copies).support e,
          fullEquation_mem I copies U K (Ds i) e he⟩ =
        (taggedSource I copies).rhs e) ∧
    (T' (fullDomain I copies U K (Ds i))).comp
      (Submodule.inclusion (fullCenter_le I copies U K (Ds i))) =
      C (K.1.val.map (E I copies U).subtype)

private def domainEvent {t : Nat} (K : SideCenter I copies U t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (D : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hK : K.1.val.map (E I copies U).subtype ≤ D)
    (hrow : ∀ e (he : e ∈ U.1),
      equationVector (taggedSource I copies).support e ∈ D) : Prop :=
  (∀ e (he : e ∈ U.1),
    T' D ⟨equationVector (taggedSource I copies).support e, hrow e he⟩ =
      (taggedSource I copies).rhs e) ∧
    (T' D).comp (Submodule.inclusion hK) =
      C (K.1.val.map (E I copies U).subtype)

private theorem domainEvent_congr {t : Nat} (K : SideCenter I copies U t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (D₁ D₂ : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hD : D₁ = D₂)
    (hK₁ : K.1.val.map (E I copies U).subtype ≤ D₁)
    (hK₂ : K.1.val.map (E I copies U).subtype ≤ D₂)
    (hrow₁ : ∀ e (he : e ∈ U.1),
      equationVector (taggedSource I copies).support e ∈ D₁)
    (hrow₂ : ∀ e (he : e ∈ U.1),
      equationVector (taggedSource I copies).support e ∈ D₂) :
    domainEvent I copies U K C T' D₁ hK₁ hrow₁ ↔
      domainEvent I copies U K C T' D₂ hK₂ hrow₂ := by
  subst D₂
  rfl

theorem sideAccepts_iff_fullAccepts {t h k : Nat}
    (K : SideCenter I copies U t)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (Ls : Fin k → SideLeaf I copies U h K) :
    sideAccepts I copies U C T' K Ls ↔
      fullAccepts I copies U K C T'
        (fun i => sideLeafToFull I copies U K (Ls i)) := by
  simp only [sideAccepts, fullAccepts]
  apply forall_congr'
  intro i
  have hD := (sideLeafToFull_domain I copies U K (Ls i)).symm
  change domainEvent I copies U K C T'
      (sideDomain I copies U (Ls i))
        (sideCenter_le_domain I copies U K (Ls i))
        (sideEquation_mem_domain I copies U K (Ls i)) ↔
    domainEvent I copies U K C T'
      (fullDomain I copies U K (sideLeafToFull I copies U K (Ls i)))
        (fullCenter_le I copies U K (sideLeafToFull I copies U K (Ls i)))
        (fullEquation_mem I copies U K (sideLeafToFull I copies U K (Ls i)))
  exact domainEvent_congr I copies U K C T' _ _ hD _ _ _ _

/-- The actual fixed-center acceptance mass is exactly the mass of the same
event under uniform full-domain tuples. Both tables remain globally fixed. -/
theorem side_fixedCenter_acceptance_mass_eq_full {t h k : Nat}
    (K : SideCenter I copies U t) (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    letI : Nonempty (SideLeaf I copies U h K) := by
      letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
        (sideQuestion I copies U K) h) :=
        ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
          (sideQuestion I copies U K) ht hh
      exact ⟨taggedLeafEquivSideFixed I copies U K
        (ActualTaggedConditionalDomainDraw.taggedDomainDraw_leaf I copies
          (sideQuestion I copies U K) (Classical.choice inferInstance))⟩
    letI : Nonempty (SideFullDomain I copies U K h) := by
      letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
        (sideQuestion I copies U K) h) :=
        ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
          (sideQuestion I copies U K) ht hh
      exact ⟨(sideFullTaggedEquiv I copies U K).symm
        (Classical.choice inferInstance)⟩
    (∑ Ls : Fin k → SideLeaf I copies U h K,
      ((1 : Rat) / Fintype.card (Fin k → SideLeaf I copies U h K)) *
        (if sideAccepts I copies U C T' K Ls then 1 else 0)) =
    (∑ Ds : Fin k → SideFullDomain I copies U K h,
      ((1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h)) *
        (if fullAccepts I copies U K C T' Ds then 1 else 0)) := by
  classical
  letI : Nonempty (SideLeaf I copies U h K) := by
    letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
      (sideQuestion I copies U K) h) :=
      ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
        (sideQuestion I copies U K) ht hh
    exact ⟨taggedLeafEquivSideFixed I copies U K
      (ActualTaggedConditionalDomainDraw.taggedDomainDraw_leaf I copies
        (sideQuestion I copies U K) (Classical.choice inferInstance))⟩
  letI : Nonempty (SideFullDomain I copies U K h) := by
    letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
      (sideQuestion I copies U K) h) :=
      ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
        (sideQuestion I copies U K) ht hh
    exact ⟨(sideFullTaggedEquiv I copies U K).symm
      (Classical.choice inferInstance)⟩
  let F : (Fin k → SideLeaf I copies U h K) →
      (Fin k → SideFullDomain I copies U K h) :=
    fun Ls i => sideLeafToFull I copies U K (Ls i)
  let E : Finset (Fin k → SideFullDomain I copies U K h) :=
    Finset.univ.filter (fullAccepts I copies U K C T')
  have hpush := uniform_sideLeafTuple_pushforward I copies U K ht hh (k := k)
  have hevent := congrArg (fun μ => eventMass μ E) hpush
  rw [eventMass_pushforward] at hevent
  have hsum :
      (∑ Ls : Fin k → SideLeaf I copies U h K,
        if fullAccepts I copies U K C T' (F Ls) then
          (1 : Rat) / Fintype.card (Fin k → SideLeaf I copies U h K) else 0) =
      (∑ Ds : Fin k → SideFullDomain I copies U K h,
        if fullAccepts I copies U K C T' Ds then
          (1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h)
        else 0) := by
    simpa only [eventMass, preimageEvent, E, F, Finset.sum_filter,
      Finset.mem_filter, Finset.mem_univ, true_and, uniformLaw_apply] using hevent
  simpa only [F, sideAccepts_iff_fullAccepts, mul_ite, mul_one,
    mul_zero] using hsum

def CenterInComplement (A : SideComplement I copies U) (t : Nat) :=
  {K : SideCenter I copies U t // K.1.val ≤ A.1}

instance (A : SideComplement I copies U) (t : Nat) :
    Fintype (CenterInComplement I copies U A t) := by
  classical
  unfold CenterInComplement
  infer_instance

def ordinaryCenterToSide (A : SideComplement I copies U) {t : Nat}
    (K : Grass A.1 t) : CenterInComplement I copies U A t := by
  let B : Submodule (ZMod 2) (E I copies U) := K.val.map A.1.subtype
  have hB_A : B ≤ A.1 := A.1.map_subtype_le K.val
  have hBdim : Module.finrank (ZMod 2) B = t := by
    rw [Submodule.finrank_map_subtype_eq]
    exact K.property
  have hBE : Disjoint B (H I copies U) :=
    (A.2.disjoint.mono_right hB_A).symm
  have hHmap : (H I copies U).map (E I copies U).subtype =
      equationSpan (taggedSource I copies).support U.1 :=
    equation_map_eq I copies U
  have htrans : B.map (E I copies U).subtype ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥ := by
    rw [← hHmap]
    exact (Submodule.disjoint_map_of_ker_le_right hBE (by simp)).eq_bot
  exact ⟨⟨⟨B, hBdim⟩, htrans⟩, hB_A⟩

def sideCenterToOrdinary (A : SideComplement I copies U) {t : Nat}
    (K : CenterInComplement I copies U A t) : Grass A.1 t := by
  refine ⟨K.1.1.val.comap A.1.subtype, ?_⟩
  rw [(Submodule.comapSubtypeEquivOfLe K.2).finrank_eq]
  exact K.1.1.property

def centerInComplementEquiv (A : SideComplement I copies U) (t : Nat) :
    Grass A.1 t ≃ CenterInComplement I copies U A t where
  toFun := ordinaryCenterToSide I copies U A
  invFun := sideCenterToOrdinary I copies U A
  left_inv := by
    intro K
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective A.1.injective_subtype K.val
  right_inv := by
    intro K
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [ordinaryCenterToSide, sideCenterToOrdinary]
    change (K.1.1.val.comap A.1.subtype).map A.1.subtype = K.1.1.val
    exact (Submodule.map_comap_subtype _ _).trans (inf_of_le_right K.2)

theorem sideComplement_finrank (A : SideComplement I copies U) :
    Module.finrank (ZMod 2) A.1 = 2 * J := by
  obtain ⟨K₀⟩ := taggedCenterOver_nonempty I copies U (t := 0) (by omega)
  let q := questionOf I copies U K₀
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    have hh := taggedEquationInCoordinate_finrank I copies q
    change Module.finrank (ZMod 2) (H I copies U) = J at hh
    exact hh
  have hEdim : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by
    have hh := taggedCoordinate_finrank I copies q
    change Module.finrank (ZMod 2) (E I copies U) = 3 * J at hh
    exact hh
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (K := ZMod 2) (V := E I copies U) (H I copies U) A.1
  rw [A.2.codisjoint.eq_top, finrank_top, A.2.disjoint.eq_bot,
    finrank_bot, add_zero, hHdim, hEdim] at hs
  omega

theorem centerInComplement_card (A : SideComplement I copies U) (t : Nat) :
    Fintype.card (CenterInComplement I copies U A t) =
      gaussian (2 * J) t := by
  rw [← Fintype.card_congr (centerInComplementEquiv I copies U A t)]
  rw [card_grass, sideComplement_finrank I copies U A]

private theorem full_eq_H_sup_inf {t h : Nat}
    (A : SideComplement I copies U) (K : SideCenter I copies U t)
    (_hKA : K.1.val ≤ A.1) (D : SideFullDomain I copies U K h)
    : H I copies U ⊔ (A.1 ⊓ D.1) = D.1 := by
  have hmod := Submodule.sup_inf_assoc_of_le_of_neg_le A.1 D.2.1
    (by simpa using D.2.1)
  rw [A.2.codisjoint.eq_top] at hmod
  simpa using hmod.symm

def ordinaryToFull {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (L : OrdinaryLeaf I copies U A K hKA h) :
    SideFullDomain I copies U K h := by
  let B : Submodule (ZMod 2) (E I copies U) := L.1.val.map A.1.subtype
  have hB_A : B ≤ A.1 := A.1.map_subtype_le L.1.val
  have hBdim : Module.finrank (ZMod 2) B = 2 * h := by
    rw [Submodule.finrank_map_subtype_eq]
    exact L.1.property
  have hK_B : K.1.val ≤ B := by
    intro x hx
    let y : A.1 := ⟨x, hKA hx⟩
    have hy : y ∈ K.1.val.comap A.1.subtype := hx
    exact ⟨y, L.2 hy, rfl⟩
  have hdis : Disjoint (H I copies U) B :=
    A.2.disjoint.mono_right hB_A
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    let q := questionOf I copies U (sideToCenter I copies U K)
    have hh := taggedEquationInCoordinate_finrank I copies q
    change Module.finrank (ZMod 2) (H I copies U) = J at hh
    exact hh
  have hDdim : Module.finrank (ZMod 2) ↥(H I copies U ⊔ B) = J + 2 * h := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (K := ZMod 2) (V := E I copies U) (H I copies U) B
    rw [hdis.eq_bot, finrank_bot, add_zero, hHdim, hBdim] at hs
    omega
  exact ⟨H I copies U ⊔ B,
    (le_sup_left : H I copies U ≤ H I copies U ⊔ B),
    hK_B.trans (le_sup_right : B ≤ H I copies U ⊔ B), hDdim⟩

def fullToOrdinary {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1)
    (D : SideFullDomain I copies U K h) :
    OrdinaryLeaf I copies U A K hKA h := by
  let B : Submodule (ZMod 2) A.1 := D.1.comap A.1.subtype
  have hBmap : B.map A.1.subtype = A.1 ⊓ D.1 := by
    simp only [B, Submodule.map_comap_subtype, inf_comm]
  have hdis : Disjoint (H I copies U) (A.1 ⊓ D.1) :=
    A.2.disjoint.mono_right inf_le_left
  have hEq := full_eq_H_sup_inf I copies U A K hKA D
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    let q := questionOf I copies U (sideToCenter I copies U K)
    have hh := taggedEquationInCoordinate_finrank I copies q
    change Module.finrank (ZMod 2) (H I copies U) = J at hh
    exact hh
  have hBdim : Module.finrank (ZMod 2) B = 2 * h := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (K := ZMod 2) (V := E I copies U)
      (H I copies U) (A.1 ⊓ D.1)
    rw [hdis.eq_bot, finrank_bot, add_zero, hEq, D.2.2.2, hHdim] at hs
    have hm : Module.finrank (ZMod 2) ↥(A.1 ⊓ D.1) =
        Module.finrank (ZMod 2) B := by
      rw [← hBmap, Submodule.finrank_map_subtype_eq]
    rw [hm] at hs
    omega
  refine ⟨⟨B, hBdim⟩, ?_⟩
  intro x hx
  exact D.2.2.1 hx

def ordinaryFullEquiv {t h : Nat} (A : SideComplement I copies U)
    (K : SideCenter I copies U t) (hKA : K.1.val ≤ A.1) :
    OrdinaryLeaf I copies U A K hKA h ≃
      SideFullDomain I copies U K h where
  toFun := ordinaryToFull I copies U A K hKA
  invFun := fullToOrdinary I copies U A K hKA
  left_inv := by
    intro L
    apply Subtype.ext
    apply Subtype.ext
    change (H I copies U ⊔ L.1.val.map A.1.subtype).comap A.1.subtype = L.1.val
    have hdis : Disjoint (H I copies U) A.1 := A.2.disjoint
    -- The complement is disjoint from H, so restriction of H+L to A is L.
    ext x
    simp only [Submodule.mem_comap]
    constructor
    · intro hx
      rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hsum⟩
      have hyA : y ∈ A.1 := by
        have hzA : z ∈ A.1 := A.1.map_subtype_le L.1.val hz
        have hxA : (x : E I copies U) ∈ A.1 := x.property
        have hyEq : y = (x : E I copies U) - z := by
          calc
            y = y + z - z := by simp
            _ = (x : E I copies U) - z := congrArg (fun w => w - z) hsum
        rw [hyEq]
        exact A.1.sub_mem hxA hzA
      have hy0 : y = 0 := by
        have hh : y ∈ H I copies U ⊓ A.1 := ⟨hy, hyA⟩
        rw [hdis.eq_bot] at hh
        simpa using hh
      rw [hy0, zero_add] at hsum
      have hzL : z ∈ L.1.val.map A.1.subtype := hz
      rcases hzL with ⟨v, hv, hvz⟩
      have hvx : v = x := Subtype.val_injective (hvz.trans hsum)
      simpa [← hvx] using hv
    · intro hx
      exact (le_sup_right : L.1.val.map A.1.subtype ≤
        H I copies U ⊔ L.1.val.map A.1.subtype) ⟨x, hx, rfl⟩
  right_inv := by
    intro D
    apply Subtype.ext
    change H I copies U ⊔
      (D.1.comap A.1.subtype).map A.1.subtype = D.1
    rw [Submodule.map_comap_subtype]
    simpa only [inf_comm] using full_eq_H_sup_inf I copies U A K hKA D

instance {t : Nat} (K : SideCenter I copies U t) :
    Fintype (SideComplementOver I copies U K) := by
  classical
  unfold SideComplementOver
  infer_instance

private theorem side_disjoint {t : Nat} (K : SideCenter I copies U t) :
    Disjoint K.1.val (H I copies U) := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  have hmap : ((x : E I copies U) : TaggedAmbient I copies) ∈
      (K.1.val.map (E I copies U).subtype) ⊓
        equationSpan (taggedSource I copies).support U.1 := by
    constructor
    · exact ⟨x, hx.1, rfl⟩
    · exact hx.2
  rw [K.2] at hmap
  exact Subtype.ext (by simpa using hmap)

theorem side_complements_over_card {t : Nat} (K : SideCenter I copies U t) :
    Fintype.card (SideComplementOver I copies U K) =
      2 ^ (J * (2 * J - t)) := by
  let q := questionOf I copies U (sideToCenter I copies U K)
  have hdis := side_disjoint I copies U K
  obtain ⟨C, hKC, hCompl⟩ := hdis.exists_isCompl
  let KC : Submodule (ZMod 2) C := K.1.val.comap C.subtype
  have hKCmap : KC.map C.subtype = K.1.val := by
    simpa only [KC, Submodule.map_comap_subtype, inf_of_le_right hKC]
  have hHdim : Module.finrank (ZMod 2) (H I copies U) = J := by
    have hh := taggedEquationInCoordinate_finrank I copies q
    change Module.finrank (ZMod 2) (H I copies U) = J at hh
    exact hh
  have hEdim : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by
    have hh := taggedCoordinate_finrank I copies q
    change Module.finrank (ZMod 2) (E I copies U) = 3 * J at hh
    exact hh
  have hCdim : Module.finrank (ZMod 2) C = 2 * J := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (K := ZMod 2) (V := E I copies U) (H I copies U) C
    rw [hCompl.symm.codisjoint.eq_top, finrank_top, hCompl.symm.disjoint.eq_bot,
      finrank_bot, add_zero, hHdim, hEdim] at hs
    have hs' : 3 * J = J + Module.finrank (ZMod 2) C := by
      simpa only [hHdim, hEdim] using hs
    omega
  have hKCdim : Module.finrank (ZMod 2) KC = t := by
    change Module.finrank (ZMod 2) (K.1.val.comap C.subtype) = t
    rw [(Submodule.comapSubtypeEquivOfLe hKC).finrank_eq]
    exact K.1.property
  letI : Fintype (Submodule (ZMod 2) (E I copies U)) :=
    ActualTaggedConditionalGraphCount.conditionalSubmoduleFintype
  have hcard := card_conditional_complements (H I copies U) C hCompl.symm KC
  have hequiv : SideComplementOver I copies U K ≃
      {A : SideComplement I copies U // KC.map C.subtype ≤ A.1} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro A
      simp [hKCmap])
  calc
    _ = Fintype.card
        {A : SideComplement I copies U // KC.map C.subtype ≤ A.1} :=
      Fintype.card_congr hequiv
    _ = Fintype.card
        {A : {M : Submodule (ZMod 2) (E I copies U) //
          IsCompl (H I copies U) M} // KC.map C.subtype ≤ A.1} :=
      Fintype.card_congr (Equiv.refl _)
    _ = 2 ^ ((Module.finrank (ZMod 2) C - Module.finrank (ZMod 2) KC) *
          Module.finrank (ZMod 2) (H I copies U)) := by
      exact (Fintype.card_congr (Equiv.refl _)).trans hcard
    _ = 2 ^ (J * (2 * J - t)) := by rw [hCdim, hKCdim, hHdim, Nat.mul_comm]

private def centerComplementIncidenceEquiv (t : Nat) :
    (Σ A : SideComplement I copies U, CenterInComplement I copies U A t) ≃
      (Σ K : SideCenter I copies U t, SideComplementOver I copies U K) where
  toFun p := ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
  invFun p := ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
  left_inv := by intro p; cases p with | mk A K => cases K; rfl
  right_inv := by intro p; cases p with | mk K A => cases A; rfl

theorem center_complement_incidence_balance (t : Nat) :
    Fintype.card (SideComplement I copies U) * gaussian (2 * J) t =
      Fintype.card (SideCenter I copies U t) *
        2 ^ (J * (2 * J - t)) := by
  classical
  calc
    _ = ∑ A : SideComplement I copies U,
          Fintype.card (CenterInComplement I copies U A t) := by
      simp [centerInComplement_card I copies U, Finset.sum_const]
    _ = Fintype.card
        (Σ A : SideComplement I copies U, CenterInComplement I copies U A t) :=
      Fintype.card_sigma.symm
    _ = Fintype.card
        (Σ K : SideCenter I copies U t, SideComplementOver I copies U K) :=
      Fintype.card_congr (centerComplementIncidenceEquiv I copies U t)
    _ = ∑ K : SideCenter I copies U t,
          Fintype.card (SideComplementOver I copies U K) := Fintype.card_sigma
    _ = _ := by simp [side_complements_over_card I copies U, Finset.sum_const]

theorem ordinary_tuple_card_eq_full {t h k : Nat}
    (A : SideComplement I copies U) (K : SideCenter I copies U t)
    (hKA : K.1.val ≤ A.1) :
    Fintype.card (Fin k → OrdinaryLeaf I copies U A K hKA h) =
      Fintype.card (Fin k → SideFullDomain I copies U K h) := by
  exact Fintype.card_congr
    (Equiv.arrowCongr (Equiv.refl (Fin k))
      (ordinaryFullEquiv I copies U A K hKA))

/-- Exact scalar normalization of one observed `(K, full-domain tuple)` atom
after summing every complement containing the same fixed center. -/
theorem complement_observed_atom_weight {t h k : Nat}
    (K : SideCenter I copies U t) (ht : t ≤ 2 * J)
    [Nonempty (SideFullDomain I copies U K h)] :
    (∑ A : SideComplementOver I copies U K,
      ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
        ((1 : Rat) / Fintype.card
          (CenterInComplement I copies U A.1 t)) *
        ((1 : Rat) / Fintype.card
          (Fin k → OrdinaryLeaf I copies U A.1 K A.2 h))) =
      ((1 : Rat) / Fintype.card (SideCenter I copies U t)) *
        ((1 : Rat) / Fintype.card
          (Fin k → SideFullDomain I copies U K h)) := by
  classical
  have hcent (A : SideComplementOver I copies U K) :
      Fintype.card (CenterInComplement I copies U A.1 t) =
        gaussian (2 * J) t := centerInComplement_card I copies U A.1 t
  have hleaf (A : SideComplementOver I copies U K) :
      Fintype.card (Fin k → OrdinaryLeaf I copies U A.1 K A.2 h) =
        Fintype.card (Fin k → SideFullDomain I copies U K h) :=
    ordinary_tuple_card_eq_full I copies U A.1 K A.2
  simp_rw [hcent, hleaf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcomp : 0 < Fintype.card (SideComplement I copies U) := by
    have hover : 0 < Fintype.card (SideComplementOver I copies U K) := by
      rw [side_complements_over_card I copies U K]
      positivity
    obtain ⟨A⟩ := Fintype.card_pos_iff.mp hover
    exact Fintype.card_pos_iff.mpr ⟨A.1⟩
  have hcenter : 0 < Fintype.card (SideCenter I copies U t) :=
    Fintype.card_pos_iff.mpr ⟨K⟩
  have hgauss : 0 < gaussian (2 * J) t := gaussian_pos ht
  have htuple : 0 < Fintype.card (Fin k → SideFullDomain I copies U K h) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Classical.choice inferInstance⟩
  have hbalance := center_complement_incidence_balance I copies U t
  have hbalanceR :
      (Fintype.card (SideComplement I copies U) : Rat) * gaussian (2 * J) t =
        (Fintype.card (SideCenter I copies U t) : Rat) *
          Fintype.card (SideComplementOver I copies U K) := by
    rw [side_complements_over_card I copies U K]
    exact_mod_cast hbalance
  have hcR : (Fintype.card (SideComplement I copies U) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcomp.ne'
  have hgR : (gaussian (2 * J) t : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr hgauss.ne'
  have huR : (Fintype.card (SideCenter I copies U t) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcenter.ne'
  have hdR : (Fintype.card (Fin k → SideFullDomain I copies U K h) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr htuple.ne'
  field_simp
  nlinarith [hbalanceR]

/-- Density of the observed full-domain star at the same fixed eligible U and
globally fixed center and leaf tables. -/
def observedFullDensity (t h k : Nat)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : Rat :=
  ∑ K : SideCenter I copies U t,
    ∑ Ds : Fin k → SideFullDomain I copies U K h,
      ((1 : Rat) / Fintype.card (SideCenter I copies U t)) *
        ((1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h)) *
          (if fullAccepts I copies U K C T' Ds then 1 else 0)

theorem sideConditionalDensity_eq_observedFullDensity {t h k : Nat}
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    sideConditionalDensity I copies U t h k C T' =
      observedFullDensity I copies U t h k C T' := by
  classical
  unfold sideConditionalDensity observedFullDensity
  apply Finset.sum_congr rfl
  intro K _
  have hmass := side_fixedCenter_acceptance_mass_eq_full
    I copies U K ht hh C T' (k := k)
  let c : Rat := (1 : Rat) / Fintype.card (SideCenter I copies U t)
  calc
    (∑ Ls : Fin k → SideLeaf I copies U h K,
      c * ((1 : Rat) / Fintype.card (Fin k → SideLeaf I copies U h K)) *
        (if sideAccepts I copies U C T' K Ls then 1 else 0)) =
      c * (∑ Ls : Fin k → SideLeaf I copies U h K,
        ((1 : Rat) / Fintype.card (Fin k → SideLeaf I copies U h K)) *
          (if sideAccepts I copies U C T' K Ls then 1 else 0)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = c * (∑ Ds : Fin k → SideFullDomain I copies U K h,
        ((1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h)) *
          (if fullAccepts I copies U K C T' Ds then 1 else 0)) := by rw [hmass]
    _ = ∑ Ds : Fin k → SideFullDomain I copies U K h,
        c * ((1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h)) *
          (if fullAccepts I copies U K C T' Ds then 1 else 0) := by
      simp only [Finset.mul_sum, mul_assoc]

/-- The A-first ordinary complement experiment, expressed through its
full-domain observation after the ordinary-leaf equivalence. -/
def complementFullDensity (t h k : Nat)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : Rat :=
  ∑ A : SideComplement I copies U,
    ∑ Kc : CenterInComplement I copies U A t,
      ∑ Ds : Fin k → SideFullDomain I copies U Kc.1 h,
        (((1 : Rat) / Fintype.card (SideComplement I copies U)) *
          ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
          ((1 : Rat) / Fintype.card
            (Fin k → SideFullDomain I copies U Kc.1 h))) *
          (if fullAccepts I copies U Kc.1 C T' Ds then 1 else 0)

theorem complementFullDensity_eq_observedFullDensity {t h k : Nat}
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    complementFullDensity I copies U t h k C T' =
      observedFullDensity I copies U t h k C T' := by
  classical
  have htJ : t ≤ 2 * J := by omega
  let w (A : SideComplement I copies U) (K : SideCenter I copies U t)
      (Ds : Fin k → SideFullDomain I copies U K h) : Rat :=
    (((1 : Rat) / Fintype.card (SideComplement I copies U)) *
      ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
      ((1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h))) *
      (if fullAccepts I copies U K C T' Ds then 1 else 0)
  let v (K : SideCenter I copies U t)
      (Ds : Fin k → SideFullDomain I copies U K h) : Rat :=
    ((1 : Rat) / Fintype.card (SideCenter I copies U t)) *
      ((1 : Rat) / Fintype.card (Fin k → SideFullDomain I copies U K h)) *
      (if fullAccepts I copies U K C T' Ds then 1 else 0)
  change (∑ A : SideComplement I copies U,
    ∑ Kc : CenterInComplement I copies U A t,
      ∑ Ds : Fin k → SideFullDomain I copies U Kc.1 h,
        w A Kc.1 Ds) =
    ∑ K : SideCenter I copies U t,
      ∑ Ds : Fin k → SideFullDomain I copies U K h, v K Ds
  calc
    _ = ∑ p : Σ A : SideComplement I copies U,
        CenterInComplement I copies U A t,
        ∑ Ds : Fin k → SideFullDomain I copies U p.2.1 h,
          w p.1 p.2.1 Ds := (Fintype.sum_sigma _).symm
    _ = ∑ p : Σ K : SideCenter I copies U t,
        SideComplementOver I copies U K,
        ∑ Ds : Fin k → SideFullDomain I copies U p.1 h,
          w p.2.1 p.1 Ds := by
      apply Fintype.sum_equiv (centerComplementIncidenceEquiv I copies U t)
      intro p
      rfl
    _ = ∑ K : SideCenter I copies U t,
        ∑ A : SideComplementOver I copies U K,
          ∑ Ds : Fin k → SideFullDomain I copies U K h,
            w A.1 K Ds := Fintype.sum_sigma _
    _ = ∑ K : SideCenter I copies U t,
        ∑ Ds : Fin k → SideFullDomain I copies U K h,
          ∑ A : SideComplementOver I copies U K,
            w A.1 K Ds := by
      apply Finset.sum_congr rfl
      intro K _
      exact Finset.sum_comm
    _ = ∑ K : SideCenter I copies U t,
        ∑ Ds : Fin k → SideFullDomain I copies U K h, v K Ds := by
      apply Finset.sum_congr rfl
      intro K _
      letI : Nonempty (SideFullDomain I copies U K h) := by
        letI : Nonempty (ActualTaggedConditionalDomainDraw.TaggedDomainDraw I copies
          (sideQuestion I copies U K) h) :=
          ActualTaggedConditionalDomainDraw.taggedDomainDraw_nonempty I copies
            (sideQuestion I copies U K) ht hh
        exact ⟨(sideFullTaggedEquiv I copies U K).symm
          (Classical.choice inferInstance)⟩
      apply Finset.sum_congr rfl
      intro Ds _
      have hweight :
          (∑ A : SideComplementOver I copies U K,
            ((1 : Rat) / Fintype.card (SideComplement I copies U)) *
              ((1 : Rat) / Fintype.card
                (CenterInComplement I copies U A.1 t)) *
              ((1 : Rat) / Fintype.card
                (Fin k → SideFullDomain I copies U K h))) =
            ((1 : Rat) / Fintype.card (SideCenter I copies U t)) *
              ((1 : Rat) / Fintype.card
                (Fin k → SideFullDomain I copies U K h)) := by
        simpa only [ordinary_tuple_card_eq_full I copies U] using
          complement_observed_atom_weight I copies U K htJ (h := h) (k := k)
      dsimp only [w, v]
      rw [← Finset.sum_mul, hweight]
/-- Ordinary A-first star density: draw a uniform complement, then a uniform
center in it, then independent uniform ordinary leaves in that complement.
Acceptance reads the globally fixed tables on the resulting full domains. -/
def ordinaryComplementStarDensity (t h k : Nat)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : Rat :=
  ∑ A : SideComplement I copies U,
    ∑ Kc : CenterInComplement I copies U A t,
      ∑ Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h,
        (((1 : Rat) / Fintype.card (SideComplement I copies U)) *
          ((1 : Rat) / Fintype.card (CenterInComplement I copies U A t)) *
          ((1 : Rat) / Fintype.card
            (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h))) *
          (if fullAccepts I copies U Kc.1 C T'
            (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))
            then 1 else 0)

theorem ordinaryComplementStarDensity_eq_complementFullDensity {t h k : Nat}
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    ordinaryComplementStarDensity I copies U t h k C T' =
      complementFullDensity I copies U t h k C T' := by
  classical
  unfold ordinaryComplementStarDensity complementFullDensity
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro Kc _
  let e : (Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h) ≃
      (Fin k → SideFullDomain I copies U Kc.1 h) :=
    Equiv.arrowCongr (Equiv.refl (Fin k))
      (ordinaryFullEquiv I copies U A Kc.1 Kc.2)
  apply Fintype.sum_equiv e
  intro Ls
  rw [ordinary_tuple_card_eq_full I copies U A Kc.1 Kc.2 (k := k)]
  rfl

/-- Fixed-U observed-law comparison required by the tagged NO route. It uses
the actual transverse source law and the same arbitrary fixed center/leaf
tables on both sides. Representative collision remains charged upstream. -/
theorem sideConditionalDensity_eq_ordinaryComplementStarDensity {t h k : Nat}
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    sideConditionalDensity I copies U t h k C T' =
      ordinaryComplementStarDensity I copies U t h k C T' := by
  calc
    _ = observedFullDensity I copies U t h k C T' :=
      sideConditionalDensity_eq_observedFullDensity I copies U ht hh C T'
    _ = complementFullDensity I copies U t h k C T' :=
      (complementFullDensity_eq_observedFullDensity I copies U ht hh C T').symm
    _ = ordinaryComplementStarDensity I copies U t h k C T' :=
      (ordinaryComplementStarDensity_eq_complementFullDensity I copies U C T').symm

end
end PvNP.RealizableHardness.ActualTaggedComplementIncidence
