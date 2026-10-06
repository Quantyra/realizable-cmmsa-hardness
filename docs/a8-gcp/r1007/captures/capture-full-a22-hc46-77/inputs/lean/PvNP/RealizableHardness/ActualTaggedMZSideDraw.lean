import PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
import PvNP.RealizableHardness.GrassmannCounting

/-! The fixed first-question MZ draw in the actual tagged coordinate space. -/

namespace PvNP.RealizableHardness.ActualTaggedMZSideDraw

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
open PvNP.RealizableHardness.ActualTaggedFixedUDensityForce
open PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-- Transverse center in the coordinate space of a fixed eligible first
question.  Mapping it to the tagged ambient gives the paper's center R. -/
def SideCenter (t : Nat) :=
  {K : Grass (coordinateSpace (taggedSource I copies).support U.1) t //
    (K.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype) ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥}

instance (t : Nat) : Fintype (SideCenter I copies U t) := by
  classical
  unfold SideCenter
  infer_instance

def centerToSide {t : Nat} (K : TaggedCenterOver I copies t U) :
    SideCenter I copies U t := by
  let E := coordinateSpace (taggedSource I copies).support U.1
  refine { val := { val := K.1.comap E.subtype, property := ?_ }, property := ?_ }
  · rw [(Submodule.comapSubtypeEquivOfLe K.2.1).finrank_eq, K.2.2.1]
  · change (K.1.comap E.subtype).map E.subtype ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥
    rw [Submodule.map_comap_subtype, inf_of_le_right K.2.1]
    exact K.2.2.2

def sideToCenter {t : Nat} (K : SideCenter I copies U t) :
    TaggedCenterOver I copies t U := by
  let E := coordinateSpace (taggedSource I copies).support U.1
  refine { val := K.1.val.map E.subtype, property := ?_ }
  constructor
  · exact E.map_subtype_le K.1.val
  constructor
  · rw [Submodule.finrank_map_subtype_eq, K.1.property]
  · exact K.2

def centerEquivSide (t : Nat) :
    Equiv (TaggedCenterOver I copies t U) (SideCenter I copies U t) where
  toFun := centerToSide I copies U
  invFun := sideToCenter I copies U
  left_inv := by
    intro K
    unfold sideToCenter centerToSide
    apply Subtype.ext
    change (K.1.comap (coordinateSpace (taggedSource I copies).support U.1).subtype).map
      (coordinateSpace (taggedSource I copies).support U.1).subtype = K.1
    exact (Submodule.map_comap_subtype _ _).trans (inf_of_le_right K.2.1)
  right_inv := by
    intro K
    unfold sideToCenter centerToSide
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective
      (coordinateSpace (taggedSource I copies).support U.1).injective_subtype K.1.val

instance sideCenterNonempty {t : Nat}
    [Nonempty (TaggedCenterOver I copies t U)] :
    Nonempty (SideCenter I copies U t) :=
  ⟨centerEquivSide I copies U t (Classical.choice inferInstance)⟩

/-- A side-conditioned leaf is transverse to the equation space and contains
the sampled center in the same coordinate space. -/
def SideLeaf {t : Nat} (h : Nat) (K : SideCenter I copies U t) :=
  {L : Grass (coordinateSpace (taggedSource I copies).support U.1) (2 * h) //
    (L.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype) ⊓
      equationSpan (taggedSource I copies).support U.1 = ⊥ ∧
    K.1.val ≤ L.val}

instance {t : Nat} (h : Nat) (K : SideCenter I copies U t) :
    Fintype (SideLeaf I copies U h K) := by
  classical
  unfold SideLeaf
  infer_instance

def leafToSide {t h : Nat} (K : TaggedCenterOver I copies t U)
    (P : TaggedLeafOver I copies h (questionOf I copies U K)) :
    SideLeaf I copies U h (centerToSide I copies U K) := by
  let E := coordinateSpace (taggedSource I copies).support U.1
  have hPU : P.1.U = U.1 := by simpa only [questionOf] using P.2.1
  have hLle : P.1.L ≤ E := by
    simpa only [E, hPU] using P.1.L_le
  refine { val := { val := P.1.L.comap E.subtype, property := ?_ }, property := ?_ }
  · rw [(Submodule.comapSubtypeEquivOfLe hLle).finrank_eq, P.1.finrank_L]
  · constructor
    · change (P.1.L.comap E.subtype).map E.subtype ⊓
        equationSpan (taggedSource I copies).support U.1 = ⊥
      rw [Submodule.map_comap_subtype, inf_of_le_right hLle]
      simpa only [hPU] using P.1.transverse
    · intro x hx
      exact P.2.2 hx

def sideToLeaf {t h : Nat} (K : TaggedCenterOver I copies t U)
    (L : SideLeaf I copies U h (centerToSide I copies U K)) :
    TaggedLeafOver I copies h (questionOf I copies U K) := by
  let E := coordinateSpace (taggedSource I copies).support U.1
  refine { val := {
    U := U.1
    goodU := U.2.1
    card_U := U.2.2
    L := L.1.val.map E.subtype
    L_le := E.map_subtype_le L.1.val
    finrank_L := by rw [Submodule.finrank_map_subtype_eq, L.1.property]
    transverse := L.2.1 }, property := ?_ }
  constructor
  · rfl
  · intro x hx
    have hxE : x ∈ E := K.2.1 hx
    let z : E := ⟨x, hxE⟩
    have hz : z ∈ (centerToSide I copies U K).1.val := hx
    exact ⟨z, L.2.2 hz, rfl⟩

def leafEquivSide {t h : Nat} (K : TaggedCenterOver I copies t U) :
    Equiv (TaggedLeafOver I copies h (questionOf I copies U K))
      (SideLeaf I copies U h (centerToSide I copies U K)) where
  toFun := leafToSide I copies U K
  invFun := sideToLeaf I copies U K
  left_inv := by
    intro P
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P with
      | mk U' good card L Lle rank trans =>
        have hU : U' = U.1 := hP.1
        subst U'
        simp only [sideToLeaf, leafToSide]
        congr 1
        exact (Submodule.map_comap_subtype _ _).trans (inf_of_le_right Lle)
  right_inv := by
    intro L
    unfold leafToSide sideToLeaf
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective
      (coordinateSpace (taggedSource I copies).support U.1).injective_subtype L.1.val

instance sideLeafNonempty {t h : Nat} (K : TaggedCenterOver I copies t U)
    [Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))] :
    Nonempty (SideLeaf I copies U h (centerToSide I copies U K)) :=
  ⟨leafEquivSide I copies U K (Classical.choice inferInstance)⟩

/-- The complete fixed-U MZ side-conditioned draw. -/
def SideDraw (t h k : Nat) :=
  Sigma (fun K : SideCenter I copies U t => Fin k → SideLeaf I copies U h K)

noncomputable instance sideDrawFintype (t h k : Nat) :
    Fintype (SideDraw I copies U t h k) := by
  unfold SideDraw
  infer_instance

def taggedDrawEquivSide (t h k : Nat) :
    Equiv
      (Sigma (fun K : TaggedCenterOver I copies t U =>
        Fin k → TaggedLeafOver I copies h (questionOf I copies U K)))
      (SideDraw I copies U t h k) :=
  Equiv.sigmaCongr (centerEquivSide I copies U t)
    (fun K => Equiv.arrowCongr (Equiv.refl (Fin k))
      (leafEquivSide I copies U K))

/-- The center marginal remains uniform after the coordinate-space change
of variables; there is no reweighting by complement presentations. -/
theorem center_uniform_mass_eq {t : Nat}
    [Nonempty (TaggedCenterOver I copies t U)]
    (K : TaggedCenterOver I copies t U) :
    (uniformLaw (TaggedCenterOver I copies t U)).mass K =
      (uniformLaw (SideCenter I copies U t)).mass
        (centerEquivSide I copies U t K) := by
  letI : Nonempty (SideCenter I copies U t) :=
    ⟨centerEquivSide I copies U t (Classical.choice inferInstance)⟩
  rw [uniformLaw_apply, uniformLaw_apply]
  congr 1
  exact_mod_cast Fintype.card_congr (centerEquivSide I copies U t)

/-- Conditional independent leaf tuples also retain uniform mass. -/
theorem leaves_uniform_mass_eq {t h k : Nat}
    (K : TaggedCenterOver I copies t U)
    [Nonempty (TaggedLeafOver I copies h (questionOf I copies U K))]
    (Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K)) :
    (uniformLaw (Fin k → TaggedLeafOver I copies h
      (questionOf I copies U K))).mass Ls =
      (uniformLaw (Fin k → SideLeaf I copies U h
        (centerToSide I copies U K))).mass
          (Equiv.arrowCongr (Equiv.refl (Fin k))
            (leafEquivSide I copies U K) Ls) := by
  letI : Nonempty (Fin k → TaggedLeafOver I copies h
      (questionOf I copies U K)) := ⟨fun _ => Classical.choice inferInstance⟩
  letI : Nonempty (Fin k → SideLeaf I copies U h
      (centerToSide I copies U K)) :=
    ⟨fun _ => leafEquivSide I copies U K (Classical.choice inferInstance)⟩
  rw [uniformLaw_apply, uniformLaw_apply]
  congr 1
  exact_mod_cast Fintype.card_congr
    (Equiv.arrowCongr (Equiv.refl (Fin k)) (leafEquivSide I copies U K))

/-- The full vertex queried by a side-conditioned transverse leaf is its
ambient lift together with the first question's equation space. -/
def sideDomain {t h : Nat} {K : SideCenter I copies U t}
    (L : SideLeaf I copies U h K) :
    Submodule (ZMod 2) (TaggedAmbient I copies) :=
  (L.1.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype) ⊔
    equationSpan (taggedSource I copies).support U.1

theorem sideToLeaf_domain {t h : Nat}
    (K : TaggedCenterOver I copies t U)
    (L : SideLeaf I copies U h (centerToSide I copies U K)) :
    (sideToLeaf I copies U K L).1.domain I copies =
      sideDomain I copies U L := rfl

theorem sideDomain_leafToSide {t h : Nat}
    (K : TaggedCenterOver I copies t U)
    (P : TaggedLeafOver I copies h (questionOf I copies U K)) :
    sideDomain I copies U (leafToSide I copies U K P) =
      P.1.domain I copies := by
  rw [← sideToLeaf_domain I copies U K]
  have hP := (leafEquivSide I copies U K).left_inv P
  rw [show sideToLeaf I copies U K (leafToSide I copies U K P) = P from hP]

theorem sideCenter_le_domain {t h : Nat}
    (K : SideCenter I copies U t) (L : SideLeaf I copies U h K) :
    K.1.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype ≤
      sideDomain I copies U L := by
  exact (Submodule.map_mono L.2.2).trans le_sup_left

theorem sideEquation_mem_domain {t h : Nat}
    (K : SideCenter I copies U t) (L : SideLeaf I copies U h K)
    (e : TaggedRow I copies) (he : e ∈ U.1) :
    equationVector (taggedSource I copies).support e ∈
      sideDomain I copies U L := by
  exact (le_sup_right : equationSpan (taggedSource I copies).support U.1 ≤
    sideDomain I copies U L)
    (equationVector_mem_equationSpan (taggedSource I copies).support U.1 e he)

/-- The MZ side-conditioned consistency event, with one fixed full-domain
table and one fixed center table.  The equation RHS is checked on the same
full vertex domain used for the center restriction. -/
def sideAccepts {t h k : Nat}
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (K : SideCenter I copies U t)
    (Ls : Fin k → SideLeaf I copies U h K) : Prop :=
  ∀ i,
    (∀ e (he : e ∈ U.1),
      T' (sideDomain I copies U (Ls i))
        ⟨equationVector (taggedSource I copies).support e,
          sideEquation_mem_domain I copies U K (Ls i) e he⟩ =
        (taggedSource I copies).rhs e) ∧
    (T' (sideDomain I copies U (Ls i))).comp
        (Submodule.inclusion (sideCenter_le_domain I copies U K (Ls i))) =
      C (K.1.val.map (coordinateSpace (taggedSource I copies).support U.1).subtype)

private theorem fixedLeaf_test_iff_domain {t : Nat}
    (q : TaggedQuestionCenter I copies J t)
    (F : TaggedLeaf I copies q)
    (D : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hD : F.domain I copies = D)
    (hK : q.K ≤ D)
    (hrow : ∀ e (he : e ∈ q.U),
      equationVector (taggedSource I copies).support e ∈ D)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    (F.respectsRows I copies T' ∧
      F.restrictedLabel I copies T' = C q.K) ↔
      (∀ e (he : e ∈ q.U),
        T' D ⟨equationVector (taggedSource I copies).support e,
          hrow e he⟩ = (taggedSource I copies).rhs e) ∧
      (T' D).comp (Submodule.inclusion hK) = C q.K := by
  subst D
  rfl

private theorem restriction_label_congr
    (D S S' : Submodule (ZMod 2) (TaggedAmbient I copies))
    (hEq : S = S') (hSD : S ≤ D) (hS'D : S' ≤ D)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    ((T' D).comp (Submodule.inclusion hSD) = C S) ↔
      ((T' D).comp (Submodule.inclusion hS'D) = C S') := by
  cases hEq
  rfl

/-- On every fixed center and leaf tuple, the actual tagged verifier is
exactly the side-conditioned MZ consistency event.  Both sides use the same
predraw full-domain table and the same stored center. -/
theorem taggedAccepts_iff_sideAccepts {t h k : Nat}
    (K : TaggedCenterOver I copies t U)
    (Ls : Fin k → TaggedLeafOver I copies h (questionOf I copies U K))
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    taggedAccepts I copies C T'
      (sampledStar I copies
        (⟨U, K, Ls⟩ : TaggedSample I copies J t h k)).q
      (taggedConvertedLeaves I copies
        (sampledStar I copies (⟨U, K, Ls⟩ : TaggedSample I copies J t h k))) ↔
      sideAccepts I copies U C T' (centerToSide I copies U K)
        (fun i => leafToSide I copies U K (Ls i)) := by
  let omega : TaggedSample I copies J t h k := ⟨U, K, Ls⟩
  let z := sampledStar I copies omega
  have hKmap :
      (centerToSide I copies U K).1.val.map
        (coordinateSpace (taggedSource I copies).support U.1).subtype = K.1 := by
    change (K.1.comap
      (coordinateSpace (taggedSource I copies).support U.1).subtype).map
        (coordinateSpace (taggedSource I copies).support U.1).subtype = K.1
    exact (Submodule.map_comap_subtype _ _).trans (inf_of_le_right K.2.1)
  have hD (i : Fin k) :
      (taggedConvertedLeaves I copies z i).domain I copies =
        sideDomain I copies U (leafToSide I copies U K (Ls i)) := by
    calc
      _ = (z.leaves i).domain I copies := taggedConvertedLeaves_domain I copies z i
      _ = (Ls i).1.domain I copies := rfl
      _ = _ := (sideDomain_leafToSide I copies U K (Ls i)).symm
  unfold taggedAccepts sideAccepts
  apply forall_congr'
  intro i
  have hK : z.q.K ≤ sideDomain I copies U (leafToSide I copies U K (Ls i)) := by
    change K.1 ≤ sideDomain I copies U (leafToSide I copies U K (Ls i))
    rw [← hKmap]
    exact sideCenter_le_domain I copies U (centerToSide I copies U K)
      (leafToSide I copies U K (Ls i))
  have hrow : ∀ e (he : e ∈ z.q.U),
      equationVector (taggedSource I copies).support e ∈
        sideDomain I copies U (leafToSide I copies U K (Ls i)) := by
    intro e he
    exact sideEquation_mem_domain I copies U (centerToSide I copies U K)
      (leafToSide I copies U K (Ls i)) e he
  have h := fixedLeaf_test_iff_domain I copies z.q
    (taggedConvertedLeaves I copies z i)
    (sideDomain I copies U (leafToSide I copies U K (Ls i)))
    (hD i) hK hrow C T'
  have hc := restriction_label_congr I copies
    (sideDomain I copies U (leafToSide I copies U K (Ls i))) z.q.K
    ((centerToSide I copies U K).1.val.map
      (coordinateSpace (taggedSource I copies).support U.1).subtype)
    (by simpa only [z, omega, sampledStar, questionOf] using hKmap.symm)
    hK (sideCenter_le_domain I copies U (centerToSide I copies U K)
      (leafToSide I copies U K (Ls i))) C T'
  have h' := h.trans (and_congr Iff.rfl hc)
  simpa only [z, omega, sampledStar, questionOf] using h'

/-- Exact normalized side-conditioned Grassmann test density at a fixed
eligible first question.  Each center has its own conditional independent
leaf tuple, and the tables are fixed outside both sums. -/
def sideConditionalDensity (t h k : Nat)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) : ℚ := by
  classical
  exact ∑ K : SideCenter I copies U t,
    ∑ Ls : Fin k → SideLeaf I copies U h K,
      ((1 : ℚ) / Fintype.card (SideCenter I copies U t)) *
        ((1 : ℚ) / Fintype.card (Fin k → SideLeaf I copies U h K)) *
        (if sideAccepts I copies U C T' K Ls then (1 : ℚ) else 0)

theorem conditionalCanonicalDensity_eq_side {t h k : Nat}
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies) :
    conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U =
      sideConditionalDensity I copies U t h k C T' := by
  classical
  letI : Nonempty (TaggedCenterOver I copies t U) := hcenter U
  unfold conditionalCanonicalDensity sideConditionalDensity
  apply Fintype.sum_equiv (centerEquivSide I copies U t)
  intro K
  letI : Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)) :=
    hleaf U K
  apply Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.refl (Fin k)) (leafEquivSide I copies U K))
  intro Ls
  simp only [uniformLaw_apply]
  rw [Fintype.card_congr (centerEquivSide I copies U t),
    Fintype.card_congr
      (Equiv.arrowCongr (Equiv.refl (Fin k)) (leafEquivSide I copies U K))]
  congr 1
  exact ite_congr
    (propext (taggedAccepts_iff_sideAccepts I copies U K Ls C T'))
    (fun _ => rfl) (fun _ => rfl)

/-- The composed legal value forces the exact MZ side-conditioned test above
the `8S` threshold on the same fraction of eligible first questions.  This
does not assert the MZ decoder conclusion. -/
theorem composedLegalValue_gt_forces_side_threshold_U
    {J t h k p q : Nat} [Nonempty (TaggedGoodU I copies J)]
    (hcenter : ∀ U : TaggedGoodU I copies J,
      Nonempty (TaggedCenterOver I copies t U))
    (hleaf : ∀ (U : TaggedGoodU I copies J)
      (K : TaggedCenterOver I copies t U),
      Nonempty (TaggedLeafOver I copies h (questionOf I copies U K)))
    (ht : t ≤ 2 * h) (hh : h ≤ J)
    (hexp : 2 * J ≤ (2 * h - t) * (2 * J - 2 * h))
    (hk : k ^ 2 ≤ 2 ^ J)
    (xi rho : ℚ) (hxi : xi = 4000 * rho)
    (hp : (p : ℚ) = 2 * (1 - 1000 * rho) * h * m)
    (hq : (q : ℚ) = 2 * (1 - xi) * h * m)
    (hlarge : (6 : ℚ) ≤ 6000 * rho * h * m)
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
              sideConditionalDensity I copies U t h k C T'
             then (1 : ℚ) else 0) := by
  obtain ⟨C, T, T', hgood⟩ :=
    composedLegalValue_gt_forces_MZ_threshold_U I copies
      hcenter hleaf ht hh hexp hk xi rho hxi hp hq hlarge hpJ hvalue
  refine ⟨C, T, T', ?_⟩
  calc
    8 * (1 / 2 : ℚ) ^ p ≤
        ∑ U : TaggedGoodU I copies J,
          (uniformLaw (TaggedGoodU I copies J)).mass U *
            (if 8 * (1 / 2 : ℚ) ^ p ≤
              conditionalCanonicalDensity I copies (k := k) hcenter hleaf C T' U
             then (1 : ℚ) else 0) := hgood
    _ = _ := by
      apply Finset.sum_congr rfl
      intro U _
      rw [conditionalCanonicalDensity_eq_side I copies U hcenter hleaf C T']

end
end PvNP.RealizableHardness.ActualTaggedMZSideDraw
