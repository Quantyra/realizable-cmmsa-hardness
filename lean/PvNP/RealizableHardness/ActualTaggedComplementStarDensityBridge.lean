import PvNP.RealizableHardness.ActualTaggedComplementIncidence
import PvNP.RealizableHardness.ActualChangedAmbient8SBoundary

/-! Deterministic transport of one globally fixed tagged table pair to each
ordinary complement. The source row predicate is retained separately. -/
namespace PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge

open PvNP.RealizableHardness
open ActualTaggedComplementIncidence
open ActualTaggedMZSideDraw
open ActualTaggedFixedTableAcceptance
open ActualTaggedFixedCenterGeometry
open ActualChangedAmbient8SBoundary
open ActualTaggedConcreteStarLaw
open ActualStarSpanIntersection
open GrassmannCounting

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
local instance : DecidableEq I.RowId := Classical.decEq _
local instance : DecidableEq I.GlobalVar := inferInstance

private abbrev E := coordinateSpace (taggedSource I copies).support U.1

def complementInclusion (A : SideComplement I copies U) :
    A.1 →ₗ[ZMod 2] TaggedAmbient I copies :=
  (E I copies U).subtype.comp A.1.subtype

def ordinaryObservedDomain (A : SideComplement I copies U) {d : Nat}
    (L : Grass A.1 d) : Submodule (ZMod 2) (TaggedAmbient I copies) :=
  equationSpan (taggedSource I copies).support U.1 ⊔
    L.val.map (complementInclusion I copies U A)

/-- The center table on a complement is the pullback of the one fixed
predraw center table. No table is selected in response to A. -/
def transportedCenterTable (A : SideComplement I copies U) {t : Nat}
    (C : TaggedCenterTable I copies) : Labels (V := A.1) t :=
  fun K =>
    (C (K.val.map (complementInclusion I copies U A))).comp
      (((complementInclusion I copies U A).comp K.val.subtype).codRestrict
        (K.val.map (complementInclusion I copies U A)) (by
          intro x
          exact ⟨x.1, x.2, rfl⟩))

/-- The ordinary leaf label is the pullback of the same globally fixed
full-domain leaf table, indexed at H_U+L. -/
def transportedLeafTable (A : SideComplement I copies U) {d : Nat}
    (T' : TaggedLeafTable I copies) : Labels (V := A.1) d :=
  fun (L : Grass A.1 d) => by
    let D := ordinaryObservedDomain I copies U A L
    let f : L.val →ₗ[ZMod 2] D :=
      ((complementInclusion I copies U A).comp L.val.subtype).codRestrict
        D (by
          intro x
          exact (le_sup_right :
            L.val.map (complementInclusion I copies U A) ≤ D)
            ⟨x.1, x.2, rfl⟩)
    exact (T' D).comp f

/-- The ordinary leaf carrier used by the complement density is the leaf
carrier of the changed-ambient star at the corresponding ordinary center. -/
def ordinaryToStarLeaf (A : SideComplement I copies U) {t h : Nat}
    (Kc : CenterInComplement I copies U A t)
    (L : OrdinaryLeaf I copies U A Kc.1 Kc.2 h) :
    LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h) := L

def starToOrdinaryLeaf (A : SideComplement I copies U) {t h : Nat}
    (Kc : CenterInComplement I copies U A t)
    (L : LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h)) :
    OrdinaryLeaf I copies U A Kc.1 Kc.2 h := L

def ordinaryStarLeafEquiv (A : SideComplement I copies U) {t h : Nat}
    (Kc : CenterInComplement I copies U A t) :
    OrdinaryLeaf I copies U A Kc.1 Kc.2 h ≃
      LeafOver (sideCenterToOrdinary I copies U A Kc) (2 * h) where
  toFun := ordinaryToStarLeaf I copies U A Kc
  invFun := starToOrdinaryLeaf I copies U A Kc
  left_inv := by intro L; rfl
  right_inv := by intro L; rfl

theorem transported_center_domain_eq (A : SideComplement I copies U) {t : Nat}
    (Kc : CenterInComplement I copies U A t) :
    (sideCenterToOrdinary I copies U A Kc).val.map
      (complementInclusion I copies U A) =
      Kc.1.1.val.map (E I copies U).subtype := by
  change (Kc.1.1.val.comap A.1.subtype).map
    ((E I copies U).subtype.comp A.1.subtype) =
      Kc.1.1.val.map (E I copies U).subtype
  rw [Submodule.map_comp, Submodule.map_comap_subtype,
    inf_of_le_right Kc.2]

theorem transported_leaf_domain_eq (A : SideComplement I copies U)
    {t h : Nat} (Kc : CenterInComplement I copies U A t)
    (L : OrdinaryLeaf I copies U A Kc.1 Kc.2 h) :
    ordinaryObservedDomain I copies U A L.1 =
      (sideFullToTagged I copies U Kc.1
        (ordinaryToFull I copies U A Kc.1 Kc.2 L)).1 := by
  have hEq :
      ((equationSpan (taggedSource I copies).support U.1).comap
          (E I copies U).subtype).map (E I copies U).subtype =
        equationSpan (taggedSource I copies).support U.1 := by
    have hle : equationSpan (taggedSource I copies).support U.1 ≤
        E I copies U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      exact equationVector_mem_coordinateSpace
        (taggedSource I copies).support U.1 e he
    rw [Submodule.map_comap_subtype]
    exact inf_of_le_right hle
  change equationSpan (taggedSource I copies).support U.1 ⊔
      L.1.val.map ((E I copies U).subtype.comp A.1.subtype) =
    ((equationSpan (taggedSource I copies).support U.1).comap
      (E I copies U).subtype ⊔ L.1.val.map A.1.subtype).map
        (E I copies U).subtype
  rw [Submodule.map_sup, hEq, Submodule.map_comp]

private theorem centerTable_eval_congr {D₁ D₂ : Submodule (ZMod 2)
    (TaggedAmbient I copies)} (C : TaggedCenterTable I copies)
    (hD : D₁ = D₂) (x₁ : D₁) (x₂ : D₂) (hx : (x₁ : TaggedAmbient I copies) = x₂) :
    C D₁ x₁ = C D₂ x₂ := by
  subst D₂
  congr 1
  exact Subtype.ext hx

private theorem leafTable_eval_congr {D₁ D₂ : Submodule (ZMod 2)
    (TaggedAmbient I copies)} (T' : TaggedLeafTable I copies)
    (hD : D₁ = D₂) (x₁ : D₁) (x₂ : D₂) (hx : (x₁ : TaggedAmbient I copies) = x₂) :
    T' D₁ x₁ = T' D₂ x₂ := by
  subst D₂
  congr 1
  exact Subtype.ext hx

/-- The actual complement test includes row right-hand-side checks. Dropping
those checks can only enlarge its pointwise event. The restrictions still use
the same globally predrawn tables, transported to this complement. -/
theorem actual_implies_ordinary_star_accepts (A : SideComplement I copies U)
    {t h k : Nat} (Kc : CenterInComplement I copies U A t)
    (Ls : Fin k → OrdinaryLeaf I copies U A Kc.1 Kc.2 h)
    (C : TaggedCenterTable I copies) (T' : TaggedLeafTable I copies)
    (hactual : fullAccepts I copies U Kc.1 C T'
      (fun i => ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i))) :
    StarAccepts (transportedCenterTable I copies U A C)
      (transportedLeafTable I copies U A T')
      (sideCenterToOrdinary I copies U A Kc)
      (fun i => ordinaryToStarLeaf I copies U A Kc (Ls i)) := by
  classical
  intro i x
  have hacc := hactual i
  have hcenter := transported_center_domain_eq I copies U A Kc
  have hleaf := transported_leaf_domain_eq I copies U A Kc (Ls i)
  -- The second conjunct of the actual test is precisely restriction
  -- agreement after the center and full-leaf domains are identified.
  have hres := hacc.2
  let y : Kc.1.1.val.map (E I copies U).subtype :=
    ⟨(complementInclusion I copies U A ∘ₗ
        (sideCenterToOrdinary I copies U A Kc).val.subtype) x,
      by
        rw [← hcenter]
        exact ⟨x, x.property, rfl⟩⟩
  have heval := LinearMap.congr_fun hres y
  let xC : (sideCenterToOrdinary I copies U A Kc).val.map
      (complementInclusion I copies U A) :=
    ⟨(complementInclusion I copies U A ∘ₗ
        (sideCenterToOrdinary I copies U A Kc).val.subtype) x,
      ⟨x, x.property, rfl⟩⟩
  have hc := centerTable_eval_congr I copies C hcenter xC y (by rfl)
  let L' := ordinaryToStarLeaf I copies U A Kc (Ls i)
  let L := L'.1
  let xL : ↥L.val := ⟨x, L'.2 x.property⟩
  let zStar : ↥(ordinaryObservedDomain I copies U A L) :=
    ⟨(complementInclusion I copies U A ∘ₗ L.val.subtype) xL,
      (le_sup_right : L.val.map (complementInclusion I copies U A) ≤
        ordinaryObservedDomain I copies U A L) ⟨xL, xL.property, rfl⟩⟩
  let D := ordinaryToFull I copies U A Kc.1 Kc.2 (Ls i)
  have hcenterFull : Kc.1.1.val.map (E I copies U).subtype ≤
      D.1.map (E I copies U).subtype :=
    Submodule.map_mono D.2.2.1
  let zActual : (sideFullToTagged I copies U Kc.1 D).1 :=
    Submodule.inclusion hcenterFull y
  have hleafEval := leafTable_eval_congr I copies T' hleaf zStar zActual (by rfl)
  have hcDef : transportedCenterTable I copies U A C
      (sideCenterToOrdinary I copies U A Kc) x = C _ y := by
    change C _ _ = C _ y
    have hx : (((complementInclusion I copies U A ∘ₗ
        (sideCenterToOrdinary I copies U A Kc).val.subtype).codRestrict _
        (by
          intro c
          exact ⟨c, c.property, rfl⟩)) x) = xC := by
      apply Subtype.ext
      rfl
    rw [hx]
    exact hc
  have hlDef : transportedLeafTable I copies U A T'
      L xL = T' _ zActual := by
    change T' _ _ = T' _ zActual
    have hx : (((complementInclusion I copies U A ∘ₗ L.val.subtype).codRestrict _
        (by
          intro c
          exact (le_sup_right : L.val.map (complementInclusion I copies U A) ≤
            ordinaryObservedDomain I copies U A L) ⟨c, c.property, rfl⟩)) xL) = zStar := by
      apply Subtype.ext
      rfl
    rw [hx]
    exact hleafEval
  calc
    transportedCenterTable I copies U A C
        (sideCenterToOrdinary I copies U A Kc) x = C _ y := hcDef
    _ = T' _ zActual := heval.symm
    _ = transportedLeafTable I copies U A T' L xL := hlDef.symm
    _ = transportedLeafTable I copies U A T' L'.1
        ⟨x, L'.2 x.property⟩ := by rfl

end
end PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
