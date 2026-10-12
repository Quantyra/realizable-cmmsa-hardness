import PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance
import PvNP.RealizableHardness.ActualRestrictedVisiblePair
import PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss
import PvNP.RealizableHardness.ActualMaximalPairLadder
import PvNP.RealizableHardness.TripleRestrictionDimension

/-! The ladder is applied only in the visible coordinate ambient. The actual
restricted pair is represented on the retained subspace and then pushed
through its exact linear equivalence with visible coordinates. This module
contains no all-window list bound or outer-law claim. -/
namespace PvNP.RealizableHardness.ActualVisibleAmbientLadder

open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry
open ActualTaggedRowDeletion ActualVisibleQuestionCompletion
open ActualVisibleLeafAgreementLoss ActualRestrictedVisiblePair
open ActualFunctionalAssignmentAcceptance ActualMaximalPairLadder GrassmannCounting
open TripleRestrictionRank TripleRestrictionDimension
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies J : Nat) (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1

private theorem retainedVisible_bijective (s : ActualRowDraw I copies U) :
    Function.Bijective (actualRetainedToVisible I copies U s) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val h
  · intro y
    have hy : y.1 ∈ (actualRetained I copies U s).map (E I copies J U).subtype := by
      rw [← actualRetained_map_visible I copies J U s]
      exact y.2
    rcases Submodule.mem_map.mp hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- The actual retained carrier and the visible coordinate carrier are
linearly equivalent. -/
noncomputable def retainedVisibleEquiv (s : ActualRowDraw I copies U) :
    actualRetained I copies U s ≃ₗ[ZMod 2]
      visibleCoordinateSpace I copies (retainedVariables I copies J U s) :=
  LinearEquiv.ofBijective (actualRetainedToVisible I copies U s)
    (retainedVisible_bijective I copies J U s)

theorem retainedVisible_finrank (s : ActualRowDraw I copies U) :
    Module.finrank (ZMod 2) (actualRetained I copies U s) =
      Module.finrank (ZMod 2)
        (visibleCoordinateSpace I copies (retainedVariables I copies J U s)) :=
  (retainedVisibleEquiv I copies J U s).finrank_eq

/-- Each actual row retains at least one variable; hence dim V >= J. -/
theorem visible_finrank_lower (s : ActualRowDraw I copies U) :
    J ≤ Module.finrank (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s)) := by
  rw [← retainedVisible_finrank I copies J U s,
    actualRetained_finrank I copies U s]
  have hd := dropCount_le (rowDrawEquiv I copies U s)
  omega

private def retainedPreimageEquiv (s : ActualRowDraw I copies U)
    (W : Submodule (ZMod 2) (E I copies J U))
    (hW : W ≤ actualRetained I copies U s) :
    (W.comap (actualRetained I copies U s).subtype) ≃ₗ W where
  toFun x := ⟨(actualRetained I copies U s).subtype x.1, x.2⟩
  invFun x := ⟨⟨x.1, hW x.2⟩, x.2⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

private def retainedPreimageGrass (s : ActualRowDraw I copies U) {a : Nat}
    (Q : Grass (E I copies J U) a)
    (hQ : Q.val ≤ actualRetained I copies U s) :
    Grass (actualRetained I copies U s) a :=
  ⟨Q.val.comap (actualRetained I copies U s).subtype,
    (retainedPreimageEquiv I copies J U s Q.val hQ).finrank_eq.trans Q.property⟩

/-- Push a Grassmann object and decoded pair through a linear equivalence. -/
def pushGrass {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a : Nat} (Q : Grass A a) : Grass B a :=
  ⟨Q.val.map (e : A →ₗ[ZMod 2] B), by
    rw [e.finrank_map_eq]
    exact Q.property⟩

def pushPair {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a d : Nat} (Q : Grass A a)
    (P : DecodedPair Q d) : DecodedPair (pushGrass e Q) d where
  W := P.W.map (e : A →ₗ[ZMod 2] B)
  hQW := Submodule.map_mono P.hQW
  g := P.g.comp (e.submoduleMap P.W).symm.toLinearMap

theorem pushPair_preserves_functional
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a d : Nat} (Q : Grass A a)
    (P : DecodedPair Q d) (x : P.W) :
    (pushPair e Q P).g ((e.submoduleMap P.W) x) = P.g x := by
  simp [pushPair]

/-- Pull the actual restricted pair back to the actual retained carrier.
Every decoder value is the corresponding value of the original restricted
functional. -/
def actualRetainedRestrictedPair {a d : Nat} (s : ActualRowDraw I copies U)
    (Q : Grass (E I copies J U) a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ actualRetained I copies U s) :
    DecodedPair (retainedPreimageGrass I copies J U s Q hQV) d := by
  let R := restrictedPair I copies U Q P s hQV
  let hR : R.W ≤ actualRetained I copies U s := inf_le_right
  exact {
    W := R.W.comap (actualRetained I copies U s).subtype
    hQW := Submodule.comap_mono R.hQW
    g := R.g.comp (retainedPreimageEquiv I copies J U s R.W hR).toLinearMap
  }

theorem actualRetainedRestrictedPair_apply {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies J U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s)
    (x : (actualRetainedRestrictedPair I copies J U s Q P hQV).W) :
    (actualRetainedRestrictedPair I copies J U s Q P hQV).g x =
      (restrictedPair I copies U Q P s hQV).g
        ⟨(actualRetained I copies U s).subtype x.1, x.2⟩ := rfl

/-- The analysis pair in the visible ambient is the exact image of the
restricted original decoder. Its visible table is defined only from X. -/
noncomputable def actualVisibleRestrictedPair {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies J U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s) :
    DecodedPair
      (pushGrass (retainedVisibleEquiv I copies J U s)
        (retainedPreimageGrass I copies J U s Q hQV)) d :=
  pushPair (retainedVisibleEquiv I copies J U s)
    (retainedPreimageGrass I copies J U s Q hQV)
    (actualRetainedRestrictedPair I copies J U s Q P hQV)

theorem actualVisibleRestrictedPair_preserves_functional {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies J U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s)
    (x : (actualRetainedRestrictedPair I copies J U s Q P hQV).W) :
    (actualVisibleRestrictedPair I copies J U s Q P hQV).g
      ((retainedVisibleEquiv I copies J U s).submoduleMap
        (actualRetainedRestrictedPair I copies J U s Q P hQV).W x) =
      (restrictedPair I copies U Q P s hQV).g
        ⟨(actualRetained I copies U s).subtype x.1, x.2⟩ := by
  rw [pushPair_preserves_functional]
  exact actualRetainedRestrictedPair_apply I copies J U s Q P hQV x

/-- Rank stability is W + V = E. The codimension of W intersect V, measured
inside V through its preimage, is exactly the original codimension in E. -/
theorem actual_restriction_codim_eq {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies J U) a)
    (P : DecodedPair Q d)
    (hrank : P.W ⊔ actualRetained I copies U s = ⊤) :
    codim ((P.W ⊓ actualRetained I copies U s).comap
      (actualRetained I copies U s).subtype) = codim P.W := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    P.W (actualRetained I copies U s)
  rw [hrank] at hdim
  have hpre := retainedPreimageEquiv I copies J U s
    (P.W ⊓ actualRetained I copies U s) inf_le_right
  unfold codim
  rw [hpre.finrank_eq]
  omega

/-- The visible-space ladder consumes only X, the visible question, visible
table, and C. Rank stability transfers the original rank cap into this
ambient. The threshold premise is the actual visible-table comparison. -/
theorem actual_visible_ambient_ladder {a d r : Nat}
    (s : ActualRowDraw I copies U)
    (T : (L : Grass
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s)) d) →
        Module.Dual (ZMod 2) L.val)
    (Q : Grass (E I copies J U) a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ actualRetained I copies U s)
    (hrank : P.W ⊔ actualRetained I copies U s = ⊤)
    (C : ℚ) (hC : 0 < C)
    (hstart : C / 4 ≤ agreement T
      (pushGrass (retainedVisibleEquiv I copies J U s)
        (retainedPreimageGrass I copies J U s Q hQV))
      (actualVisibleRestrictedPair I copies J U s Q P hQV))
    (hcodim : codim P.W ≤ r) :
    ∃ j : Nat, ∃ Pvis : DecodedPair
        (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q hQV)) d,
      CompatibleExtension
          (actualVisibleRestrictedPair I copies J U s Q P hQV) Pvis ∧
      MaximalAt T
        (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q hQV))
        (C / (4 * (5 : ℚ) ^ j)) (1 / 5) Pvis ∧
      C / (4 * (5 : ℚ) ^ j) ≤ agreement T
        (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q hQV)) Pvis ∧
      codim Pvis.W + j ≤ codim
        (actualVisibleRestrictedPair I copies J U s Q P hQV).W ∧
      j ≤ r ∧
      C / (4 * (5 : ℚ) ^ r) ≤ agreement T
        (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q hQV)) Pvis := by
  have hsame := actual_restriction_codim_eq I copies J U s Q P hrank
  have hmap := (retainedVisibleEquiv I copies J U s).finrank_map_eq
    ((actualRetainedRestrictedPair I copies J U s Q P hQV).W)
  have hcodim' : codim
      (actualVisibleRestrictedPair I copies J U s Q P hQV).W ≤ r := by
    have heq : codim
        (actualVisibleRestrictedPair I copies J U s Q P hQV).W = codim P.W := by
      unfold codim
      rw [← retainedVisible_finrank I copies J U s, ← hmap]
      exact hsame
    rw [heq]
    exact hcodim
  obtain ⟨j, Pvis, hcomp, hmax, hagree, hprogress, _hcodimP, hj, hterminal⟩ :=
    maximalPairLadder_from_quarter T
      (pushGrass (retainedVisibleEquiv I copies J U s)
        (retainedPreimageGrass I copies J U s Q hQV))
      (actualVisibleRestrictedPair I copies J U s Q P hQV) r C hC hcodim' hstart
  exact ⟨j, Pvis, hcomp, hmax, hagree, hprogress, hj, hterminal⟩

private theorem map_symm_map
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B]
    (e : A ≃ₗ[ZMod 2] B) (W : Submodule (ZMod 2) A) :
    (W.map (e : A →ₗ[ZMod 2] B)).map
      (e.symm : B →ₗ[ZMod 2] A) = W := by
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, hzy⟩
    have hyx : y = e x := by
      have := congrArg e hxy
      simpa using this
    have hzx : e z = e x := hzy.trans hyx
    have hzx' : z = x := e.injective hzx
    simpa [hzx'] using hz
  · intro x hx
    apply Submodule.mem_map.mpr
    refine ⟨e x, ?_, by simp⟩
    apply Submodule.mem_map.mpr
    exact ⟨x, hx, rfl⟩

def pushGrassEquiv
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) (d : Nat) : Grass A d ≃ Grass B d where
  toFun Q := pushGrass e Q
  invFun Q := pushGrass e.symm Q
  left_inv := by
    intro Q
    apply Subtype.ext
    exact map_symm_map e Q.val
  right_inv := by
    intro Q
    apply Subtype.ext
    exact map_symm_map e.symm Q.val

/-- The complete finite leaf fibre maps bijectively through the ambient
linear equivalence, with advice containment and decoder-window containment
both preserved. -/
def pushZoomEquiv
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a d : Nat}
    (Q : Grass A a) (P : DecodedPair Q d) :
    Zoom Q P ≃ Zoom (pushGrass e Q) (pushPair e Q P) where
  toFun z := ⟨(pushGrass e z.1),
    Submodule.map_mono z.2.1, Submodule.map_mono z.2.2⟩
  invFun z := by
    refine ⟨pushGrass e.symm z.1, ?_, ?_⟩
    · have h := Submodule.map_mono z.2.1
      simpa [pushGrass, map_symm_map] using h
    · have h := Submodule.map_mono z.2.2
      simpa [pushGrass, map_symm_map] using h
  left_inv := by
    intro z
    apply Subtype.ext
    exact (pushGrassEquiv e d).left_inv z.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact (pushGrassEquiv e.symm d).left_inv z.1

/-- Pull a table back along the exact image of its leaf. -/
def pullTable
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {d : Nat}
    (T : (L : Grass B d) → Module.Dual (ZMod 2) L.val) :
    (L : Grass A d) → Module.Dual (ZMod 2) L.val :=
  fun L => (T (pushGrass e L)).comp (e.submoduleMap L).toLinearMap

private def embeddedRetainedGrass {d : Nat} (s : ActualRowDraw I copies U)
    (L : Grass (actualRetained I copies U s) d) : Grass (E I copies J U) d :=
  ⟨L.val.map (actualRetained I copies U s).subtype, by
    rw [Submodule.finrank_map_subtype_eq]
    exact L.property⟩

private def embeddedRetainedVector {d : Nat} (s : ActualRowDraw I copies U)
    (L : Grass (actualRetained I copies U s) d) :
    L.val →ₗ[ZMod 2] (embeddedRetainedGrass I copies J U s L).val :=
  ((actualRetained I copies U s).subtype.comp L.val.subtype).codRestrict
    (embeddedRetainedGrass I copies J U s L).val
    (fun x => ⟨x.1, x.2, rfl⟩)

/-- Restrict the global visible-only table to a leaf of the visible coordinate
carrier. Its arguments contain X and fixed global data only. -/
def actualVisibleAmbientTable {h : Nat}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U) :
    (L : Grass (visibleCoordinateSpace I copies
      (retainedVariables I copies J U s)) (2 * h)) →
        Module.Dual (ZMod 2) L.val := by
  intro L
  exact (visibleLeafTable I copies J Traw choice
      (retainedVariables I copies J U s) (L.val.map
        (visibleCoordinateSpace I copies (retainedVariables I copies J U s)).subtype)).comp
    (((visibleCoordinateSpace I copies (retainedVariables I copies J U s)).subtype.comp
      L.val.subtype).codRestrict
        (L.val.map (visibleCoordinateSpace I copies
          (retainedVariables I copies J U s)).subtype)
        (fun x => ⟨x.1, x.2, rfl⟩))

private theorem map_comap_subtype_eq
    {K : Type*} [Semiring K] {F : Type*}
    [AddCommMonoid F] [Module K F] (V W : Submodule K F) (hW : W ≤ V) :
    (W.comap V.subtype).map V.subtype = W := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    change V.subtype x = y at hxy
    rw [← hxy]
    exact hx
  · intro hy
    exact ⟨⟨y, hW hy⟩, hy, rfl⟩

private theorem comap_map_subtype_eq
    {K : Type*} [Semiring K] {F : Type*}
    [AddCommMonoid F] [Module K F] (V : Submodule K F) (W : Submodule K V) :
    (W.map V.subtype).comap V.subtype = W := by
  ext x
  change V.subtype x ∈ W.map V.subtype ↔ x ∈ W
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hEq : y = x := V.injective_subtype hxy
    exact hEq ▸ hy
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- The E-level zoom fibre of the restricted pair is exactly the zoom fibre
inside the retained carrier, via image and preimage under its subtype map. -/
private def retainedZoomEquiv {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies J U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s) :
    Zoom Q (restrictedPair I copies U Q P s hQV) ≃
      Zoom (retainedPreimageGrass I copies J U s Q hQV)
        (actualRetainedRestrictedPair I copies J U s Q P hQV) where
  toFun z := by
    refine ⟨retainedPreimageGrass I copies J U s z.1
      (z.2.2.trans inf_le_right), ?_, ?_⟩
    · exact Submodule.comap_mono z.2.1
    · exact Submodule.comap_mono z.2.2
  invFun z := by
    refine ⟨embeddedRetainedGrass I copies J U s z.1, ?_, ?_⟩
    · have hQ := map_comap_subtype_eq (actualRetained I copies U s) Q.val hQV
      have h := Submodule.map_mono z.2.1
      simpa [retainedPreimageGrass, hQ] using h
    · have hR := map_comap_subtype_eq (actualRetained I copies U s)
        (restrictedPair I copies U Q P s hQV).W inf_le_right
      have h := Submodule.map_mono z.2.2
      simpa [actualRetainedRestrictedPair, embeddedRetainedGrass, hR] using h
  left_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact map_comap_subtype_eq (actualRetained I copies U s) z.1.val
      (z.2.2.trans inf_le_right)
  right_inv := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact comap_map_subtype_eq (actualRetained I copies U s) z.1.val

/-- On a retained-carrier leaf, the visible table is the same global
visibleLeafTable entry whether its vector is read in retained or original
coordinates. -/
theorem actual_visible_table_pullback_apply {h : Nat}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U)
    (L : Grass (actualRetained I copies U s) (2 * h)) (x : L.val) :
    (pullTable (retainedVisibleEquiv I copies J U s)
      (actualVisibleAmbientTable I copies J U Traw choice s) L) x =
    (visibleTableInOriginalCoordinates I copies U Traw choice
      (retainedVariables I copies J U s) (embeddedRetainedGrass I copies J U s L))
        (embeddedRetainedVector I copies J U s L x) := by
  have hcomp :
      ((visibleCoordinateSpace I copies (retainedVariables I copies J U s)).subtype).comp
          (retainedVisibleEquiv I copies J U s).toLinearMap =
        (E I copies J U).subtype.comp (actualRetained I copies U s).subtype := by
    ext v x
    rfl
  have hsub :
      ((L.val.map (retainedVisibleEquiv I copies J U s).toLinearMap).map
          (visibleCoordinateSpace I copies
            (retainedVariables I copies J U s)).subtype) =
        (L.val.map (actualRetained I copies U s).subtype).map
          (E I copies J U).subtype := by
    rw [Submodule.map_map, Submodule.map_map, hcomp]
  simp [pullTable, actualVisibleAmbientTable, embeddedRetainedGrass,
    embeddedRetainedVector, visibleTableInOriginalCoordinates, pushGrass,
    LinearMap.comp_apply, hcomp, hsub]

private def retainedAgreeingZoomEquiv {a d h : Nat}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies J U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s) :
    AgreeingZoom
        (visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s)) Q
        (restrictedPair I copies U Q P s hQV) ≃
      AgreeingZoom
        (pullTable (retainedVisibleEquiv I copies J U s)
          (actualVisibleAmbientTable I copies J U Traw choice s))
        (retainedPreimageGrass I copies J U s Q hQV)
        (actualRetainedRestrictedPair I copies J U s Q P hQV) where
  toFun z := by
    let ez := retainedZoomEquiv I copies J U s Q P hQV
    let zA := ez z.1
    refine ⟨zA, ?_⟩
    intro xA
    have hleaf : embeddedRetainedGrass I copies J U s zA.1 = z.1.1 :=
      congrArg Subtype.val (ez.left_inv z.1)
    let xE : z.1.1.val :=
      ⟨(embeddedRetainedVector I copies J U s zA.1 xA).1, by
        rw [← hleaf]
        exact (embeddedRetainedVector I copies J U s zA.1 xA).property⟩
    let yA : (actualRetainedRestrictedPair I copies J U s Q P hQV).W :=
      ⟨xA.1, zA.2.2 xA.property⟩
    have hsource := z.2 xE
    have htable := actual_visible_table_pullback_apply I copies J U
      Traw choice s zA.1 xA
    have hsource' :
        visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s)
          (embeddedRetainedGrass I copies J U s zA.1)
          (embeddedRetainedVector I copies J U s zA.1 xA) =
        (restrictedPair I copies U Q P s hQV).g
          ⟨(actualRetained I copies U s).subtype yA.1, yA.property⟩ := by
      simpa [hleaf, xE, yA, embeddedRetainedVector] using hsource
    have hlabel := actualRetainedRestrictedPair_apply I copies J U s Q P hQV yA
    change (pullTable (retainedVisibleEquiv I copies J U s)
      (actualVisibleAmbientTable I copies J U Traw choice s) zA.1) xA =
        (actualRetainedRestrictedPair I copies J U s Q P hQV).g yA
    rw [htable]
    exact hsource'.trans hlabel.symm
  invFun z := by
    let ez := retainedZoomEquiv I copies J U s Q P hQV
    let zE := ez.symm z.1
    have hleafA :
        retainedPreimageGrass I copies J U s zE.1.1
          (zE.2.2.trans inf_le_right) = z.1.1 :=
      congrArg Subtype.val (ez.apply_symm_apply z.1)
    have hleafE : embeddedRetainedGrass I copies J U s z.1.1 = zE.1.1 := rfl
    intro xE
    have hLV : zE.1.1.val ≤ actualRetained I copies U s :=
      zE.2.2.trans inf_le_right
    let epre := retainedPreimageEquiv I copies J U s zE.1.1.val hLV
    let x0 := epre.symm xE
    let xA : z.1.1.val := ⟨x0.1, by simpa [hleafA] using x0.property⟩
    let yA : (actualRetainedRestrictedPair I copies J U s Q P hQV).W :=
      ⟨xA.1, z.1.2.2 xA.property⟩
    have htable := actual_visible_table_pullback_apply I copies J U
      Traw choice s (retainedPreimageGrass I copies J U s zE.1.1 hLV) x0
    have htarget := z.2 xA
    have htable' :
        visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s) zE.1.1 xE =
        (pullTable (retainedVisibleEquiv I copies J U s)
          (actualVisibleAmbientTable I copies J U Traw choice s)
          (retainedPreimageGrass I copies J U s zE.1.1 hLV)) x0 := by
      simpa [hleafA, hleafE, xA, x0, epre, embeddedRetainedGrass,
        embeddedRetainedVector] using htable.symm
    have htarget' :
        (pullTable (retainedVisibleEquiv I copies J U s)
          (actualVisibleAmbientTable I copies J U Traw choice s)
          (retainedPreimageGrass I copies J U s zE.1.1 hLV)) x0 =
        (actualRetainedRestrictedPair I copies J U s Q P hQV).g yA := by
      simpa [hleafA, xA, yA] using htarget
    change visibleTableInOriginalCoordinates I copies U Traw choice
      (retainedVariables I copies J U s) zE.1.1 xE =
        (restrictedPair I copies U Q P s hQV).g
          ⟨xE.1, zE.2.2 xE.property⟩
    rw [htable']
    rw [htarget']
    simpa [actualRetainedRestrictedPair_apply, yA, xA, x0, epre,
      embeddedRetainedVector] using rfl
  left_inv := by
    intro z
    apply Subtype.ext
    exact (retainedZoomEquiv I copies J U s Q P hQV).left_inv z.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact (retainedZoomEquiv I copies J U s Q P hQV).right_inv z.1

/-- The agreeing fibres are carried bijectively too: the table is evaluated
on the image leaf and the decoder is transported by the inverse restriction
of the same ambient equivalence. -/
def pushAgreeingZoomEquiv
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a d : Nat}
    (T : (L : Grass B d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass A a) (P : DecodedPair Q d) :
    AgreeingZoom (pullTable e T) Q P ≃
      AgreeingZoom T (pushGrass e Q) (pushPair e Q P) where
  toFun z := by
    refine ⟨(pushZoomEquiv e Q P z.1), ?_⟩
    intro x'
    let x := (e.submoduleMap z.1.1.val).symm x'
    have hmap : (e.submoduleMap z.1.1.val) x = x' := by
      simp [x]
    have hwindow :
        (pushPair e Q P).g
          ⟨x'.1, (Submodule.map_mono z.1.2.2) x'.property⟩ =
        P.g ⟨x.1, z.1.2.2 x.property⟩ := by
      have hfun := pushPair_preserves_functional e Q P
        ⟨x.1, z.1.2.2 x.property⟩
      have hcoord :
          (e.submoduleMap P.W) ⟨x.1, z.1.2.2 x.property⟩ =
            ⟨x'.1, (Submodule.map_mono z.1.2.2) x'.property⟩ := by
        apply Subtype.ext
        simpa [x] using congrArg Subtype.val hmap
      rw [← hcoord]
      exact hfun
    change T (pushGrass e z.1.1) x' =
      (pushPair e Q P).g ⟨x'.1, (Submodule.map_mono z.1.2.2) x'.property⟩
    rw [hwindow]
    rw [← hmap]
    change (pullTable e T z.1.1) x = P.g ⟨x.1, z.1.2.2 x.property⟩
    exact z.2 x
  invFun z := by
    refine ⟨(pushZoomEquiv e Q P).symm z.1, ?_⟩
    intro x
    let z0 := (pushZoomEquiv e Q P).symm z.1
    let x' := (e.submoduleMap z0.1.val) x
    have hz : pushGrass e z0.1 = z.1.1 := by
      exact congrArg Subtype.val ((pushZoomEquiv e Q P).apply_symm_apply z.1)
    let y : z.1.1.val := ⟨x'.1, by simpa [hz] using x'.property⟩
    have hpair :
        (pushPair e Q P).g ⟨x'.1, z.1.2.2 y.property⟩ =
          P.g ⟨x.1, z0.2.2 x.property⟩ := by
      have hfun := pushPair_preserves_functional e Q P
        ⟨x.1, z0.2.2 x.property⟩
      have hcoord :
          (e.submoduleMap P.W) ⟨x.1, z0.2.2 x.property⟩ =
            ⟨x'.1, z.1.2.2 y.property⟩ := by
        apply Subtype.ext
        rfl
      rw [← hcoord]
      exact hfun
    change (pullTable e T z0.1) x = P.g ⟨x.1, z0.2.2 x.property⟩
    rw [← hpair]
    simpa [pullTable, x', hz, y] using z.2 y
  left_inv := by
    intro z
    apply Subtype.ext
    exact (pushZoomEquiv e Q P).left_inv z.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact (pushZoomEquiv e Q P).right_inv z.1

/-- Exact rational agreement, including the zero-fibre convention, is
invariant under the ambient transport. This supplies both the Zoom and
AgreeingZoom cardinality identities rather than assuming agreement transport. -/
theorem pullTable_agreement_eq
    {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a d : Nat}
    (T : (L : Grass B d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass A a) (P : DecodedPair Q d) :
    agreement (pullTable e T) Q P =
      agreement T (pushGrass e Q) (pushPair e Q P) := by
  let ez := pushZoomEquiv e Q P
  let ea := pushAgreeingZoomEquiv e T Q P
  have hden := Fintype.card_congr ez
  have hnum := Fintype.card_congr ea
  by_cases hzero : Fintype.card (Zoom Q P) = 0
  · have hzero' : Fintype.card (Zoom (pushGrass e Q) (pushPair e Q P)) = 0 := by
      exact hden ▸ hzero
    rw [agreement_eq_zero_of_empty (pullTable e T) Q P hzero]
    exact (agreement_eq_zero_of_empty T (pushGrass e Q) (pushPair e Q P) hzero').symm
  · have hzero' : Fintype.card (Zoom (pushGrass e Q) (pushPair e Q P)) ≠ 0 := by
      intro hz
      exact hzero (hden.symm ▸ hz)
    rw [agreement_eq_fraction_of_nonempty (pullTable e T) Q P hzero]
    rw [agreement_eq_fraction_of_nonempty T (pushGrass e Q) (pushPair e Q P) hzero']
    simp [hden, hnum]

/-- The actual visible table and the original-coordinate visible table give
the same exact agreement after restricting the original pair to the retained
carrier and transporting it into visible coordinates. -/
theorem actual_visible_agreement_eq_retained
    {a d h : Nat}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U)
    (Q : Grass (E I copies J U) a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ actualRetained I copies U s) :
    agreement
        (visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s))
        Q (restrictedPair I copies U Q P s hQV) =
      agreement
        (actualVisibleAmbientTable I copies J U Traw choice s)
        (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q hQV))
        (actualVisibleRestrictedPair I copies J U s Q P hQV) := by
  let QA := retainedPreimageGrass I copies J U s Q hQV
  let PA := actualRetainedRestrictedPair I copies J U s Q P hQV
  let e := retainedVisibleEquiv I copies J U s
  have hmid :
      agreement
          (visibleTableInOriginalCoordinates I copies U Traw choice
            (retainedVariables I copies J U s))
          Q (restrictedPair I copies U Q P s hQV) =
        agreement (pullTable e (actualVisibleAmbientTable I copies J U Traw choice s))
          QA PA := by
    let ez := retainedZoomEquiv I copies J U s Q P hQV
    let ea := retainedAgreeingZoomEquiv I copies J U s Traw choice Q P hQV
    have hden := Fintype.card_congr ez
    have hnum := Fintype.card_congr ea
    by_cases hzero : Fintype.card
        (Zoom Q (restrictedPair I copies U Q P s hQV)) = 0
    · have hzero' : Fintype.card (Zoom QA PA) = 0 := hden ▸ hzero
      rw [agreement_eq_zero_of_empty
        (visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s)) Q
        (restrictedPair I copies U Q P s hQV) hzero]
      exact (agreement_eq_zero_of_empty
        (pullTable e (actualVisibleAmbientTable I copies J U Traw choice s)
          ) QA PA hzero').symm
    · have hzero' : Fintype.card (Zoom QA PA) ≠ 0 := by
        intro hz
        exact hzero (hden.symm ▸ hz)
      rw [agreement_eq_fraction_of_nonempty
        (visibleTableInOriginalCoordinates I copies U Traw choice
          (retainedVariables I copies J U s)) Q
        (restrictedPair I copies U Q P s hQV) hzero]
      rw [agreement_eq_fraction_of_nonempty
        (pullTable e (actualVisibleAmbientTable I copies J U Traw choice s)
          ) QA PA hzero']
      simp [hden, hnum]
  calc
    _ = agreement (pullTable e
          (actualVisibleAmbientTable I copies J U Traw choice s)) QA PA := hmid
    _ = agreement (actualVisibleAmbientTable I copies J U Traw choice s)
          (pushGrass e QA) (pushPair e QA PA) :=
        pullTable_agreement_eq e (actualVisibleAmbientTable I copies J U Traw choice s)
          QA PA

/-- The actual row-draw comparison also lands directly in the visible
coordinate ambient. The original side-loss estimate is retained, while its
visible-table endpoint is transported by the exact agreement identity above. -/
theorem actual_visible_agreement_ge_original_sub_dyadic {a h : Nat}
    (Traw : TaggedRawVertexTable I copies J h)
    (choice : TaggedRepresentativeChoice I copies J h)
    (s : ActualRowDraw I copies U)
    (Q : Grass (E I copies J U) a) (P : DecodedPair Q (2 * h))
    (hWV : P.W ≤ actualRetained I copies U s)
    (hQH : Q.val ⊓ originalSideSpace I copies U = ⊥)
    (hQ0 : Q.val ⊓ visibleSideSpace I copies U
      (retainedVariables I copies J U s)
      (retainedVariables_reachable I copies J U s) = ⊥)
    (had : a ≤ 2 * h) (hd : 2 * h ≤ Module.finrank (ZMod 2) P.W)
    (hbd : 1 ≤ 2 * h - a)
    (hslack : J + (2 * h - a) + 1 ≤
      Module.finrank (ZMod 2) P.W - a) :
    agreement (totalHLeafTable I copies U Traw choice) Q P -
        2 / (2 : Rat) ^ (Module.finrank (ZMod 2) P.W - J - 2 * h - 1) ≤
      agreement (actualVisibleAmbientTable I copies J U Traw choice s)
        (pushGrass (retainedVisibleEquiv I copies J U s)
          (retainedPreimageGrass I copies J U s Q P.hQW.trans hWV))
        (actualVisibleRestrictedPair I copies J U s Q P
          P.hQW.trans hWV) := by
  have h := ActualVisibleLeafAgreementLoss.actual_draw_visible_agreement_ge_original_sub_dyadic
    I copies U Traw choice s Q P hWV hQH hQ0 had hd hbd hslack
  simpa only [actual_visible_agreement_eq_retained I copies J U Traw choice s Q P
      (P.hQW.trans hWV)] using h
end
end PvNP.RealizableHardness.ActualVisibleAmbientLadder
