import PvNP.RealizableHardness.ActualFunctionalAssignmentAcceptance
import PvNP.RealizableHardness.ActualRestrictedVisiblePair
import PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss
import PvNP.RealizableHardness.ActualMaximalPairLadder

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
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
variable (copies : Nat) {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1

private theorem retainedVisible_bijective (s : ActualRowDraw I copies U) :
    Function.Bijective (actualRetainedToVisible I copies J U s) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val h
  · intro y
    have hy : y.1 ∈ (actualRetained I copies U s).map (E I copies U).subtype := by
      rw [← actualRetained_map_visible I copies J U s]
      exact y.2
    rcases Submodule.mem_map.mp hy with ⟨x, hx, hxy⟩
    refine ⟨x, hx⟩, ?_
    apply Subtype.ext
    exact hxy

/-- The actual retained carrier and the visible coordinate carrier are
linearly equivalent. -/
noncomputable def retainedVisibleEquiv (s : ActualRowDraw I copies U) :
    actualRetained I copies U s ≃ₗ[ZMod 2]
      visibleCoordinateSpace I copies (retainedVariables I copies J U s) :=
  LinearEquiv.ofBijective (actualRetainedToVisible I copies J U s)
    (retainedVisible_bijective I copies J U s)

theorem retainedVisible_finrank (s : ActualRowDraw I copies U) :
    Module.finrank (ZMod 2) (actualRetained I copies U s) =
      Module.finrank (ZMod 2)
        (visibleCoordinateSpace I copies (retainedVariables I copies J U s)) :=
  (retainedVisibleEquiv I copies J U s).finrank_eq.symm

/-- Each actual row retains at least one variable; hence dim V >= J. -/
theorem visible_finrank_lower (s : ActualRowDraw I copies U) :
    J ≤ Module.finrank (ZMod 2)
      (visibleCoordinateSpace I copies (retainedVariables I copies J U s)) := by
  rw [← retainedVisible_finrank I copies J U s,
    actualRetained_finrank I copies J U s]
  have hd := dropCount_le (rowDrawEquiv I copies U s)
  omega

private def retainedPreimageEquiv (s : ActualRowDraw I copies U)
    (W : Submodule (ZMod 2) (E I copies U))
    (hW : W ≤ actualRetained I copies U s) :
    (W.comap (actualRetained I copies U s).subtype) ≃ₗ W where
  toFun x := ⟨(actualRetained I copies U s).subtype x.1, x.2⟩
  invFun x := ⟨⟨x.1, hW x.2⟩, x.2⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

private def retainedPreimageGrass (s : ActualRowDraw I copies U) {a : Nat}
    (Q : Grass (E I copies U) a)
    (hQ : Q.val ≤ actualRetained I copies U s) :
    Grass (actualRetained I copies U s) a :=
  ⟨Q.val.comap (actualRetained I copies U s).subtype,
    (retainedPreimageEquiv I copies J U s Q.val hQ).finrank_eq.trans Q.property⟩

/-- Push a Grassmann object and decoded pair through a linear equivalence. -/
def pushGrass {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a : Nat} (Q : Grass A a) : Grass B a :=
  ⟨Q.val.map (e : A →[ZMod 2] B), by
    rw [e.finrank_map_eq]
    exact Q.property⟩

def pushPair {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B] [Finite B]
    (e : A ≃ₗ[ZMod 2] B) {a d : Nat} (Q : Grass A a)
    (P : DecodedPair Q d) : DecodedPair (pushGrass e Q) d where
  W := P.W.map (e : A →[ZMod 2] B)
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
    (Q : Grass (E I copies U) a) (P : DecodedPair Q d)
    (hQV : Q.val ≤ actualRetained I copies U s) :
    DecodedPair (retainedPreimageGrass I copies J U s Q hQV) d := by
  let R := restrictedPair I copies J U Q P s hQV
  let hR : R.W ≤ actualRetained I copies U s := inf_le_right
  exact {
    W := R.W.comap (actualRetained I copies U s).subtype
    hQW := Submodule.comap_mono R.hQW
    g := R.g.comp (retainedPreimageEquiv I copies J U s R.W hR).toLinearMap
  }

theorem actualRetainedRestrictedPair_apply {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s)
    (x : (actualRetainedRestrictedPair I copies J U s Q P hQV).W) :
    (actualRetainedRestrictedPair I copies J U s Q P hQV).g x =
      (restrictedPair I copies J U Q P s hQV).g
        ⟨(actualRetained I copies U s).subtype x.1, x.2⟩ := rfl

/-- The analysis pair in the visible ambient is the exact image of the
restricted original decoder. Its visible table is defined only from X. -/
noncomputable def actualVisibleRestrictedPair {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s) :
    DecodedPair
      (pushGrass (retainedVisibleEquiv I copies J U s)
        (retainedPreimageGrass I copies J U s Q hQV)) d :=
  pushPair (retainedVisibleEquiv I copies J U s)
    (retainedPreimageGrass I copies J U s Q hQV)
    (actualRetainedRestrictedPair I copies J U s Q P hQV)

theorem actualVisibleRestrictedPair_preserves_functional {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies U) a)
    (P : DecodedPair Q d) (hQV : Q.val ≤ actualRetained I copies U s)
    (x : (actualRetainedRestrictedPair I copies J U s Q P hQV).W) :
    (actualVisibleRestrictedPair I copies J U s Q P hQV).g
      ((retainedVisibleEquiv I copies J U s).submoduleMap
        (actualRetainedRestrictedPair I copies J U s Q P hQV).W x) =
      (restrictedPair I copies J U Q P s hQV).g
        ⟨(actualRetained I copies U s).subtype x.1, x.2⟩ := by
  rw [pushPair_preserves_functional]
  exact actualRetainedRestrictedPair_apply I copies J U s Q P hQV x

/-- Rank stability is W + V = E. The codimension of W intersect V, measured
inside V through its preimage, is exactly the original codimension in E. -/
theorem actual_restriction_codim_eq {a d : Nat}
    (s : ActualRowDraw I copies U) (Q : Grass (E I copies U) a)
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
    (Q : Grass (E I copies U) a) (P : DecodedPair Q d)
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
        (pushGrass (retainedVisibleEquiv I copies J U s Q hQV)) Pvis ∧
      codim Pvis.W + j ≤ codim
        (actualVisibleRestrictedPair I copies J U s Q P hQV).W ∧
      j ≤ r ∧
      C / (4 * (5 : ℚ) ^ r) ≤ agreement T
        (pushGrass (retainedVisibleEquiv I copies J U s Q hQV)) Pvis := by
  have hsame := actual_restriction_codim_eq I copies J U s Q P hrank
  have hmap := (retainedVisibleEquiv I copies J U s).finrank_map_eq
    ((actualRetainedRestrictedPair I copies J U s Q P hQV).W)
  have hambient := (retainedVisibleEquiv I copies J U s).finrank_eq
  have hcodim' : codim
      (actualVisibleRestrictedPair I copies J U s Q P hQV).W ≤ r := by
    unfold codim at hcodim hsame ⊢
    rw [hambient, ← hmap, ← hsame]
    exact hcodim
  exact maximalPairLadder_from_quarter T
    (pushGrass (retainedVisibleEquiv I copies J U s)
      (retainedPreimageGrass I copies J U s Q hQV))
    (actualVisibleRestrictedPair I copies J U s Q P hQV) r C hC hcodim' hstart

end PvNP.RealizableHardness.ActualVisibleAmbientLadder