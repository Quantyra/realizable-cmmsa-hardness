import PvNP.RealizableHardness.ActualNumericSideExtension
import PvNP.RealizableHardness.ActualTransverseAgreementLoss

/-! Exact original H-side event ratio on the full decoder's transverse zoom.
The canonical total table is independent of the advice and chosen complement. -/
namespace PvNP.RealizableHardness.ActualHSideFullZoom

open PvNP.RealizableHardness
open ActualTaggedComplementIncidence ActualTaggedMZSideDraw
open ActualTaggedSelectedDecoderBridge ActualTaggedPresentedSelection
open ActualTaggedConcreteStarLaw ActualTaggedFixedCenterGeometry ActualStarSpanIntersection
open ActualRhsFunctionalConstruction ActualNumericSideExtension
open ActualFiniteLaw ActualMaximalPairLadder ActualTransverseAgreementLoss
open GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {N rows : Nat} (I : ActualOccurrenceAllocation.Instance N rows) (copies : Nat)
variable {J : Nat} (U : TaggedGoodU I copies J)
private abbrev E := coordinateSpace (taggedSource I copies).support U.1
private abbrev H :=
  (equationSpan (taggedSource I copies).support U.1).comap (E I copies U).subtype

/-- The canonical global domain label restricted to the actual leaf.
This is total on all leaves, including nontransverse ones. -/
def totalHLeafTable {h : Nat}
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (L : Grass (E I copies U) (2 * h)) : Module.Dual (ZMod 2) L.val :=
  (taggedSelectedDomainTable I copies T s
    ((H I copies U ⊔ L.val).map (E I copies U).subtype)).comp
      (((E I copies U).subtype.comp L.val.subtype).codRestrict
        ((H I copies U ⊔ L.val).map (E I copies U).subtype) (by
          intro x
          exact ⟨x.1, le_sup_right x.2, rfl⟩))

/-- The actual H-window extension as the decoded-pair carrier. -/
def sideDecodedPair {t h : Nat} (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) (g : Module.Dual (ZMod 2) W')
    (K : SideCenter I copies U t)
    (hKW : K.1.val ≤ sideWindow I copies U A W') : DecodedPair K.1 (2 * h) where
  W := sideWindow I copies U A W'
  hQW := hKW
  g := sideExtensionOnWindow I copies U A W' (sideCanonicalRhs I copies U) g

private theorem global_transverse_iff (L : Submodule (ZMod 2) (E I copies U)) :
    L.map (E I copies U).subtype ⊓
        equationSpan (taggedSource I copies).support U.1 = ⊥ ↔
      L ⊓ H I copies U = ⊥ := by
  constructor
  · intro hbot
    apply le_antisymm _ bot_le
    intro x hx
    have hxg : (x : TaggedAmbient I copies) ∈
        L.map (E I copies U).subtype ⊓
          equationSpan (taggedSource I copies).support U.1 :=
      ⟨⟨x, hx.1, rfl⟩, hx.2⟩
    have hx0 := Submodule.mem_bot.mp (hbot ▸ hxg)
    exact Submodule.mem_bot.mpr (Subtype.ext hx0)
  · intro hbot
    apply le_antisymm _ bot_le
    intro x hx
    rcases hx.1 with ⟨y, hy, hxy⟩
    have hyH : y ∈ H I copies U := by
      change ((E I copies U).subtype y) ∈ _
      rw [hxy]
      exact hx.2
    have hy0 : y = 0 := Submodule.mem_bot.mp (hbot ▸ And.intro hy hyH)
    exact Submodule.mem_bot.mpr (by simpa [hy0] using hxy.symm)

private theorem side_full_le_iff {t h : Nat} (K : SideCenter I copies U t)
    (L : SideLeaf I copies U h K) (W : Submodule (ZMod 2) (E I copies U))
    (hHW : H I copies U ≤ W) :
    (sideLeafToFull I copies U K L).1 ≤ W ↔ L.1.val ≤ W := by
  change H I copies U ⊔ L.1.val ≤ W ↔ L.1.val ≤ W
  exact ⟨fun h => le_sup_right.trans h, fun h => sup_le hHW h⟩

private def boundedSideLeafEquiv {t h : Nat} (K : SideCenter I copies U t)
    (P : DecodedPair K.1 (2 * h)) (hHW : H I copies U ≤ P.W) :
    {L : SideLeaf I copies U h K // (sideLeafToFull I copies U K L).1 ≤ P.W} ≃
      {z : Zoom K.1 P // z.1.val ⊓ H I copies U = ⊥} where
  toFun L := ⟨⟨L.1.1, L.1.2.2,
    (side_full_le_iff I copies U K L.1 P.W hHW).mp L.2⟩,
      (global_transverse_iff I copies U L.1.1.val).mp L.1.2.1⟩
  invFun z := ⟨⟨z.1.1,
    (global_transverse_iff I copies U z.1.1.val).mpr z.2, z.1.2.1⟩,
      (side_full_le_iff I copies U K _ P.W hHW).mpr z.1.2.2⟩
  left_inv L := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Pointwise agreement is the same equality of restricted actual maps. -/
theorem sideRestriction_iff_agreesOn {t h : Nat} (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) (g : Module.Dual (ZMod 2) W')
    (K : SideCenter I copies U t)
    (hKW : K.1.val ≤ sideWindow I copies U A W')
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (L : SideLeaf I copies U h K) (hLW : L.1.val ≤ sideWindow I copies U A W') :
    actualSideLeafRestrictionAgreement I copies U A W' g K L T s ↔
      AgreesOn (totalHLeafTable I copies U T s)
        (P := sideDecodedPair (h := h) I copies U A W' g K hKW) L.1 hLW := by
  constructor
  · intro heq x
    exact (LinearMap.congr_fun heq x).symm
  · intro heq
    ext x
    exact (heq x).symm

/-- The literal original k=1 SideLeaf success/window ratio. -/
def originalSideRestrictionRatio {t h : Nat} (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) (g : Module.Dual (ZMod 2) W')
    (K : SideCenter I copies U t)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    [Nonempty (SideLeaf I copies U h K)] : Rat :=
  eventMass (uniformLaw (Fin 1 → SideLeaf I copies U h K))
      (Finset.univ.filter fun Ls =>
        (sideLeafToFull I copies U K (Ls 0)).1 ≤ sideWindow I copies U A W' ∧
          actualSideLeafRestrictionAgreement I copies U A W' g K (Ls 0) T s) /
    eventMass (uniformLaw (Fin 1 → SideLeaf I copies U h K))
      (Finset.univ.filter fun Ls =>
        (sideLeafToFull I copies U K (Ls 0)).1 ≤ sideWindow I copies U A W')

/-- Original H-side conditioning is exactly transversality conditioning in
the full zoom, on the same total table and actual H-window decoded pair. -/
theorem originalSideRestrictionRatio_eq_transverse {t h : Nat}
    (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) (g : Module.Dual (ZMod 2) W')
    (K : SideCenter I copies U t)
    (hKW : K.1.val ≤ sideWindow I copies U A W')
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    [Nonempty (SideLeaf I copies U h K)] :
    originalSideRestrictionRatio I copies U A W' g K T s =
      transverseAgreement (totalHLeafTable I copies U T s) K.1
        (sideDecodedPair (h := h) I copies U A W' g K hKW) (H I copies U) := by
  let P := sideDecodedPair (h := h) I copies U A W' g K hKW
  let p : SideLeaf I copies U h K → Prop :=
    fun L => (sideLeafToFull I copies U K L).1 ≤ P.W
  let q : SideLeaf I copies U h K → Prop :=
    fun L => actualSideLeafRestrictionAgreement I copies U A W' g K L T s
  let B := {L : SideLeaf I copies U h K // p L}
  let G := {z : Zoom K.1 P // z.1.val ⊓ H I copies U = ⊥}
  let e : B ≃ G := boundedSideLeafEquiv I copies U K P le_sup_left
  let aq : Zoom K.1 P → Prop :=
    fun z => AgreesOn (totalHLeafTable I copies U T s) z.1 z.2.2
  have hpq (L : B) : q L.1 ↔ aq (e L).1 :=
    sideRestriction_iff_agreesOn I copies U A W' g K hKW T s L.1
      ((side_full_le_iff I copies U K L.1 P.W le_sup_left).mp L.2)
  let es : {L : B // q L.1} ≃ {z : G // aq z.1} := Equiv.subtypeEquiv e hpq
  have hratio : originalSideRestrictionRatio I copies U A W' g K T s =
      (Fintype.card {L : B // q L.1} : Rat) / Fintype.card B := by
    unfold originalSideRestrictionRatio
    rw [finOne_uniformEventMass_eq_original_count,
      finOne_uniformEventMass_eq_original_count]
    have hn : (Fintype.card (SideLeaf I copies U h K) : Rat) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := SideLeaf I copies U h K)
    rw [div_div_div_cancel_right₀ hn]
    change (Fintype.card {L : SideLeaf I copies U h K // p L ∧ q L} : Rat) /
      Fintype.card B = _
    rw [Fintype.card_congr (subtypeAndEquiv p q)]
  have hden : (transverseZoom K.1 P (H I copies U)).card = Fintype.card G := by
    exact (Fintype.card_subtype _).symm
  have hnum : ((transverseZoom K.1 P (H I copies U)).filter aq).card =
      Fintype.card {z : G // aq z.1} := by
    unfold transverseZoom
    rw [Finset.filter_filter, ← Fintype.card_subtype]
    exact Fintype.card_congr
      (subtypeAndEquiv (fun z : Zoom K.1 P => z.1.val ⊓ H I copies U = ⊥) aq)
  rw [hratio, Fintype.card_congr es, Fintype.card_congr e]
  change _ = ((transverseZoom K.1 P (H I copies U)).filter aq).card /
    ((transverseZoom K.1 P (H I copies U)).card : Rat)
  rw [hnum, hden]

/-- Full agreement pays the actual H-side leaf-transversality loss. -/
theorem full_agreement_ge_original_side_sub_dyadic {t h : Nat}
    (A : SideComplement I copies U)
    (W' : Submodule (ZMod 2) A.1) (g : Module.Dual (ZMod 2) W')
    (K : SideCenter I copies U t)
    (hKW : K.1.val ≤ sideWindow I copies U A W')
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    [Nonempty (SideLeaf I copies U h K)]
    (ht : t ≤ 2 * h)
    (hd : 2 * h ≤ Module.finrank (ZMod 2) (sideWindow I copies U A W'))
    (hbd : 1 ≤ 2 * h - t)
    (hslack : Module.finrank (ZMod 2) (H I copies U) + (2 * h - t) + 1 ≤
      Module.finrank (ZMod 2) (sideWindow I copies U A W') - t) :
    originalSideRestrictionRatio I copies U A W' g K T s -
      1 / (2 : Rat)^(Module.finrank (ZMod 2) (sideWindow I copies U A W') - t -
        Module.finrank (ZMod 2) (H I copies U) - (2 * h - t) - 1) ≤
      agreement (totalHLeafTable I copies U T s) K.1
        (sideDecodedPair (h := h) I copies U A W' g K hKW) := by
  rw [originalSideRestrictionRatio_eq_transverse I copies U A W' g K hKW T s]
  exact full_agreement_ge_transverse_sub_dyadic
    (totalHLeafTable I copies U T s) K.1
    (sideDecodedPair (h := h) I copies U A W' g K hKW) (H I copies U)
    le_sup_left ((global_transverse_iff I copies U K.1.val).mp K.2)
    ht hd hbd hslack

end
end PvNP.RealizableHardness.ActualHSideFullZoom
