import PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finiteness

/-! Exact graph-map counts for complements containing a fixed subspace.
These are used by the tagged ordered star collision comparison. -/

namespace PvNP.RealizableHardness.ActualTaggedConditionalGraphCount

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedFixedCenterGeometry
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedPresentationFiberAudit
open PvNP.RealizableHardness.ActualStarSpanIntersection

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _
local instance (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.GlobalVar :=
  inferInstance

/-- In one sampled tagged question all leaves share the same row set, so
class collision is exactly equality of their full presented domains. -/
theorem tagged_class_eq_iff_domain_eq_sameU {J h : Nat}
    (P Q : TaggedPresentedLeaf I copies J h) (hU : P.U = Q.U) :
    taggedClassOf I copies P = taggedClassOf I copies Q ↔
      P.domain I copies = Q.domain I copies := by
  rw [taggedClassOf_eq_iff I copies]
  constructor
  · intro hRel
    change P.domain I copies ⊔ Q.H I copies =
      Q.domain I copies ⊔ P.H I copies at hRel
    have hH : P.H I copies = Q.H I copies :=
      congrArg (equationSpan (taggedSource I copies).support) hU
    have hleft : P.domain I copies ⊔ Q.H I copies = P.domain I copies :=
      sup_eq_left.mpr (by rw [← hH]; exact P.H_le_domain I copies)
    have hright : Q.domain I copies ⊔ P.H I copies = Q.domain I copies :=
      sup_eq_left.mpr (by rw [hH]; exact Q.H_le_domain I copies)
    exact hleft.symm.trans (hRel.trans hright)
  · intro hD
    exact tagged_rel_of_domain_eq I copies P Q hD

noncomputable local instance conditionalSubmoduleFintype
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Fintype (Submodule (ZMod 2) V) := by
  letI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun L => (L : Set V)) SetLike.coe_injective
  exact Fintype.ofFinite _

private noncomputable def vanishOnCenterEquivQuotient
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (K : Submodule (ZMod 2) V) :
    {f : V →ₗ[ZMod 2] W // K ≤ LinearMap.ker f} ≃
      ((V ⧸ K) →ₗ[ZMod 2] W) where
  toFun f := K.liftQ f.1 f.2
  invFun g := ⟨g.comp K.mkQ, by
    intro x hx
    have hx0 : K.mkQ x = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hx
    simpa [LinearMap.mem_ker, hx0]⟩
  left_inv f := by
    apply Subtype.ext
    exact K.liftQ_mkQ f.1 f.2
  right_inv g := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := K.mkQ_surjective x
    simp [Submodule.liftQ_mkQ]

private noncomputable instance finiteLinearMapFintype
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Fintype (V →ₗ[ZMod 2] W) := by
  letI : Finite (V →ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : V →ₗ[ZMod 2] W => fun x : V => f x) (by
      intro f g hfg
      apply LinearMap.ext
      intro x
      exact congrFun hfg x)
  exact Fintype.ofFinite _

/-- A lift graph can vary on the quotient of the transverse increment by
the fixed center. This is the exact count needed for each fixed domain:
`2^(J*(2*h-t))` once the tagged dimensions are substituted. -/
private theorem card_maps_vanishing_on_center
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (K : Submodule (ZMod 2) V) :
    Fintype.card {f : V →ₗ[ZMod 2] W // K ≤ LinearMap.ker f} =
      2 ^ ((Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) K) *
        Module.finrank (ZMod 2) W) := by
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  letI : Fintype (V ⧸ K) := Fintype.ofFinite _
  have hrank : Module.finrank (ZMod 2) (V ⧸ K) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) K :=
    Nat.eq_sub_of_add_eq K.finrank_quotient_add_finrank
  calc
    Fintype.card {f : V →ₗ[ZMod 2] W // K ≤ LinearMap.ker f} =
        Fintype.card ((V ⧸ K) →ₗ[ZMod 2] W) :=
      Fintype.card_congr (vanishOnCenterEquivQuotient K)
    _ = 2 ^ ((Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) K) *
        Module.finrank (ZMod 2) W) := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2)
        (V := (V ⧸ K) →ₗ[ZMod 2] W),
        Module.finrank_linearMap (R := ZMod 2) (S := ZMod 2)
          (M := V ⧸ K) (N := W), hrank]
      norm_num

/-- A fixed center lies in a complement precisely when the graph map
vanishes on that center. The center here is the actual embedded subspace,
not a resampled projection. -/
private theorem center_le_complement_iff
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (H C : Submodule (ZMod 2) V) (h : IsCompl H C)
    (K : Submodule (ZMod 2) C)
    (L : {M : Submodule (ZMod 2) V // IsCompl H M}) :
    K.map C.subtype ≤ L.1 ↔
      K ≤ LinearMap.ker (complementEquivLinearMap H C h L) := by
  change K.map C.subtype ≤ L.1 ↔
    K ≤ LinearMap.ker ((H.isComplEquivProj L).1.comp C.subtype)
  rw [Submodule.map_le_iff_le_comap, LinearMap.ker_comp]
  simp only [Submodule.coe_isComplEquivProj_apply,
    Submodule.ker_projectionOnto]

/-- Conditional complements containing one fixed center correspond to
linear graph maps that vanish there. -/
private noncomputable def conditionalComplementEquivVanish
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (H C : Submodule (ZMod 2) V) (h : IsCompl H C)
    (K : Submodule (ZMod 2) C) :
    {L : {M : Submodule (ZMod 2) V // IsCompl H M} //
      K.map C.subtype ≤ L.1} ≃
      {f : C →ₗ[ZMod 2] H // K ≤ LinearMap.ker f} where
  toFun L := ⟨complementEquivLinearMap H C h L.1,
    (center_le_complement_iff H C h K L.1).mp L.2⟩
  invFun f := ⟨(complementEquivLinearMap H C h).symm f.1,
    (center_le_complement_iff H C h K
      ((complementEquivLinearMap H C h).symm f.1)).mpr (by
        simpa only [Equiv.apply_symm_apply] using f.2)⟩
  left_inv L := by
    apply Subtype.ext
    exact (complementEquivLinearMap H C h).symm_apply_apply L.1
  right_inv f := by
    apply Subtype.ext
    exact (complementEquivLinearMap H C h).apply_symm_apply f.1

/-- Exact count of complements containing a fixed transverse center.
This becomes `2^(J*(2*h-t))` for the tagged star dimensions. -/
theorem card_conditional_complements
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H C : Submodule (ZMod 2) V) (h : IsCompl H C)
    (K : Submodule (ZMod 2) C) :
    Fintype.card {L : {M : Submodule (ZMod 2) V // IsCompl H M} //
      K.map C.subtype ≤ L.1} =
      2 ^ ((Module.finrank (ZMod 2) C - Module.finrank (ZMod 2) K) *
        Module.finrank (ZMod 2) H) := by
  letI : Finite C := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite H := Finite.of_injective Subtype.val Subtype.val_injective
  calc
    Fintype.card {L : {M : Submodule (ZMod 2) V // IsCompl H M} //
        K.map C.subtype ≤ L.1} =
        Fintype.card {f : C →ₗ[ZMod 2] H // K ≤ LinearMap.ker f} :=
      Fintype.card_congr (conditionalComplementEquivVanish H C h K)
    _ = 2 ^ ((Module.finrank (ZMod 2) C - Module.finrank (ZMod 2) K) *
        Module.finrank (ZMod 2) H) :=
      card_maps_vanishing_on_center K


end
end PvNP.RealizableHardness.ActualTaggedConditionalGraphCount
