import PvNP.RealizableHardness.ActualTaggedVertexPhysicalLaw

/-! The physical verifier's target leaf may be represented by any transverse
presentation of the same full vertex. The center and raw tables stay fixed. -/

namespace PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualTaggedPresentedSelection
open PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge
open PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
open PvNP.RealizableHardness.ActualFiniteLaw
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)

def replaceTargetLeaves {J t h k : Nat}
    (z : TaggedPresentedStar I copies J t h k)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (hrows : ∀ i, (vs i).U = z.q.U)
    (hcenter : ∀ i, z.q.K ≤ (vs i).domain I copies) :
    TaggedPresentedStar I copies J t h k :=
  { q := z.q, leaves := vs, sameRows := hrows, center_le := hcenter }

def replaceTargetChoice {J t h k : Nat}
    (z : TaggedPresentedStar I copies J t h k)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (hD : ∀ i, (z.leaves i).domain I copies = (vs i).domain I copies)
    (r : TaggedIndependentChoice I copies z.leaves) :
    TaggedIndependentChoice I copies vs :=
  fun i => ⟨(r i).1, (r i).2.trans
    ((taggedClassOf_eq_iff I copies).mpr
      (tagged_rel_of_domain_eq I copies (z.leaves i) (vs i) (hD i)))⟩

def replaceTargetChoiceEquiv {J t h k : Nat}
    (z : TaggedPresentedStar I copies J t h k)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (hD : ∀ i, (z.leaves i).domain I copies = (vs i).domain I copies) :
    TaggedIndependentChoice I copies z.leaves ≃
      TaggedIndependentChoice I copies vs where
  toFun := replaceTargetChoice I copies z vs hD
  invFun := fun s i => ⟨(s i).1, (s i).2.trans
    ((taggedClassOf_eq_iff I copies).mpr
      (tagged_rel_of_domain_eq I copies (vs i) (z.leaves i) (hD i).symm))⟩
  left_inv r := by funext i; apply Subtype.ext; rfl
  right_inv s := by funext i; apply Subtype.ext; rfl

theorem taggedPhysicalAccepts_replaceTargetLeaves {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (hrows : ∀ i, (vs i).U = z.q.U)
    (hcenter : ∀ i, z.q.K ≤ (vs i).domain I copies)
    (hD : ∀ i, (z.leaves i).domain I copies = (vs i).domain I copies)
    (r : TaggedIndependentChoice I copies z.leaves) :
    taggedPhysicalAccepts I copies C T z r ↔
      taggedPhysicalAccepts I copies C T
        (replaceTargetLeaves I copies z vs hrows hcenter)
        (replaceTargetChoice I copies z vs hD r) := by
  have hlabel (i : Fin k) :
      ((taggedIndependentLabels I copies T z.leaves r) i).1.comp
          (Submodule.inclusion (z.center_le i)) =
        ((taggedIndependentLabels I copies T vs
          (replaceTargetChoice I copies z vs hD r)) i).1.comp
          (Submodule.inclusion (hcenter i)) := by
    have hc := taggedTransportedRawLabel_domain_coherent I copies
      (r i).1 (z.leaves i) (vs i)
      (taggedRepresentativeRel I copies (z.leaves i) (r i))
      (taggedRepresentativeRel I copies (vs i)
        (replaceTargetChoice I copies z vs hD r i))
      (hD i)
      (taggedValidifiedRawLabel I copies T (r i).1).1
      (taggedValidifiedRawLabel I copies T (r i).1).2
    ext x
    have hx := LinearMap.congr_fun hc
      (⟨x.1, hcenter i x.2⟩ : (vs i).domain I copies)
    exact hx
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · exact hp.1
    · intro i
      exact (hlabel i).symm.trans (hp.2 i)
  · intro hp
    refine ⟨?_, ?_⟩
    · exact hp.1
    · intro i
      exact (hlabel i).trans (hp.2 i)

theorem taggedPhysicalMean_replaceTargetLeaves {J t h k : Nat}
    (C : TaggedCenterTable I copies)
    (T : TaggedRawVertexTable I copies J h)
    (z : TaggedPresentedStar I copies J t h k)
    (vs : Fin k → TaggedPresentedLeaf I copies J h)
    (hrows : ∀ i, (vs i).U = z.q.U)
    (hcenter : ∀ i, z.q.K ≤ (vs i).domain I copies)
    (hD : ∀ i, (z.leaves i).domain I copies = (vs i).domain I copies) :
    uniformMean (TaggedIndependentChoice I copies z.leaves)
      (fun r => if taggedPhysicalAccepts I copies C T z r then 1 else 0) =
    uniformMean (TaggedIndependentChoice I copies vs)
      (fun s => if taggedPhysicalAccepts I copies C T
        (replaceTargetLeaves I copies z vs hrows hcenter) s then 1 else 0) := by
  classical
  let e := replaceTargetChoiceEquiv I copies z vs hD
  calc
    _ = uniformMean (TaggedIndependentChoice I copies z.leaves)
        (fun r => if taggedPhysicalAccepts I copies C T
          (replaceTargetLeaves I copies z vs hrows hcenter) (e r) then 1 else 0) := by
            apply congrArg (uniformMean (TaggedIndependentChoice I copies z.leaves))
            funext r
            exact if_congr
              (taggedPhysicalAccepts_replaceTargetLeaves I copies C T z vs
                hrows hcenter hD r) rfl rfl
    _ = _ := tagged_uniformMean_equiv e
      (fun s => if taggedPhysicalAccepts I copies C T
        (replaceTargetLeaves I copies z vs hrows hcenter) s then 1 else 0)

end
end PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant
