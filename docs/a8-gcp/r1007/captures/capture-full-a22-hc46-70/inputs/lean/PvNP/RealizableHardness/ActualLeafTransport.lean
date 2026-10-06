import PvNP.RealizableHardness.ActualPresentedLeafGluing

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualPresentedLeafGluing
noncomputable section

local instance leafTransportRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

namespace PresentedLeaf

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

/-- Two presentations admit one-way transport when the source domain together
with the target equation space is the same common ambient submodule as the
target domain together with the source equation space. -/
def Rel (P Q : PresentedLeaf I J h) : Prop :=
  P.domain ⊔ Q.H = Q.domain ⊔ P.H

theorem rightDomain_le_common
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q) :
    Q.domain ≤ P.domain ⊔ Q.H := by
  rw [hPQ]
  exact le_sup_left

end PresentedLeaf

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

/-- A target label is compatible with a source label when both are restrictions
of the unique common functional that preserves the target equations' RHS. -/
def TransportCompatible
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (g : RawLeafLabel I Q.domain) : Prop :=
  ∃ F : ↥(P.domain ⊔ Q.H) →ₗ[ZMod 2] ZMod 2,
    F.comp (Submodule.inclusion le_sup_left) = f ∧
    (∀ e (he : e ∈ Q.U),
      F ⟨equationVector I.support e,
        Submodule.mem_sup_right
          (equationVector_mem_equationSpan I.support Q.U e he)⟩ =
        I.rowRhs e) ∧
    F.comp
      (Submodule.inclusion (P.rightDomain_le_common Q hPQ)) = g

noncomputable def transportedLabel
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    RawLeafLabel I Q.domain :=
  (Classical.choose
      (actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf)).comp
    (Submodule.inclusion (P.rightDomain_le_common Q hPQ))

theorem transportedLabel_respectsAt
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    RespectsAt Q rfl (transportedLabel P Q hPQ f hf) := by
  intro e he
  have hspec := Classical.choose_spec
    (actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf)
  exact hspec.1.2 e he

theorem transportedLabel_compatible
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    TransportCompatible P Q hPQ f (transportedLabel P Q hPQ f hf) := by
  let F := Classical.choose
    (actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf)
  have hspec := Classical.choose_spec
    (actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf)
  refine ⟨F, hspec.1.1, hspec.1.2, ?_⟩
  rfl

theorem transportedLabel_unique
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f)
    (g : RawLeafLabel I Q.domain)
    (hg : TransportCompatible P Q hPQ f g) :
    g = transportedLabel P Q hPQ f hf := by
  obtain ⟨G, hGleft, hGrhs, hGright⟩ := hg
  let F : ↥(P.domain ⊔ Q.H) →ₗ[ZMod 2] ZMod 2 := Classical.choose
    (actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf)
  have hspec := Classical.choose_spec
    (actual_existsUnique_gluedLeafRhsFunctional I P Q.U Q.goodU f hf)
  have hG : G = F :=
    hspec.2 G ⟨hGleft, hGrhs⟩
  have hGcomp :
      G.comp (Submodule.inclusion (P.rightDomain_le_common Q hPQ)) =
        F.comp (Submodule.inclusion (P.rightDomain_le_common Q hPQ)) :=
    congrArg
      (fun K : ↥(P.domain ⊔ Q.H) →ₗ[ZMod 2] ZMod 2 =>
        K.comp (Submodule.inclusion (P.rightDomain_le_common Q hPQ))) hG
  have hFcomp :
      F.comp (Submodule.inclusion (P.rightDomain_le_common Q hPQ)) =
        transportedLabel P Q hPQ f hf := by
    rfl
  exact hGright.symm.trans (hGcomp.trans hFcomp)

theorem existsUnique_compatibleTransport
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    ∃! g : RawLeafLabel I Q.domain,
      RespectsAt Q rfl g ∧ TransportCompatible P Q hPQ f g := by
  refine ⟨transportedLabel P Q hPQ f hf,
    ⟨transportedLabel_respectsAt P Q hPQ f hf,
      transportedLabel_compatible P Q hPQ f hf⟩, ?_⟩
  intro g hg
  exact transportedLabel_unique P Q hPQ f hf g hg.2

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
