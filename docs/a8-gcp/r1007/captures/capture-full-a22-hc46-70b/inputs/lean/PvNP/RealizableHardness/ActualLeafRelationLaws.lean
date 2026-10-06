import PvNP.RealizableHardness.ActualLeafTransport

namespace PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualStarQuestionSupport

variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

theorem row_private_outside_two_questions
    (row : E → Finset X)
    (hthree : ∀ e, (row e).card = 3)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ row f).card ≤ 1)
    (U₁ U₂ U₃ : Finset E)
    (hU₁ : GoodQuestion row U₁)
    (hU₂ : GoodQuestion row U₂)
    (hU₃ : GoodQuestion row U₃)
    (e : E) (he₂ : e ∈ U₂) (he₁ : e ∉ U₁) (he₃ : e ∉ U₃) :
    ∃ x ∈ row e,
      x ∉ questionSupport row U₁ ∧
      x ∉ questionSupport row U₃ ∧
      x ∉ questionSupport row (U₂.erase e) := by
  classical
  let A := row e ∩ questionSupport row U₁
  let B := row e ∩ questionSupport row U₃
  have hA : A.card ≤ 1 :=
    excluded_row_overlap_le_one row hlinear U₁ hU₁ e he₁
  have hB : B.card ≤ 1 :=
    excluded_row_overlap_le_one row hlinear U₃ hU₃ e he₃
  have hAB : (A ∪ B).card ≤ 2 := by
    exact (Finset.card_union_le A B).trans (by omega)
  have hnsub : ¬ row e ⊆ A ∪ B := by
    intro hsub
    have hc := Finset.card_le_card hsub
    rw [hthree e] at hc
    omega
  obtain ⟨x, hxrow, hxAB⟩ := Finset.not_subset.mp hnsub
  have hx₁ : x ∉ questionSupport row U₁ := by
    intro hx
    apply hxAB
    exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxrow, hx⟩)
  have hx₃ : x ∉ questionSupport row U₃ := by
    intro hx
    apply hxAB
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxrow, hx⟩)
  refine ⟨x, hxrow, hx₁, hx₃, ?_⟩
  intro hxerase
  rw [questionSupport, Finset.mem_biUnion] at hxerase
  obtain ⟨f, hf, hxf⟩ := hxerase
  have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
  have hf₂ : f ∈ U₂ := (Finset.mem_erase.mp hf).2
  have hdis : Disjoint (row e) (row f) := hU₂.1 he₂ hf₂ (Ne.symm hfe)
  exact (Finset.disjoint_left.mp hdis) hxrow hxf

theorem equationSpan_inf_sup_coordinateSpace_le
    (row : E → Finset X)
    (hthree : ∀ e, (row e).card = 3)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ row f).card ≤ 1)
    (U₁ U₂ U₃ : Finset E)
    (hU₁ : GoodQuestion row U₁)
    (hU₂ : GoodQuestion row U₂)
    (hU₃ : GoodQuestion row U₃) :
    equationSpan row U₂ ⊓
        (coordinateSpace row U₁ ⊔ coordinateSpace row U₃) ≤
      equationSpan row U₁ ⊔ equationSpan row U₃ := by
  classical
  intro v hv
  rcases (Finsupp.mem_span_image_iff_linearCombination (R := ZMod 2)).mp hv.1 with
    ⟨l, hlU₂, hlcomb⟩
  have hcoeff : ∀ e ∈ U₂, e ∉ U₁ → e ∉ U₃ → l e = 0 := by
    intro e he₂ he₁ he₃
    obtain ⟨x, hxe, hx₁, hx₃, hxrest⟩ :=
      row_private_outside_two_questions row hthree hlinear
        U₁ U₂ U₃ hU₁ hU₂ hU₃ e he₂ he₁ he₃
    have hxother : ∀ f ∈ U₂, f ≠ e → equationVector row f x = 0 := by
      intro f hf hfe
      have hxf : x ∉ row f := by
        intro hxin
        apply hxrest
        exact Finset.mem_biUnion.mpr
          ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hxin⟩
      simp [equationVector, hxf]
    have hrepr : (∑ f ∈ U₂, l f • equationVector row f) = v := by
      simpa only [Finsupp.linearCombination_apply_of_mem_supported (ZMod 2) hlU₂]
        using hlcomb
    have heval := congrFun hrepr x
    have hleft : (∑ f ∈ U₂, l f • equationVector row f) x = l e := by
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single e]
      · simp [equationVector, hxe]
      · intro f hf hfe
        simp [hxother f hf hfe]
      · intro he'
        exact (he' he₂).elim
    have hvx : v x = 0 := by
      rcases Submodule.mem_sup.mp hv.2 with ⟨a, ha, b, hb, hab⟩
      rw [← hab]
      simp only [Pi.add_apply]
      rw [ha x hx₁, hb x hx₃, add_zero]
    rw [hleft, hvx] at heval
    exact heval
  have hlrestricted : l ∈ Finsupp.supported (ZMod 2) (ZMod 2)
      (↑(U₂ ∩ (U₁ ∪ U₃)) : Set E) := by
    rw [Finsupp.mem_supported']
    intro e heinter
    by_cases he₂ : e ∈ U₂
    · have hout : e ∉ U₁ ∪ U₃ := by
        intro hin
        exact heinter (Finset.mem_inter.mpr ⟨he₂, hin⟩)
      exact hcoeff e he₂
        (fun h => hout (Finset.mem_union_left _ h))
        (fun h => hout (Finset.mem_union_right _ h))
    · exact (Finsupp.mem_supported' (ZMod 2) l).mp hlU₂ e (by simpa using he₂)
  have hvsmall : v ∈ equationSpan row (U₂ ∩ (U₁ ∪ U₃)) := by
    apply (Finsupp.mem_span_image_iff_linearCombination (R := ZMod 2)).mpr
    exact ⟨l, hlrestricted, hlcomb⟩
  apply (Submodule.span_le.mpr ?_) hvsmall
  rintro _ ⟨e, he, rfl⟩
  rcases Finset.mem_inter.mp he with ⟨_, heout⟩
  rcases Finset.mem_union.mp heout with he₁ | he₃
  · exact Submodule.mem_sup_left
      (equationVector_mem_equationSpan row U₁ e he₁)
  · exact Submodule.mem_sup_right
      (equationVector_mem_equationSpan row U₃ e he₃)

end PvNP.RealizableHardness.ActualStarSpanIntersection

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section

local instance leafRelationLawsRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

theorem actual_equationSpan_inf_sup_coordinateSpace_le
    {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (U₁ U₂ U₃ : Finset I.RowId)
    (hU₁ : GoodQuestion I.support U₁)
    (hU₂ : GoodQuestion I.support U₂)
    (hU₃ : GoodQuestion I.support U₃) :
    equationSpan I.support U₂ ⊓
        (coordinateSpace I.support U₁ ⊔ coordinateSpace I.support U₃) ≤
      equationSpan I.support U₁ ⊔ equationSpan I.support U₃ := by
  exact equationSpan_inf_sup_coordinateSpace_le I.support I.support_card
    I.pair_intersection U₁ U₂ U₃ hU₁ hU₂ hU₃

namespace PresentedLeaf

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

theorem Rel.refl (P : PresentedLeaf I J h) : P.Rel P := by
  rfl

theorem Rel.symm {P Q : PresentedLeaf I J h} (hPQ : P.Rel Q) : Q.Rel P := by
  exact Eq.symm hPQ

private theorem domain_le_endpoint_common
    (P Q R : PresentedLeaf I J h)
    (hPQ : P.Rel Q) (hQR : Q.Rel R) :
    P.domain ≤ R.domain ⊔ P.H := by
  intro x hx
  have hxPQ : x ∈ Q.domain ⊔ P.H := by
    rw [← hPQ]
    exact Submodule.mem_sup_left hx
  rcases Submodule.mem_sup.mp hxPQ with ⟨q, hqQ, p, hpP, hqpx⟩
  have hqQR : q ∈ R.domain ⊔ Q.H := by
    rw [← hQR]
    exact Submodule.mem_sup_left hqQ
  rcases Submodule.mem_sup.mp hqQR with ⟨r, hrR, k, hkQ, hrkq⟩
  have hqPcoord : q ∈ coordinateSpace I.support P.U := by
    have hxcoord := P.domain_le_coordinateSpace hx
    have hpcoord := P.H_le_coordinateSpace hpP
    have hsub := (coordinateSpace I.support P.U).sub_mem hxcoord hpcoord
    convert hsub using 1
    rw [← hqpx]
    abel
  have hrRcoord : r ∈ coordinateSpace I.support R.U :=
    R.domain_le_coordinateSpace hrR
  have hkOuter : k ∈
      coordinateSpace I.support P.U ⊔ coordinateSpace I.support R.U := by
    apply Submodule.mem_sup.mpr
    refine ⟨q, hqPcoord, -r, (coordinateSpace I.support R.U).neg_mem hrRcoord, ?_⟩
    rw [← hrkq]
    abel
  have hkEnds : k ∈ P.H ⊔ R.H :=
    actual_equationSpan_inf_sup_coordinateSpace_le I P.U Q.U R.U
      P.goodU Q.goodU R.goodU ⟨hkQ, hkOuter⟩
  rcases Submodule.mem_sup.mp hkEnds with ⟨p', hp'P, r', hr'R, hp'r'k⟩
  apply Submodule.mem_sup.mpr
  refine ⟨r + r', R.domain.add_mem hrR (R.H_le_domain hr'R),
    p' + p, P.H.add_mem hp'P hpP, ?_⟩
  rw [← hqpx, ← hrkq, ← hp'r'k]
  abel

theorem Rel.trans (P Q R : PresentedLeaf I J h) :
    P.Rel Q → Q.Rel R → P.Rel R := by
  intro hPQ hQR
  apply le_antisymm
  · apply sup_le
    · exact domain_le_endpoint_common P Q R hPQ hQR
    · exact le_sup_of_le_left R.H_le_domain
  · apply sup_le
    · exact domain_le_endpoint_common R Q P (Rel.symm hQR) (Rel.symm hPQ)
    · exact le_sup_of_le_left P.H_le_domain

end PresentedLeaf

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

theorem transportCompatible_refl
    (P : PresentedLeaf I J h)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    TransportCompatible P P (PresentedLeaf.Rel.refl P) f f := by
  obtain ⟨F, hF, _⟩ :=
    actual_existsUnique_gluedLeafRhsFunctional I P P.U P.goodU f hf
  refine ⟨F, hF.1, hF.2, ?_⟩
  have hincl :
      Submodule.inclusion (P.rightDomain_le_common P (PresentedLeaf.Rel.refl P)) =
        Submodule.inclusion le_sup_left := by
    apply LinearMap.ext
    intro z
    rfl
  rw [hincl]
  exact hF.1

theorem transportedLabel_identity_canonical
    (P : PresentedLeaf I J h)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    transportedLabel P P (PresentedLeaf.Rel.refl P) f hf = f := by
  exact (transportedLabel_unique P P (PresentedLeaf.Rel.refl P)
    f hf f (transportCompatible_refl P f hf)).symm

theorem transportCompatible_symm
    (P Q : PresentedLeaf I J h)
    (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f)
    (g : RawLeafLabel I Q.domain)
    (hfg : TransportCompatible P Q hPQ f g) :
    TransportCompatible Q P (PresentedLeaf.Rel.symm hPQ) g f := by
  obtain ⟨F, hFleft, hFrhs, hFright⟩ := hfg
  have hback : Q.domain ⊔ P.H ≤ P.domain ⊔ Q.H := by
    rw [hPQ]
  let G : ↥(Q.domain ⊔ P.H) →ₗ[ZMod 2] ZMod 2 :=
    F.comp (Submodule.inclusion hback)
  refine ⟨G, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hFright z
    simpa only [G, LinearMap.comp_apply, Submodule.inclusion_apply] using hz
  · intro e he
    let z : P.domain :=
      ⟨equationVector I.support e,
        P.H_le_domain
          (equationVector_mem_equationSpan I.support P.U e he)⟩
    have hz := LinearMap.congr_fun hFleft z
    change F ⟨equationVector I.support e, _⟩ = I.rowRhs e
    exact hz.trans (hf e he)
  · apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hFleft z
    simpa only [G, LinearMap.comp_apply, Submodule.inclusion_apply] using hz

theorem transportedLabel_inverse_canonical
    (P Q : PresentedLeaf I J h)
    (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    transportedLabel Q P (PresentedLeaf.Rel.symm hPQ)
        (transportedLabel P Q hPQ f hf)
        (transportedLabel_respectsAt P Q hPQ f hf) = f := by
  have hcompat := transportCompatible_symm P Q hPQ f hf
    (transportedLabel P Q hPQ f hf)
    (transportedLabel_compatible P Q hPQ f hf)
  exact (transportedLabel_unique Q P (PresentedLeaf.Rel.symm hPQ)
    (transportedLabel P Q hPQ f hf)
    (transportedLabel_respectsAt P Q hPQ f hf) f hcompat).symm

theorem transportedLabel_proof_irrel
    (P Q : PresentedLeaf I J h)
    (hPQ₁ hPQ₂ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf₁ : RespectsAt P rfl f)
    (hf₂ : RespectsAt P rfl f) :
    transportedLabel P Q hPQ₁ f hf₁ =
      transportedLabel P Q hPQ₂ f hf₂ := by
  congr

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
