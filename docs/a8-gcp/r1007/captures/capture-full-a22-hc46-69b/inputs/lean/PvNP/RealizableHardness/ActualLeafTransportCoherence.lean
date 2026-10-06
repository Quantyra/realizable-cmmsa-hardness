import PvNP.RealizableHardness.ActualLeafRelationLaws

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
open PvNP.RealizableHardness.ActualRhsFunctionalConstruction
open PvNP.RealizableHardness.SubmoduleFunctionalGluing
noncomputable section

variable {X E : Type*} [Fintype X] [Fintype E]
  [DecidableEq X] [DecidableEq E]

private theorem goodQuestion_erase
    (row : E → Finset X) (U : Finset E) (hU : GoodQuestion row U) (e : E) :
    GoodQuestion row (U.erase e) := by
  constructor
  · intro a ha b hb hab
    exact hU.1 (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp hb).2 hab
  · intro a ha b hb hab g x hxa y hyb hxg hyg
    exact hU.2 a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2
      hab g x hxa y hyb hxg hyg

theorem equationVectors_threeGoodQuestions_linearIndependent
    (row : E → Finset X)
    (hthree : ∀ e, (row e).card = 3)
    (hlinear : ∀ e f, e ≠ f → ((row e) ∩ row f).card ≤ 1)
    (U₁ U₂ U₃ : Finset E)
    (hU₁ : GoodQuestion row U₁)
    (hU₂ : GoodQuestion row U₂)
    (hU₃ : GoodQuestion row U₃) :
    LinearIndependent (ZMod 2)
      (fun e : ↥(U₁ ∪ U₂ ∪ U₃) => equationVector row e.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have private_coordinate
      (A B C : Finset E) (hA : GoodQuestion row A)
      (hB : GoodQuestion row B) (hC : GoodQuestion row C)
      (hiA : i.1 ∈ A) :
      ∃ x ∈ row i.1,
        x ∉ questionSupport row (B.erase i.1) ∧
        x ∉ questionSupport row (C.erase i.1) ∧
        x ∉ questionSupport row (A.erase i.1) := by
    exact row_private_outside_two_questions row hthree hlinear
      (B.erase i.1) A (C.erase i.1)
      (goodQuestion_erase row B hB i.1) hA
      (goodQuestion_erase row C hC i.1) i.1 hiA
      (by simp) (by simp)
  obtain ⟨x, hxrow, hxB, hxC, hxA⟩ :
      ∃ x ∈ row i.1,
        x ∉ questionSupport row (U₂.erase i.1) ∧
        x ∉ questionSupport row (U₃.erase i.1) ∧
        x ∉ questionSupport row (U₁.erase i.1) := by
    rcases Finset.mem_union.mp i.2 with hi12 | hi3
    · rcases Finset.mem_union.mp hi12 with hi1 | hi2
      · exact private_coordinate U₁ U₂ U₃ hU₁ hU₂ hU₃ hi1
      · obtain ⟨x, hx, hx1, hx3, hx2⟩ :=
          private_coordinate U₂ U₁ U₃ hU₂ hU₁ hU₃ hi2
        exact ⟨x, hx, hx2, hx3, hx1⟩
    · obtain ⟨x, hx, hx1, hx2, hx3⟩ :=
        private_coordinate U₃ U₁ U₂ hU₃ hU₁ hU₂ hi3
      exact ⟨x, hx, hx2, hx3, hx1⟩
  have hxother : ∀ j : ↥(U₁ ∪ U₂ ∪ U₃), j ≠ i →
      equationVector row j.1 x = 0 := by
    intro j hji
    have hbase : j.1 ≠ i.1 := by
      intro h
      apply hji
      exact Subtype.ext h
    have hnotrow : x ∉ row j.1 := by
      intro hxj
      rcases Finset.mem_union.mp j.2 with hj12 | hj3
      · rcases Finset.mem_union.mp hj12 with hj1 | hj2
        · exact hxA (Finset.mem_biUnion.mpr
            ⟨j.1, Finset.mem_erase.mpr ⟨hbase, hj1⟩, hxj⟩)
        · exact hxB (Finset.mem_biUnion.mpr
            ⟨j.1, Finset.mem_erase.mpr ⟨hbase, hj2⟩, hxj⟩)
      · exact hxC (Finset.mem_biUnion.mpr
          ⟨j.1, Finset.mem_erase.mpr ⟨hbase, hj3⟩, hxj⟩)
    simp [equationVector, hnotrow]
  have hsingle : (∑ j, g j • equationVector row j.1) x = g i := by
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp [equationVector, hxrow]
    · intro j _ hji
      simp [hxother j hji]
    · simp
  have heval := congrFun hsum x
  rw [hsingle] at heval
  simpa using heval

local instance coherenceRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

theorem actual_existsUnique_rhsFunctional_threeGoodQuestions
    {N m J h : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (P Q R : PresentedLeaf I J h) :
    ∃! psi : equationSpan I.support (P.U ∪ Q.U ∪ R.U) →ₗ[ZMod 2] ZMod 2,
      ∀ e (he : e ∈ P.U ∪ Q.U ∪ R.U),
        psi ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support
            (P.U ∪ Q.U ∪ R.U) e he⟩ = I.rowRhs e := by
  let U := P.U ∪ Q.U ∪ R.U
  let v : ↥U → equationSpan I.support U := fun e =>
    ⟨equationVector I.support e.1,
      equationVector_mem_equationSpan I.support U e.1 e.2⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (equationSpan I.support U).subtype
    change LinearIndependent (ZMod 2)
      (fun e : ↥(P.U ∪ Q.U ∪ R.U) => equationVector I.support e.1)
    exact equationVectors_threeGoodQuestions_linearIndependent
      I.support I.support_card I.pair_intersection
      P.U Q.U R.U P.goodU Q.goodU R.goodU
  have hrange : Set.range v =
      (((↑) : equationSpan I.support U → (I.GlobalVar → ZMod 2)) ⁻¹'
        (equationVector I.support '' (U : Set I.RowId))) := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1, e.2, rfl⟩
    · rintro ⟨e, he, hval⟩
      refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      exact hval
  have htop : Submodule.span (ZMod 2)
      (((↑) : equationSpan I.support U → (I.GlobalVar → ZMod 2)) ⁻¹'
        (equationVector I.support '' (U : Set I.RowId))) = ⊤ := by
    exact Submodule.span_span_coe_preimage
      (R := ZMod 2) (M := I.GlobalVar → ZMod 2)
      (s := equationVector I.support '' (U : Set I.RowId))
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    rw [hrange, htop]
  let b : Module.Basis ↥U (ZMod 2) (equationSpan I.support U) :=
    Module.Basis.mk hv hspan
  have hb (e : ↥U) : b e = v e := by simp [b]
  let psi : equationSpan I.support U →ₗ[ZMod 2] ZMod 2 :=
    b.constr (ZMod 2) (fun e => I.rowRhs e.1)
  refine ⟨psi, ?_, ?_⟩
  · intro e he
    change psi (v ⟨e, he⟩) = I.rowRhs e
    rw [← hb]
    exact b.constr_basis (ZMod 2) (fun j => I.rowRhs j.1) ⟨e, he⟩
  · intro phi hphi
    apply b.ext
    intro e
    rw [hb e, hphi e.1 e.2]
    rw [← hb e]
    change I.rowRhs e.1 =
      (b.constr (ZMod 2) (fun j => I.rowRhs j.1)) (b e)
    exact (b.constr_basis (ZMod 2) (fun j => I.rowRhs j.1) e).symm

theorem domain_inf_twoEquationSpans_le
    {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (P Q R : PresentedLeaf I J h) :
    P.domain ⊓ (Q.H ⊔ R.H) ≤ P.H := by
  intro x hx
  rcases Submodule.mem_sup.mp hx.2 with ⟨q, hqQ, r, hrR, hqrx⟩
  have hqOuter : q ∈
      coordinateSpace I.support P.U ⊔ coordinateSpace I.support R.U := by
    apply Submodule.mem_sup.mpr
    refine ⟨x, P.domain_le_coordinateSpace hx.1, -r,
      (coordinateSpace I.support R.U).neg_mem (R.H_le_coordinateSpace hrR), ?_⟩
    rw [← hqrx]
    abel
  have hqEnds : q ∈ P.H ⊔ R.H :=
    actual_equationSpan_inf_sup_coordinateSpace_le I P.U Q.U R.U
      P.goodU Q.goodU R.goodU ⟨hqQ, hqOuter⟩
  rcases Submodule.mem_sup.mp hqEnds with ⟨p, hpP, r', hr'R, hprq⟩
  have hrr' : r + r' ∈ R.H := R.H.add_mem hrR hr'R
  have hxpr : x = p + (r + r') := by
    rw [← hqrx, ← hprq]
    abel
  have hRcoordP : r + r' ∈ coordinateSpace I.support P.U := by
    have hxcoord := P.domain_le_coordinateSpace hx.1
    have hpcoord := P.H_le_coordinateSpace hpP
    have hsub := (coordinateSpace I.support P.U).sub_mem hxcoord hpcoord
    convert hsub using 1
    rw [hxpr]
    abel
  have hsmall : r + r' ∈ equationSpan I.support (R.U ∩ P.U) := by
    rw [← equationSpan_inf_coordinateSpace I.support I.support_card
      I.pair_intersection P.U R.U P.goodU R.goodU]
    exact ⟨hrr', hRcoordP⟩
  have hsmallP : r + r' ∈ P.H := by
    apply (Submodule.span_le.mpr ?_) hsmall
    rintro _ ⟨e, he, rfl⟩
    exact equationVector_mem_equationSpan I.support P.U e
      (Finset.mem_inter.mp he).2
  rw [hxpr]
  exact P.H.add_mem hpP hsmallP

theorem actual_existsUnique_threeWayGluedLeafRhsFunctional
    {N m J h : Nat}
    (I : ActualOccurrenceAllocation.Instance N m)
    (P Q R : PresentedLeaf I J h)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    ∃! F : ↥(P.domain ⊔ (Q.H ⊔ R.H)) →ₗ[ZMod 2] ZMod 2,
      F.comp (Submodule.inclusion le_sup_left) = f ∧
      (∀ e (he : e ∈ Q.U),
        F ⟨equationVector I.support e,
          Submodule.mem_sup_right (Submodule.mem_sup_left
            (equationVector_mem_equationSpan I.support Q.U e he))⟩ =
          I.rowRhs e) ∧
      ∀ e (he : e ∈ R.U),
        F ⟨equationVector I.support e,
          Submodule.mem_sup_right (Submodule.mem_sup_right
            (equationVector_mem_equationSpan I.support R.U e he))⟩ =
          I.rowRhs e := by
  let U := P.U ∪ Q.U ∪ R.U
  obtain ⟨psi, hpsi, hpsiUnique⟩ :=
    actual_existsUnique_rhsFunctional_threeGoodQuestions I P Q R
  have hPspan : P.H ≤ equationSpan I.support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ he), rfl⟩
  have hQspan : Q.H ≤ equationSpan I.support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he), rfl⟩
  have hRspan : R.H ≤ equationSpan I.support U := by
    apply Submodule.span_mono
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Finset.mem_union_right _ he, rfl⟩
  have hQRspan : Q.H ⊔ R.H ≤ equationSpan I.support U :=
    sup_le hQspan hRspan
  let fP : P.H →ₗ[ZMod 2] ZMod 2 :=
    f.comp (Submodule.inclusion P.H_le_domain)
  let psiP : P.H →ₗ[ZMod 2] ZMod 2 :=
    psi.comp (Submodule.inclusion hPspan)
  have hfP : ∀ e (he : e ∈ P.U),
      fP ⟨equationVector I.support e,
        equationVector_mem_equationSpan I.support P.U e he⟩ = I.rowRhs e := by
    intro e he
    exact hf e he
  have hpsiP : ∀ e (he : e ∈ P.U),
      psiP ⟨equationVector I.support e,
        equationVector_mem_equationSpan I.support P.U e he⟩ = I.rowRhs e := by
    intro e he
    exact hpsi e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
  obtain ⟨psi0, _, hpsi0Unique⟩ :=
    actual_existsUnique_rhsFunctional I P.U P.goodU
  have hfpsiP : fP = psiP :=
    (hpsi0Unique fP hfP).trans (hpsi0Unique psiP hpsiP).symm
  let g : ↥(Q.H ⊔ R.H) →ₗ[ZMod 2] ZMod 2 :=
    psi.comp (Submodule.inclusion hQRspan)
  have hagree : ∀ z : ↥(P.domain ⊓ (Q.H ⊔ R.H)),
      f.toFun ⟨z.1, z.2.1⟩ = g ⟨z.1, z.2.2⟩ := by
    intro z
    let zP : P.H := ⟨z.1, domain_inf_twoEquationSpans_le P Q R z.2⟩
    have hz := LinearMap.congr_fun hfpsiP zP
    calc
      f.toFun ⟨z.1, z.2.1⟩ = fP zP := by rfl
      _ = psiP zP := hz
      _ = psi.toFun ⟨z.1, hQRspan z.2.2⟩ := by rfl
  obtain ⟨F, hF, hFUnique⟩ :=
    existsUnique_glue_on_sup P.domain (Q.H ⊔ R.H) f g hagree
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · intro e he
    have hright := LinearMap.congr_fun hF.2
      ⟨equationVector I.support e,
        Submodule.mem_sup_left
          (equationVector_mem_equationSpan I.support Q.U e he)⟩
    exact hright.trans
      (hpsi e (Finset.mem_union_left _ (Finset.mem_union_right _ he)))
  · intro e he
    have hright := LinearMap.congr_fun hF.2
      ⟨equationVector I.support e,
        Submodule.mem_sup_right
          (equationVector_mem_equationSpan I.support R.U e he)⟩
    exact hright.trans (hpsi e (Finset.mem_union_right _ he))
  · intro F' hF'
    let g' : ↥(Q.H ⊔ R.H) →ₗ[ZMod 2] ZMod 2 :=
      F'.comp (Submodule.inclusion le_sup_right)
    let gQ : Q.H →ₗ[ZMod 2] ZMod 2 :=
      g.comp (Submodule.inclusion le_sup_left)
    let gQ' : Q.H →ₗ[ZMod 2] ZMod 2 :=
      g'.comp (Submodule.inclusion le_sup_left)
    let gR : R.H →ₗ[ZMod 2] ZMod 2 :=
      g.comp (Submodule.inclusion le_sup_right)
    let gR' : R.H →ₗ[ZMod 2] ZMod 2 :=
      g'.comp (Submodule.inclusion le_sup_right)
    obtain ⟨q0, _, hqUnique⟩ :=
      actual_existsUnique_rhsFunctional I Q.U Q.goodU
    obtain ⟨r0, _, hrUnique⟩ :=
      actual_existsUnique_rhsFunctional I R.U R.goodU
    have hgQ : ∀ e (he : e ∈ Q.U),
        gQ ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support Q.U e he⟩ = I.rowRhs e := by
      intro e he
      simpa only [gQ, g, LinearMap.comp_apply, Submodule.inclusion_apply] using
        hpsi e (Finset.mem_union_left _ (Finset.mem_union_right _ he))
    have hgQ' : ∀ e (he : e ∈ Q.U),
        gQ' ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support Q.U e he⟩ = I.rowRhs e := by
      intro e he
      simpa only [gQ', g', LinearMap.comp_apply, Submodule.inclusion_apply] using
        hF'.2.1 e he
    have hgR : ∀ e (he : e ∈ R.U),
        gR ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support R.U e he⟩ = I.rowRhs e := by
      intro e he
      simpa only [gR, g, LinearMap.comp_apply, Submodule.inclusion_apply] using
        hpsi e (Finset.mem_union_right _ he)
    have hgR' : ∀ e (he : e ∈ R.U),
        gR' ⟨equationVector I.support e,
          equationVector_mem_equationSpan I.support R.U e he⟩ = I.rowRhs e := by
      intro e he
      simpa only [gR', g', LinearMap.comp_apply, Submodule.inclusion_apply] using
        hF'.2.2 e he
    have hQQ : gQ' = gQ :=
      (hqUnique gQ' hgQ').trans (hqUnique gQ hgQ).symm
    have hRR : gR' = gR :=
      (hrUnique gR' hgR').trans (hrUnique gR hgR).symm
    have hgg : g' = g := by
      apply LinearMap.ext
      intro z
      rcases Submodule.mem_sup.mp z.2 with ⟨q, hq, r, hr, hqrz⟩
      let zq : Q.H := ⟨q, hq⟩
      let zr : R.H := ⟨r, hr⟩
      have hqeq := LinearMap.congr_fun hQQ zq
      have hreq := LinearMap.congr_fun hRR zr
      have hzsub : z =
          (⟨q, Submodule.mem_sup_left hq⟩ : ↥(Q.H ⊔ R.H)) +
          ⟨r, Submodule.mem_sup_right hr⟩ := by
        apply Subtype.ext
        exact hqrz.symm
      rw [hzsub, map_add, map_add]
      exact congrArg₂ (· + ·) hqeq hreq
    apply hFUnique F'
    exact ⟨hF'.1, hgg⟩

theorem transportedLabel_coherence
    {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (P Q R : PresentedLeaf I J h)
    (hPQ : P.Rel Q) (hQR : Q.Rel R)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    transportedLabel Q R hQR
        (transportedLabel P Q hPQ f hf)
        (transportedLabel_respectsAt P Q hPQ f hf) =
      transportedLabel P R (PresentedLeaf.Rel.trans P Q R hPQ hQR) f hf := by
  let hPR : P.Rel R := PresentedLeaf.Rel.trans P Q R hPQ hQR
  obtain ⟨T, hT, _⟩ :=
    actual_existsUnique_threeWayGluedLeafRhsFunctional I P Q R f hf
  have hPQcarrier : P.domain ⊔ Q.H ≤ P.domain ⊔ (Q.H ⊔ R.H) := by
    apply sup_le
    · exact le_sup_left
    · exact le_sup_of_le_right le_sup_left
  have hPRcarrier : P.domain ⊔ R.H ≤ P.domain ⊔ (Q.H ⊔ R.H) := by
    apply sup_le
    · exact le_sup_left
    · exact le_sup_of_le_right le_sup_right
  have hQbig : Q.domain ≤ P.domain ⊔ (Q.H ⊔ R.H) :=
    (P.rightDomain_le_common Q hPQ).trans hPQcarrier
  have hRbig : R.domain ≤ P.domain ⊔ (Q.H ⊔ R.H) :=
    (P.rightDomain_le_common R hPR).trans hPRcarrier
  have hQRcarrier : Q.domain ⊔ R.H ≤ P.domain ⊔ (Q.H ⊔ R.H) :=
    sup_le hQbig (le_sup_of_le_right le_sup_right)
  let qLabel : RawLeafLabel I Q.domain :=
    T.comp (Submodule.inclusion hQbig)
  let rLabel : RawLeafLabel I R.domain :=
    T.comp (Submodule.inclusion hRbig)
  let TPQ : ↥(P.domain ⊔ Q.H) →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hPQcarrier)
  have hcompatPQ : TransportCompatible P Q hPQ f qLabel := by
    refine ⟨TPQ, ?_, ?_, ?_⟩
    · apply LinearMap.ext
      intro z
      have hz := LinearMap.congr_fun hT.1 z
      exact hz
    · intro e he
      exact hT.2.1 e he
    · apply LinearMap.ext
      intro z
      rfl
  have hqCanonical :
      qLabel = transportedLabel P Q hPQ f hf :=
    transportedLabel_unique P Q hPQ f hf qLabel hcompatPQ
  let TPR : ↥(P.domain ⊔ R.H) →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hPRcarrier)
  have hcompatPR : TransportCompatible P R hPR f rLabel := by
    refine ⟨TPR, ?_, ?_, ?_⟩
    · apply LinearMap.ext
      intro z
      have hz := LinearMap.congr_fun hT.1 z
      exact hz
    · intro e he
      exact hT.2.2 e he
    · apply LinearMap.ext
      intro z
      rfl
  have hrDirect :
      rLabel = transportedLabel P R hPR f hf :=
    transportedLabel_unique P R hPR f hf rLabel hcompatPR
  let TQR : ↥(Q.domain ⊔ R.H) →ₗ[ZMod 2] ZMod 2 :=
    T.comp (Submodule.inclusion hQRcarrier)
  have hcompatQR : TransportCompatible Q R hQR
      (transportedLabel P Q hPQ f hf) rLabel := by
    refine ⟨TQR, ?_, ?_, ?_⟩
    · apply LinearMap.ext
      intro z
      have hz := LinearMap.congr_fun hqCanonical z
      exact hz
    · intro e he
      exact hT.2.2 e he
    · apply LinearMap.ext
      intro z
      rfl
  have hrSequential :
      rLabel = transportedLabel Q R hQR
        (transportedLabel P Q hPQ f hf)
        (transportedLabel_respectsAt P Q hPQ f hf) :=
    transportedLabel_unique Q R hQR
      (transportedLabel P Q hPQ f hf)
      (transportedLabel_respectsAt P Q hPQ f hf)
      rLabel hcompatQR
  exact hrSequential.symm.trans hrDirect

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
