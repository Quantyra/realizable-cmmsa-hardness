import PvNP.RealizableHardness.ActualLeafTransportCoherence

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section

local instance presentationDescentRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

/-- Equation span of any presentation of `v`; uniqueness is `vertexH_eq_of_presentation`. -/
noncomputable def vertexH (v : LeafVertex I J h) :
    Submodule (ZMod 2) (I.GlobalVar → ZMod 2) :=
  (Classical.choose v.property).H

theorem vertexH_eq_of_presentation
    (v : LeafVertex I J h)
    (P : PresentedLeaf I J h)
    (hD : P.domain = v.1) :
    vertexH v = P.H :=
  H_eq_of_domain_eq (Classical.choose v.property) P
    ((Classical.choose_spec v.property).trans hD.symm)

namespace LeafVertex

def Rel (v w : LeafVertex I J h) : Prop :=
  v.1 ⊔ vertexH w = w.1 ⊔ vertexH v

theorem Rel_iff_presented
    (v w : LeafVertex I J h)
    (P Q : PresentedLeaf I J h)
    (hP : P.domain = v.1)
    (hQ : Q.domain = w.1) :
    Rel v w ↔ P.Rel Q := by
  have hv : vertexH v = P.H := vertexH_eq_of_presentation v P hP
  have hw : vertexH w = Q.H := vertexH_eq_of_presentation w Q hQ
  simp only [Rel, PresentedLeaf.Rel, hP, hQ, hv, hw]

theorem Rel.refl (v : LeafVertex I J h) : Rel v v := by
  rfl

theorem Rel.symm {v w : LeafVertex I J h} (hvw : Rel v w) : Rel w v :=
  Eq.symm hvw

theorem Rel.trans {u v w : LeafVertex I J h}
    (huv : Rel u v) (hvw : Rel v w) : Rel u w := by
  let P := Classical.choose u.property
  let Q := Classical.choose v.property
  let R := Classical.choose w.property
  have hP : P.domain = u.1 := Classical.choose_spec u.property
  have hQ : Q.domain = v.1 := Classical.choose_spec v.property
  have hR : R.domain = w.1 := Classical.choose_spec w.property
  exact (Rel_iff_presented u w P R hP hR).mpr
    (PresentedLeaf.Rel.trans P Q R
      ((Rel_iff_presented u v P Q hP hQ).mp huv)
      ((Rel_iff_presented v w Q R hQ hR).mp hvw))

end LeafVertex

def packagedLabel
    (P : PresentedLeaf I J h)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    LeafLabel ⟨P.domain, ⟨P, rfl⟩⟩ :=
  ⟨f, ⟨P, rfl, hf⟩⟩

theorem packagedLabel_toFun
    (P : PresentedLeaf I J h)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    (packagedLabel P f hf).1 = f :=
  rfl

theorem LeafLabel.eq_of_toFun
    {v : LeafVertex I J h} {φ ψ : LeafLabel v} :
    φ.1 = ψ.1 → φ = ψ :=
  Subtype.ext

private def recastLabel
    {D D' : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hDD : D = D') (f : RawLeafLabel I D) :
    RawLeafLabel I D' :=
  f.comp (Submodule.inclusion (le_of_eq hDD.symm))

private theorem recastLabel_toFun
    {D D' : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hDD : D = D') (f : RawLeafLabel I D) (z : D') :
    (recastLabel hDD f).toFun z =
      f.toFun ⟨z.1, le_of_eq hDD.symm z.2⟩ :=
  rfl

private theorem recastLabel_rfl
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (f : RawLeafLabel I D) :
    recastLabel rfl f = f := by
  apply LinearMap.ext
  intro z
  exact (recastLabel_toFun rfl f z).trans (congrArg f.toFun (Subtype.ext rfl))

private theorem recastLabel_proof_irrel
    {D D' : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    {h₁ h₂ : D = D'}
    (f : RawLeafLabel I D) :
    recastLabel h₁ f = recastLabel h₂ f := by
  apply LinearMap.ext
  intro z
  exact (recastLabel_toFun h₁ f z).trans
    ((congrArg f.toFun (Subtype.ext rfl)).trans (recastLabel_toFun h₂ f z).symm)

private theorem recastLabel_trans
    {D₁ D₂ D₃ : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (h12 : D₁ = D₂) (h23 : D₂ = D₃)
    (f : RawLeafLabel I D₁) :
    recastLabel h23 (recastLabel h12 f) = recastLabel (h12.trans h23) f := by
  apply LinearMap.ext
  intro z
  exact (recastLabel_toFun h23 (recastLabel h12 f) z).trans
    ((recastLabel_toFun h12 f _).trans
      ((congrArg f.toFun (Subtype.ext rfl)).trans
        (recastLabel_toFun (h12.trans h23) f z).symm))

private theorem recastLabel_cancel
    {D D' : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hDD : D = D') (f : RawLeafLabel I D) :
    recastLabel hDD.symm (recastLabel hDD f) = f :=
  (recastLabel_trans hDD hDD.symm f).trans
    ((recastLabel_proof_irrel f).trans (recastLabel_rfl f))

private theorem respectsAt_recast_to_rfl
    (P : PresentedLeaf I J h)
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hD : P.domain = D)
    (f : RawLeafLabel I D)
    (hf : RespectsAt P hD f) :
    RespectsAt P rfl (recastLabel hD.symm f) := by
  intro e he
  exact (recastLabel_toFun hD.symm f _).trans
    ((congrArg f.toFun
      (Subtype.ext (id (Eq.refl (equationVector I.support e))))).trans (hf e he))

private theorem respectsAt_recast_from_rfl
    (P : PresentedLeaf I J h)
    {D : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)}
    (hD : P.domain = D)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    RespectsAt P hD (recastLabel hD f) := by
  intro e he
  exact (recastLabel_toFun hD f _).trans
    ((congrArg f.toFun
      (Subtype.ext (id (Eq.refl (equationVector I.support e))))).trans (hf e he))

private theorem respectsAt_recast_domain
    (P Q : PresentedLeaf I J h)
    (hD : P.domain = Q.domain)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    RespectsAt Q rfl (recastLabel hD f) := by
  intro e he
  have hfQ : RespectsAt Q hD.symm f :=
    (respectsAt_iff_of_domain_eq P Q rfl hD.symm f).mp hf
  exact (recastLabel_toFun hD f _).trans
    ((congrArg f.toFun
      (Subtype.ext (id (Eq.refl (equationVector I.support e))))).trans (hfQ e he))

private theorem rel_of_domain_eq
    (P Q : PresentedLeaf I J h)
    (hD : P.domain = Q.domain) :
    P.Rel Q := by
  have hH : P.H = Q.H := H_eq_of_domain_eq P Q hD
  change P.domain ⊔ Q.H = Q.domain ⊔ P.H
  rw [hD, hH]

private theorem transportedLabel_eq_of_label_eq
    (P Q : PresentedLeaf I J h)
    (hPQ : P.Rel Q)
    (f g : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f)
    (hg : RespectsAt P rfl g)
    (hfg : f = g) :
    transportedLabel P Q hPQ f hf = transportedLabel P Q hPQ g hg := by
  cases hfg
  exact transportedLabel_proof_irrel P Q hPQ hPQ f hf hg

private theorem transportedLabel_eq_recast_of_domain_eq
    (P Q : PresentedLeaf I J h)
    (hD : P.domain = Q.domain)
    (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    transportedLabel P Q hPQ f hf = recastLabel hD f := by
  have hH : P.H = Q.H := H_eq_of_domain_eq P Q hD
  have hsup : P.domain ⊔ Q.H = P.domain := by
    rw [← hH]
    exact sup_eq_left.mpr P.H_le_domain
  let F : ↥(P.domain ⊔ Q.H) →ₗ[ZMod 2] ZMod 2 :=
    recastLabel hsup.symm f
  have hcompat : TransportCompatible P Q hPQ f (recastLabel hD f) := by
    refine ⟨F, ?_, ?_, ?_⟩
    · apply LinearMap.ext
      intro z
      exact (recastLabel_toFun hsup.symm f _).trans (congrArg f.toFun (Subtype.ext rfl))
    · intro e he
      have hfQ : RespectsAt Q hD.symm f :=
        (respectsAt_iff_of_domain_eq P Q rfl hD.symm f).mp hf
      exact (recastLabel_toFun hsup.symm f _).trans
        ((congrArg f.toFun
          (Subtype.ext (id (Eq.refl (equationVector I.support e))))).trans (hfQ e he))
    · apply LinearMap.ext
      intro z
      exact (recastLabel_toFun hsup.symm f _).trans
        ((congrArg f.toFun (Subtype.ext rfl)).trans (recastLabel_toFun hD f z).symm)
  exact (transportedLabel_unique P Q hPQ f hf (recastLabel hD f) hcompat).symm

private theorem transportedLabel_independent
    (P P' Q Q' : PresentedLeaf I J h)
    (hP : P.domain = P'.domain)
    (hQ : Q.domain = Q'.domain)
    (hPQ : P.Rel Q)
    (hP'Q' : P'.Rel Q')
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f) :
    recastLabel hQ (transportedLabel P Q hPQ f hf) =
      transportedLabel P' Q' hP'Q' (recastLabel hP f)
        (respectsAt_recast_domain P P' hP f hf) := by
  have hPP' : P.Rel P' := rel_of_domain_eq P P' hP
  have hQQ' : Q.Rel Q' := rel_of_domain_eq Q Q' hQ
  have hPQ' : P.Rel Q' := PresentedLeaf.Rel.trans P Q Q' hPQ hQQ'
  have hPP'Q' : P.Rel Q' := PresentedLeaf.Rel.trans P P' Q' hPP' hP'Q'
  have hseq :
      recastLabel hQ (transportedLabel P Q hPQ f hf) =
        transportedLabel P Q' hPQ' f hf := by
    have hrecast := transportedLabel_eq_recast_of_domain_eq Q Q' hQ hQQ'
      (transportedLabel P Q hPQ f hf)
      (transportedLabel_respectsAt P Q hPQ f hf)
    have hcoh := transportedLabel_coherence P Q Q' hPQ hQQ' f hf
    exact hrecast.symm.trans
      ((transportedLabel_proof_irrel Q Q' hQQ' hQQ'
          (transportedLabel P Q hPQ f hf)
          (transportedLabel_respectsAt P Q hPQ f hf)
          (transportedLabel_respectsAt P Q hPQ f hf)).trans
        (hcoh.trans
          (transportedLabel_proof_irrel P Q' (PresentedLeaf.Rel.trans P Q Q' hPQ hQQ')
            hPQ' f hf hf)))
  have hid : transportedLabel P P' hPP' f hf = recastLabel hP f :=
    transportedLabel_eq_recast_of_domain_eq P P' hP hPP' f hf
  have hcoh' := transportedLabel_coherence P P' Q' hPP' hP'Q' f hf
  have hdirect :
      transportedLabel P Q' hPQ' f hf =
        transportedLabel P' Q' hP'Q' (recastLabel hP f)
          (respectsAt_recast_domain P P' hP f hf) := by
    have hfun :=
      transportedLabel_eq_of_label_eq P' Q' hP'Q'
        (transportedLabel P P' hPP' f hf) (recastLabel hP f)
        (transportedLabel_respectsAt P P' hPP' f hf)
        (respectsAt_recast_domain P P' hP f hf) hid
    exact (transportedLabel_proof_irrel P Q'
        (PresentedLeaf.Rel.trans P P' Q' hPP' hP'Q') hPQ' f hf hf).symm.trans
      (hcoh'.symm.trans hfun)
  exact hseq.trans hdirect

private noncomputable def labelPresentation {v : LeafVertex I J h}
    (φ : LeafLabel v) : PresentedLeaf I J h :=
  Classical.choose φ.property

private theorem labelPresentation_domain {v : LeafVertex I J h}
    (φ : LeafLabel v) :
    (labelPresentation φ).domain = v.1 :=
  Classical.choose (Classical.choose_spec φ.property)

private theorem labelPresentation_respects {v : LeafVertex I J h}
    (φ : LeafLabel v) :
    RespectsAt (labelPresentation φ) (labelPresentation_domain φ) φ.1 :=
  Classical.choose_spec (Classical.choose_spec φ.property)

private noncomputable def vertexPresentation (v : LeafVertex I J h) :
    PresentedLeaf I J h :=
  Classical.choose v.property

private theorem vertexPresentation_domain (v : LeafVertex I J h) :
    (vertexPresentation v).domain = v.1 :=
  Classical.choose_spec v.property

noncomputable def transportedLeafLabel {v w : LeafVertex I J h}
    (hvw : LeafVertex.Rel v w) (φ : LeafLabel v) : LeafLabel w :=
  let P := labelPresentation φ
  let Q := vertexPresentation w
  let hP := labelPresentation_domain φ
  let hQ := vertexPresentation_domain w
  let hPQ := (LeafVertex.Rel_iff_presented v w P Q hP hQ).mp hvw
  let fP := recastLabel hP.symm φ.1
  let hfP := respectsAt_recast_to_rfl P hP φ.1 (labelPresentation_respects φ)
  let gQ := transportedLabel P Q hPQ fP hfP
  ⟨recastLabel hQ gQ, Q, hQ,
    respectsAt_recast_from_rfl Q hQ gQ (transportedLabel_respectsAt P Q hPQ fP hfP)⟩

private theorem transportedLeafLabel_val
    {v w : LeafVertex I J h}
    (hvw : LeafVertex.Rel v w) (φ : LeafLabel v) :
    (transportedLeafLabel hvw φ).1 =
      recastLabel (vertexPresentation_domain w)
        (transportedLabel (labelPresentation φ) (vertexPresentation w)
          ((LeafVertex.Rel_iff_presented v w (labelPresentation φ)
            (vertexPresentation w) (labelPresentation_domain φ)
            (vertexPresentation_domain w)).mp hvw)
          (recastLabel (labelPresentation_domain φ).symm φ.1)
          (respectsAt_recast_to_rfl (labelPresentation φ)
            (labelPresentation_domain φ) φ.1 (labelPresentation_respects φ))) :=
  rfl

private theorem transportedLeafLabel_raw
    {v w : LeafVertex I J h}
    (hvw : LeafVertex.Rel v w)
    (φ : LeafLabel v)
    (P : PresentedLeaf I J h) (hP : P.domain = v.1)
    (Q : PresentedLeaf I J h) (hQ : Q.domain = w.1)
    (hf : RespectsAt P hP φ.1) :
    (transportedLeafLabel hvw φ).1 =
      recastLabel hQ
        (transportedLabel P Q
          ((LeafVertex.Rel_iff_presented v w P Q hP hQ).mp hvw)
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hf)) := by
  have hP0 : (labelPresentation φ).domain = v.1 := labelPresentation_domain φ
  have hQ0 : (vertexPresentation w).domain = w.1 := vertexPresentation_domain w
  have hPP' : (labelPresentation φ).domain = P.domain := hP0.trans hP.symm
  have hQQ' : (vertexPresentation w).domain = Q.domain := hQ0.trans hQ.symm
  have hsrc :
      recastLabel hPP'
          (recastLabel (labelPresentation_domain φ).symm φ.1) =
        recastLabel hP.symm φ.1 :=
    (recastLabel_trans (labelPresentation_domain φ).symm hPP' φ.1).trans
      (recastLabel_proof_irrel φ.1)
  have hindep :=
    transportedLabel_independent (labelPresentation φ) P
      (vertexPresentation w) Q hPP' hQQ'
      ((LeafVertex.Rel_iff_presented v w (labelPresentation φ)
        (vertexPresentation w) (labelPresentation_domain φ)
        (vertexPresentation_domain w)).mp hvw)
      ((LeafVertex.Rel_iff_presented v w P Q hP hQ).mp hvw)
      (recastLabel (labelPresentation_domain φ).symm φ.1)
      (respectsAt_recast_to_rfl (labelPresentation φ)
        (labelPresentation_domain φ) φ.1 (labelPresentation_respects φ))
  have hfun :=
    transportedLabel_eq_of_label_eq P Q
      ((LeafVertex.Rel_iff_presented v w P Q hP hQ).mp hvw)
      (recastLabel hPP' (recastLabel (labelPresentation_domain φ).symm φ.1))
      (recastLabel hP.symm φ.1)
      (respectsAt_recast_domain (labelPresentation φ) P hPP'
        (recastLabel (labelPresentation_domain φ).symm φ.1)
        (respectsAt_recast_to_rfl (labelPresentation φ)
          (labelPresentation_domain φ) φ.1 (labelPresentation_respects φ)))
      (respectsAt_recast_to_rfl P hP φ.1 hf) hsrc
  have hval := transportedLeafLabel_val hvw φ
  have hchain :
      recastLabel hQ0
          (transportedLabel (labelPresentation φ) (vertexPresentation w)
            ((LeafVertex.Rel_iff_presented v w (labelPresentation φ)
              (vertexPresentation w) (labelPresentation_domain φ)
              (vertexPresentation_domain w)).mp hvw)
            (recastLabel (labelPresentation_domain φ).symm φ.1)
            (respectsAt_recast_to_rfl (labelPresentation φ)
              (labelPresentation_domain φ) φ.1 (labelPresentation_respects φ))) =
        recastLabel hQ
          (transportedLabel P Q
            ((LeafVertex.Rel_iff_presented v w P Q hP hQ).mp hvw)
            (recastLabel hP.symm φ.1)
            (respectsAt_recast_to_rfl P hP φ.1 hf)) := by
    let g0 :=
      transportedLabel (labelPresentation φ) (vertexPresentation w)
        ((LeafVertex.Rel_iff_presented v w (labelPresentation φ)
          (vertexPresentation w) (labelPresentation_domain φ)
          (vertexPresentation_domain w)).mp hvw)
        (recastLabel (labelPresentation_domain φ).symm φ.1)
        (respectsAt_recast_to_rfl (labelPresentation φ)
          (labelPresentation_domain φ) φ.1 (labelPresentation_respects φ))
    have hstep := congrArg (recastLabel hQ) (hindep.trans hfun)
    exact (recastLabel_proof_irrel g0).trans
      ((recastLabel_trans hQQ' hQ g0).symm.trans hstep)
  exact hval.trans hchain

theorem transportedLeafLabel_agrees_presented
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain) (hf : RespectsAt P rfl f) :
    let v : LeafVertex I J h := ⟨P.domain, ⟨P, rfl⟩⟩
    let w : LeafVertex I J h := ⟨Q.domain, ⟨Q, rfl⟩⟩
    (transportedLeafLabel (LeafVertex.Rel_iff_presented v w P Q rfl rfl |>.mpr hPQ)
       (packagedLabel P f hf)).1 =
      transportedLabel P Q hPQ f hf := by
  intro v w
  have hraw := transportedLeafLabel_raw
    (LeafVertex.Rel_iff_presented v w P Q rfl rfl |>.mpr hPQ)
    (packagedLabel P f hf) P rfl Q rfl hf
  have hfcast : recastLabel (rfl : P.domain = v.1).symm (packagedLabel P f hf).1 = f := by
    simp only [packagedLabel_toFun]
    exact recastLabel_rfl f
  have hfun :=
    transportedLabel_eq_of_label_eq P Q
      ((LeafVertex.Rel_iff_presented v w P Q rfl rfl).mp
        ((LeafVertex.Rel_iff_presented v w P Q rfl rfl).mpr hPQ))
      (recastLabel (rfl : P.domain = v.1).symm (packagedLabel P f hf).1) f
      (respectsAt_recast_to_rfl P rfl (packagedLabel P f hf).1 hf) hf hfcast
  have hrecast : recastLabel (rfl : Q.domain = w.1)
      (transportedLabel P Q hPQ f hf) = transportedLabel P Q hPQ f hf :=
    recastLabel_rfl (transportedLabel P Q hPQ f hf)
  refine hraw.trans ?_
  refine (congrArg (recastLabel (rfl : Q.domain = w.1))
    ((transportedLabel_proof_irrel P Q
      ((LeafVertex.Rel_iff_presented v w P Q rfl rfl).mp
        ((LeafVertex.Rel_iff_presented v w P Q rfl rfl).mpr hPQ))
      hPQ
      (recastLabel (rfl : P.domain = v.1).symm (packagedLabel P f hf).1)
      (respectsAt_recast_to_rfl P rfl (packagedLabel P f hf).1 hf)
      (respectsAt_recast_to_rfl P rfl (packagedLabel P f hf).1 hf)).trans
      (hfun.trans
        (transportedLabel_proof_irrel P Q hPQ hPQ f hf hf)))).trans
    hrecast

theorem transportedLeafLabel_coherence
    {u v w : LeafVertex I J h}
    (huv : LeafVertex.Rel u v) (hvw : LeafVertex.Rel v w)
    (φ : LeafLabel u) :
    transportedLeafLabel hvw (transportedLeafLabel huv φ) =
      transportedLeafLabel (LeafVertex.Rel.trans huv hvw) φ := by
  apply LeafLabel.eq_of_toFun
  let P := labelPresentation φ
  let Q := vertexPresentation v
  let R := vertexPresentation w
  have hP : P.domain = u.1 := labelPresentation_domain φ
  have hQ : Q.domain = v.1 := vertexPresentation_domain v
  have hR : R.domain = w.1 := vertexPresentation_domain w
  have hfP : RespectsAt P hP φ.1 := labelPresentation_respects φ
  have hrawUV := transportedLeafLabel_raw huv φ P hP Q hQ hfP
  let ψ := transportedLeafLabel huv φ
  have hfQ : RespectsAt Q hQ ψ.1 := by
    have hg : RespectsAt Q rfl
        (transportedLabel P Q
          ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP)) :=
      transportedLabel_respectsAt P Q
        ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
        (recastLabel hP.symm φ.1)
        (respectsAt_recast_to_rfl P hP φ.1 hfP)
    have hψ : ψ.1 = recastLabel hQ
        (transportedLabel P Q
          ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP)) :=
      hrawUV
    rw [hψ]
    exact respectsAt_recast_from_rfl Q hQ _ hg
  have hrawVW := transportedLeafLabel_raw hvw ψ Q hQ R hR hfQ
  have hrawUW := transportedLeafLabel_raw (LeafVertex.Rel.trans huv hvw) φ P hP R hR hfP
  have hfcast :
      recastLabel hQ.symm ψ.1 =
        transportedLabel P Q
          ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP) := by
    rw [hrawUV, recastLabel_cancel]
  have hseq :
      transportedLabel Q R
          ((LeafVertex.Rel_iff_presented v w Q R hQ hR).mp hvw)
          (recastLabel hQ.symm ψ.1)
          (respectsAt_recast_to_rfl Q hQ ψ.1 hfQ) =
        transportedLabel P R
          ((LeafVertex.Rel_iff_presented u w P R hP hR).mp
            (LeafVertex.Rel.trans huv hvw))
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP) := by
    have hfun :=
      transportedLabel_eq_of_label_eq Q R
        ((LeafVertex.Rel_iff_presented v w Q R hQ hR).mp hvw)
        (recastLabel hQ.symm ψ.1)
        (transportedLabel P Q
          ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP))
        (respectsAt_recast_to_rfl Q hQ ψ.1 hfQ)
        (transportedLabel_respectsAt P Q
          ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP))
        hfcast
    have hcoh :=
      transportedLabel_coherence P Q R
        ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
        ((LeafVertex.Rel_iff_presented v w Q R hQ hR).mp hvw)
        (recastLabel hP.symm φ.1)
        (respectsAt_recast_to_rfl P hP φ.1 hfP)
    exact hfun.trans
      (hcoh.trans
        (transportedLabel_proof_irrel P R
          (PresentedLeaf.Rel.trans P Q R
            ((LeafVertex.Rel_iff_presented u v P Q hP hQ).mp huv)
            ((LeafVertex.Rel_iff_presented v w Q R hQ hR).mp hvw))
          ((LeafVertex.Rel_iff_presented u w P R hP hR).mp
            (LeafVertex.Rel.trans huv hvw))
          (recastLabel hP.symm φ.1)
          (respectsAt_recast_to_rfl P hP φ.1 hfP)
          (respectsAt_recast_to_rfl P hP φ.1 hfP)))
  exact hrawVW.trans ((congrArg (recastLabel hR) hseq).trans hrawUW.symm)

theorem repeated_address_rowRhs
    (P Q : PresentedLeaf I J h)
    (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain)
    (hf : RespectsAt P rfl f)
    (e : I.RowId)
    (heP : e ∈ P.U)
    (heQ : e ∈ Q.U) :
    (transportedLabel P Q hPQ f hf).toFun
      ⟨equationVector I.support e,
        Q.H_le_domain (equationVector_mem_equationSpan I.support Q.U e heQ)⟩ =
      I.rowRhs e := by
  have := heP
  exact transportedLabel_respectsAt P Q hPQ f hf e heQ

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
