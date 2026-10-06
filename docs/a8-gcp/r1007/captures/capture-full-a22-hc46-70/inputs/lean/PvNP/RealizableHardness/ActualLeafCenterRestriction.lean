import PvNP.RealizableHardness.ActualLeafPresentationDescent

namespace PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualStarSpanIntersection
noncomputable section

local instance centerRestrictionRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

variable {N m J h : Nat} {I : ActualOccurrenceAllocation.Instance N m}

/-- A transverse subspace of a leaf domain; `vertexH` is independent of presentation. -/
structure CenterSubspace (v : LeafVertex I J h) (k : Nat) where
  K : Submodule (ZMod 2) (I.GlobalVar → ZMod 2)
  le_domain : K ≤ v.1
  transverse : K ⊓ vertexH v = ⊥
  finrank : Module.finrank (ZMod 2) K = k

def restrictToCenter {v : LeafVertex I J h} {k : Nat}
    (C : CenterSubspace v k) (φ : LeafLabel v) : C.K →ₗ[ZMod 2] ZMod 2 :=
  φ.1.comp (Submodule.inclusion C.le_domain)

theorem restrictToCenter_eq_subtype {v : LeafVertex I J h} {k : Nat}
    (C : CenterSubspace v k) (φ : LeafLabel v) :
    restrictToCenter C φ = φ.1.comp (Submodule.inclusion C.le_domain) :=
  rfl

private def recastToPresentation {v : LeafVertex I J h}
    (P : PresentedLeaf I J h) (hP : P.domain = v.1)
    (f : RawLeafLabel I v.1) :
    RawLeafLabel I P.domain :=
  f.comp (Submodule.inclusion (le_of_eq hP))

private theorem recastToPresentation_toFun {v : LeafVertex I J h}
    (P : PresentedLeaf I J h) (hP : P.domain = v.1)
    (f : RawLeafLabel I v.1) (z : P.domain) :
    (recastToPresentation P hP f).toFun z =
      f.toFun ⟨z.1, le_of_eq hP z.2⟩ :=
  rfl

private theorem respectsAt_recastToPresentation {v : LeafVertex I J h}
    (P : PresentedLeaf I J h) (hP : P.domain = v.1)
    (f : RawLeafLabel I v.1) (hf : RespectsAt P hP f) :
    RespectsAt P rfl (recastToPresentation P hP f) := by
  intro e he
  exact (recastToPresentation_toFun P hP f _).trans
    ((congrArg f.toFun
      (Subtype.ext (id (Eq.refl (equationVector I.support e))))).trans (hf e he))

/-- Unique restriction of the glued functional to the overlap of the two domains. -/
private theorem transportedLabel_toFun_eq_source
    (P Q : PresentedLeaf I J h) (hPQ : P.Rel Q)
    (f : RawLeafLabel I P.domain) (hf : RespectsAt P rfl f)
    (x : I.GlobalVar → ZMod 2)
    (hxP : x ∈ P.domain) (hxQ : x ∈ Q.domain) :
    (transportedLabel P Q hPQ f hf).toFun ⟨x, hxQ⟩ = f.toFun ⟨x, hxP⟩ := by
  obtain ⟨F, hFleft, _, hFright⟩ :=
    transportedLabel_compatible P Q hPQ f hf
  have hsrc := LinearMap.congr_fun hFleft ⟨x, hxP⟩
  have htgt := LinearMap.congr_fun hFright ⟨x, hxQ⟩
  have hincl :
      (Submodule.inclusion (P.rightDomain_le_common Q hPQ) ⟨x, hxQ⟩ :
          ↥(P.domain ⊔ Q.H)) =
        Submodule.inclusion le_sup_left ⟨x, hxP⟩ :=
    Subtype.ext rfl
  exact htgt.symm.trans ((congrArg F hincl).trans hsrc)

private theorem transportedLeafLabel_val
    {v w : LeafVertex I J h}
    (hvw : LeafVertex.Rel v w) (φ : LeafLabel v) :
    (transportedLeafLabel hvw φ).1 =
      (transportedLabel
          (Classical.choose φ.property)
          (Classical.choose w.property)
          ((LeafVertex.Rel_iff_presented v w
              (Classical.choose φ.property)
              (Classical.choose w.property)
              (Classical.choose (Classical.choose_spec φ.property))
              (Classical.choose_spec w.property)).mp hvw)
          (recastToPresentation (Classical.choose φ.property)
            (Classical.choose (Classical.choose_spec φ.property)) φ.1)
          (respectsAt_recastToPresentation (Classical.choose φ.property)
            (Classical.choose (Classical.choose_spec φ.property)) φ.1
            (Classical.choose_spec (Classical.choose_spec φ.property)))).comp
        (Submodule.inclusion
          (le_of_eq (Classical.choose_spec w.property).symm)) :=
  rfl

private theorem transportedLeafLabel_toFun_eq_source
    {v w : LeafVertex I J h}
    (hvw : LeafVertex.Rel v w) (φ : LeafLabel v)
    (x : I.GlobalVar → ZMod 2)
    (hxv : x ∈ v.1) (hxw : x ∈ w.1) :
    (transportedLeafLabel hvw φ).1.toFun ⟨x, hxw⟩ = φ.1.toFun ⟨x, hxv⟩ := by
  let P := Classical.choose φ.property
  let hP : P.domain = v.1 :=
    Classical.choose (Classical.choose_spec φ.property)
  let hf : RespectsAt P hP φ.1 :=
    Classical.choose_spec (Classical.choose_spec φ.property)
  let Q := Classical.choose w.property
  let hQ : Q.domain = w.1 := Classical.choose_spec w.property
  let fP := recastToPresentation P hP φ.1
  let hfP := respectsAt_recastToPresentation P hP φ.1 hf
  let hPQ : P.Rel Q :=
    (LeafVertex.Rel_iff_presented v w P Q hP hQ).mp hvw
  have hxP : x ∈ P.domain := hP.symm ▸ hxv
  have hxQ : x ∈ Q.domain := hQ.symm ▸ hxw
  have hval := transportedLeafLabel_val hvw φ
  have hleft :
      (transportedLeafLabel hvw φ).1.toFun ⟨x, hxw⟩ =
        (transportedLabel P Q hPQ fP hfP).toFun ⟨x, hxQ⟩ := by
    have happly := LinearMap.congr_fun hval ⟨x, hxw⟩
    exact happly.trans (congrArg (transportedLabel P Q hPQ fP hfP).toFun
      (Subtype.ext (id (Eq.refl x))))
  have hmid := transportedLabel_toFun_eq_source P Q hPQ fP hfP x hxP hxQ
  have hright :
      fP.toFun ⟨x, hxP⟩ = φ.1.toFun ⟨x, hxv⟩ :=
    (recastToPresentation_toFun P hP φ.1 ⟨x, hxP⟩).trans
      (congrArg φ.1.toFun (Subtype.ext (id (Eq.refl x))))
  exact hleft.trans (hmid.trans hright)

theorem restrictToCenter_transport
    {v w : LeafVertex I J h} {k : Nat}
    (hvw : LeafVertex.Rel v w)
    (Cv : CenterSubspace v k) (Cw : CenterSubspace w k)
    (hK : Cv.K = Cw.K)
    (φ : LeafLabel v) :
    restrictToCenter Cw (transportedLeafLabel hvw φ) =
      LinearMap.comp (restrictToCenter Cv φ)
        (Submodule.inclusion (le_of_eq hK.symm)) := by
  apply LinearMap.ext
  intro z
  rw [restrictToCenter_eq_subtype, restrictToCenter_eq_subtype]
  have hxw : (z : I.GlobalVar → ZMod 2) ∈ w.1 := Cw.le_domain z.property
  have hxv : (z : I.GlobalVar → ZMod 2) ∈ v.1 := by
    have hzK : (z : I.GlobalVar → ZMod 2) ∈ Cv.K := by
      rw [hK]
      exact z.property
    exact Cv.le_domain hzK
  have hfun :=
    transportedLeafLabel_toFun_eq_source hvw φ (z : I.GlobalVar → ZMod 2) hxv hxw
  exact hfun.trans (congrArg φ.1.toFun (Subtype.ext (id (Eq.refl (z : I.GlobalVar → ZMod 2)))))

end
end PvNP.RealizableHardness.ActualPresentedLeafGluing
