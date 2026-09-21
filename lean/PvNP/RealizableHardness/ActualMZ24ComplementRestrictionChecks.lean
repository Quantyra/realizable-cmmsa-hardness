import PvNP.RealizableHardness.ActualMZ24ComplementRestriction

namespace PvNP.RealizableHardness.ActualMZ24ComplementRestrictionChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

#check relCodim
#check AdviceComplement
#check complementSubspace
#check lift
#check lift_complementSubspace
#check complementInclusion
#check reconstruction_sup
#check complementSubspace_lift
#check complementSubspace_finrank
#check complementSubspace_codim
#check complementSubspace_eq_iff
#check complementSubspace_ne_iff
#check bottomGrass
#check complementContainingGrassEquiv
#check complementContainingGrassEquiv_apply
#check complementContainingGrassEquiv_lift
#check complementToPair
#check complementPair
#check complementZoomEquiv
#check complementQueryInclusion
#check complementQueryInclusion_apply
#check complementTable
#check agreesOn_complement
#check complement_agreement_le

#print axioms reconstruction_sup
#print axioms complementSubspace_finrank
#print axioms complementSubspace_codim
#print axioms complementContainingGrassEquiv
#print axioms complementZoomEquiv
#print axioms agreesOn_complement
#print axioms complement_agreement_le

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a) (C : AdviceComplement Q)
    (W : Submodule (ZMod 2) V) (hQW : Q.val ≤ W) :
    Q.val ⊔ lift C (complementSubspace C W) = W :=
  reconstruction_sup C W hQW

/- Exact odd-b surface: advice dimension one, complement query dimension three,
   and total containing-space dimension four. -/
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q : Grass V 1) (C : AdviceComplement Q) :
    {L : Grass V 4 // Q.val ≤ L.val} ≃ Grass C.A 3 :=
  complementContainingGrassEquiv C 3

/- The containing-space equivalence preserves distinct spaces. -/
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q : Grass V 1) (C : AdviceComplement Q)
    {L₁ L₂ : {L : Grass V 4 // Q.val ≤ L.val}} (h : L₁ ≠ L₂) :
    complementContainingGrassEquiv C 3 L₁ ≠
      complementContainingGrassEquiv C 3 L₂ := by
  intro hEq
  exact h ((complementContainingGrassEquiv C 3).injective hEq)

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (Q : Grass V a) (C : AdviceComplement Q)
    (P : DecodedPair Q d) (had : a ≤ d) :
    Zoom Q P ≃
      Zoom (bottomGrass C.A) (complementPair C P) :=
  complementZoomEquiv C P had

/- Exact odd-b agreement surface: the transported agreement proof is required
   at b=3, with advice dimension one and ambient/query dimension four. -/
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q : Grass V 1) (C : AdviceComplement Q)
    (T : (L : Grass V 4) → Module.Dual (ZMod 2) L.val)
    (P : DecodedPair Q 4) (z : Zoom Q P)
    (hz : AgreesOn (T := T) z.1 z.2.2)
    (had : 1 ≤ 4) :
    AgreesOn (T := complementTable T C had (by norm_num : 1 + 3 = 4))
      (complementZoomEquiv C P had z).1
      (complementZoomEquiv C P had z).2.2 := by
  exact agreesOn_complement T C P had (by norm_num) z hz

def negativeQ : Grass (ZMod 2) 1 :=
  ⟨⊤, by simp⟩

def negativeC : AdviceComplement negativeQ :=
  { A := ⊥
    isCompl := by
      change IsCompl (⊤ : Submodule (ZMod 2) (ZMod 2)) ⊥
      exact isCompl_top_bot }

def negativeP : DecodedPair negativeQ 1 :=
  { W := ⊤
    hQW := by simp [negativeQ]
    g := 0 }

def negativeTable :
    (L : Grass (ZMod 2) 1) → Module.Dual (ZMod 2) L.val :=
  fun L => L.val.subtype

noncomputable instance negativeZoomUnique :
    Unique (Zoom negativeQ negativeP) where
  default :=
    ⟨negativeQ, by simp [negativeQ, negativeP]⟩
  uniq z := by
    apply Subtype.ext
    apply Subtype.ext
    exact le_antisymm (by simp [negativeQ]) z.2.1

noncomputable instance negativeComplementZoomUnique :
    Unique (Zoom (bottomGrass negativeC.A)
      (complementPair negativeC negativeP)) where
  default :=
    ⟨bottomGrass negativeC.A, by
      constructor
      · exact bot_le
      · exact bot_le⟩
  uniq z := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [bottomGrass] using (Submodule.finrank_eq_zero.mp z.1.property)

noncomputable instance negativeAgreeingEmpty :
    IsEmpty (AgreeingZoom negativeTable negativeQ negativeP) where
  false z := by
    have hone : (1 : ZMod 2) ∈ z.1.val.val :=
      z.1.2.1 (by simp [negativeQ])
    let u : z.1.val.val := ⟨(1 : ZMod 2), hone⟩
    have hx := z.2 u
    have hl : negativeTable z.1.val u = 1 := by rfl
    have hr : negativeP.g
        ⟨(u : ZMod 2), z.1.2.2 u.property⟩ = 0 := by rfl
    have h10 : (1 : ZMod 2) = 0 := hl.symm.trans (hx.trans hr)
    exact one_ne_zero h10

noncomputable instance negativeComplementAgreeingUnique :
    Unique (AgreeingZoom
      (complementTable negativeTable negativeC (by norm_num) (by norm_num))
      (bottomGrass negativeC.A) (complementPair negativeC negativeP)) where
  default :=
    ⟨default, by
      intro x
      have hxmem : x.1.1 ∈ (⊥ : Submodule (ZMod 2) (ZMod 2)) :=
        x.1.property
      change x.1.1 = (0 : ZMod 2) at hxmem
      change (x.1.1 : ZMod 2) = 0
      exact hxmem⟩
  uniq z := by
    apply Subtype.ext
    exact Subsingleton.elim _ _

/- Required numerical negative equality fixture: the original table has no
   agreeing zoom, while restriction to the zero-dimensional complement has
   the unique agreeing zoom. -/
example :
    agreement negativeTable negativeQ negativeP = 0 ∧
      agreement
          (complementTable negativeTable negativeC (by norm_num) (by norm_num))
          (bottomGrass negativeC.A) (complementPair negativeC negativeP) = 1 := by
  constructor
  · rw [agreement_eq_fraction_of_nonempty negativeTable negativeQ negativeP
      (by simp [negativeZoomUnique])]
    simp [Fintype.card_eq_zero_iff, negativeAgreeingEmpty]
  · rw [agreement_eq_fraction_of_nonempty
      (complementTable negativeTable negativeC (by norm_num) (by norm_num))
      (bottomGrass negativeC.A) (complementPair negativeC negativeP)
      (by simp [negativeComplementZoomUnique])]
    simp [negativeComplementAgreeingUnique]

end
end PvNP.RealizableHardness.ActualMZ24ComplementRestrictionChecks
