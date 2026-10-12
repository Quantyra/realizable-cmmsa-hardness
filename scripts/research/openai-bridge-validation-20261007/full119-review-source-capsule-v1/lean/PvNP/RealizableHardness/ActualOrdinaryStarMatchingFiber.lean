import PvNP.RealizableHardness.ActualOrdinaryStarSelection
import PvNP.RealizableHardness.ActualStarAffineFunctionalSelectionForce
import PvNP.RealizableHardness.ActualStarJointKernel
import PvNP.RealizableHardness.GrassmannFlagPosterior

namespace PvNP.RealizableHardness.ActualOrdinaryStarMatchingFiber

open GrassmannCounting ActualSourceStarLaw ActualStarJointKernel
open ActualStarAffineFunctionalSelection
open ActualStarAffineFunctionalSelectionForce
open GrassmannFlagPosterior
open scoped DirectSum
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

def MatchesStar {t d m : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m)
    (f : Module.Dual (ZMod 2) V) : Prop :=
  f.comp z.1.val.subtype = C z.1 ∧
    ∀ i : Fin m, f.comp (z.2 i).val.val.subtype = T (z.2 i).val

theorem exists_matching_functional {t d m : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m)
    (hacc : accepts C T z) (hjoint : jointlyDirect z) :
    ∃ f : Module.Dual (ZMod 2) V, MatchesStar C T z f := by
  classical
  let K := z.1.val
  let Q : Fin m → Submodule (ZMod 2) (V ⧸ K) :=
    fun i => LinearMap.range (K.mkQ.domRestrict (z.2 i).val.val)
  obtain ⟨base, hbase⟩ := LinearMap.exists_extend (C z.1)
  let label : ∀ i : Fin m, Q i →ₗ[ZMod 2] ZMod 2 := fun i =>
    leafDifferenceOnQuotient K (z.2 i).val.val (z.2 i).property
      (T (z.2 i).val) base (by rw [hacc i, hbase])
  have hQ : Q = incrementFamily z := by
    funext i
    change LinearMap.range (K.mkQ.domRestrict (z.2 i).val.val) =
      Submodule.map K.mkQ (z.2 i).val.val
    exact LinearMap.range_domRestrict (z.2 i).val.val K.mkQ
  have hj : Function.Injective (DirectSum.coeLinearMap Q) := by
    rw [hQ]
    exact (jointlyDirect_iff_incrementSumMap_injective z).mp hjoint
  have hinst : instDecidableEqFin m =
      (fun a b => Classical.propDecidable (a = b)) := by
    funext a b
    exact Subsingleton.elim _ _
  have hj' : Function.Injective
      (DirectSum.coeLinearMap
        (dec_ι := fun a b => Classical.propDecidable (a = b)) Q) := by
    rw [show (fun a b => Classical.propDecidable (a = b)) =
      instDecidableEqFin m from hinst.symm]
    exact hj
  obtain ⟨ψ, hψ⟩ := jointDirectSumFunctional_glue Q hj' label
  let f : Module.Dual (ZMod 2) V := base + ψ.comp K.mkQ
  refine ⟨f, ?_, ?_⟩
  · ext x
    change base x.val + ψ (K.mkQ x.val) = C z.1 x
    have hx : K.mkQ x.val = 0 := by
      exact (Submodule.Quotient.mk_eq_zero K).mpr x.property
    rw [hx, map_zero, add_zero]
    exact LinearMap.congr_fun hbase x
  · intro i
    ext x
    change base x.val + ψ (K.mkQ x.val) = T (z.2 i).val x
    have hx : K.mkQ x.val ∈ Q i := by
      exact ⟨x, rfl⟩
    have hψx := hψ i ⟨K.mkQ x.val, hx⟩
    change ψ (K.mkQ x.val) = label i ⟨K.mkQ x.val, hx⟩ at hψx
    rw [hψx]
    let q := K.mkQ.domRestrict (z.2 i).val.val
    dsimp [label, leafDifferenceOnQuotient]
    have harg : (⟨K.mkQ x.val, hx⟩ : q.range) =
        ⟨q x, LinearMap.mem_range_self q x⟩ := by
      apply Subtype.ext
      rfl
    simp only [Submodule.mkQ_apply] at harg
    rw [harg, LinearMap.quotKerEquivRange_symm_apply_image]
    simp [Submodule.liftQ_apply, LinearMap.sub_apply, q]

def jointStarSpan {t d m : Nat} (z : StarTuple (V := V) t d m) :
    Submodule (ZMod 2) V :=
  z.1.val ⊔ ⨆ i : Fin m, (z.2 i).val.val

theorem jointStarSpan_finrank {t d m : Nat}
    (z : StarTuple (V := V) t d m)
    (hjoint : jointlyDirect z) :
    Module.finrank (ZMod 2) (jointStarSpan z) = t + m * (d - t) := by
  classical
  let K := z.1.val
  let S := jointStarSpan z
  have hKS : K ≤ S := le_sup_left
  have hmap : S.map K.mkQ = jointIncrementSpan z := by
    change (K ⊔ ⨆ i : Fin m, (z.2 i).val.val).map K.mkQ =
      ⨆ i : Fin m, Submodule.map K.mkQ (z.2 i).val.val
    rw [Submodule.map_sup, Submodule.map_iSup]
    have hzero : K.map K.mkQ = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Submodule.Quotient.mk_eq_zero K).mpr hy
    rw [hzero, bot_sup_eq]
  have hdim := quotient_map_dimension K S hKS
  have hrank : Module.finrank (ZMod 2) (S.map K.mkQ) = m * (d - t) := by
    rw [hmap]
    exact hjoint
  rw [hrank, z.1.property] at hdim
  change Module.finrank (ZMod 2) S = t + m * (d - t)
  omega

private theorem matchesStar_iff_restrict_jointSpan {t d m : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m)
    (f g : Module.Dual (ZMod 2) V) (hg : MatchesStar C T z g) :
    MatchesStar C T z f ↔
      f.comp (jointStarSpan z).subtype = g.comp (jointStarSpan z).subtype := by
  let S := jointStarSpan z
  let D : Module.Dual (ZMod 2) V := f - g
  have hK : z.1.val ≤ S := le_sup_left
  have hL (i : Fin m) : (z.2 i).val.val ≤ S :=
    le_sup_of_le_right (le_iSup (fun i : Fin m => (z.2 i).val.val) i)
  constructor
  · intro hf
    have hkerK : z.1.val ≤ LinearMap.ker D := by
      intro x hx
      have hf' := LinearMap.congr_fun hf.1 ⟨x,hx⟩
      have hg' := LinearMap.congr_fun hg.1 ⟨x,hx⟩
      change f x = C z.1 ⟨x,hx⟩ at hf'
      change g x = C z.1 ⟨x,hx⟩ at hg'
      change D x = 0
      simp [D, hf', hg']
    have hkerL (i : Fin m) : (z.2 i).val.val ≤ LinearMap.ker D := by
      intro x hx
      have hf' := LinearMap.congr_fun (hf.2 i) ⟨x,hx⟩
      have hg' := LinearMap.congr_fun (hg.2 i) ⟨x,hx⟩
      change f x = T (z.2 i).val ⟨x,hx⟩ at hf'
      change g x = T (z.2 i).val ⟨x,hx⟩ at hg'
      change D x = 0
      simp [D, hf', hg']
    have hkerS : S ≤ LinearMap.ker D :=
      sup_le hkerK (iSup_le hkerL)
    apply LinearMap.ext
    intro x
    have hd : D x.val = 0 := LinearMap.mem_ker.mp (hkerS x.property)
    exact sub_eq_zero.mp (by simpa [D] using hd)
  · intro hfg
    constructor
    · apply LinearMap.ext
      intro x
      have he := LinearMap.congr_fun hfg ⟨(x : V), hK x.property⟩
      change f (x : V) = g (x : V) at he
      have hgx := LinearMap.congr_fun hg.1 x
      change g (x : V) = C z.1 x at hgx
      exact he.trans hgx
    · intro i
      apply LinearMap.ext
      intro x
      have he := LinearMap.congr_fun hfg ⟨(x : V), hL i x.property⟩
      change f (x : V) = g (x : V) at he
      have hgx := LinearMap.congr_fun (hg.2 i) x
      change g (x : V) = T (z.2 i).val x at hgx
      exact he.trans hgx

theorem matchingStar_fibre_card {t d m : Nat}
    (C : CenterTable (V := V) t) (T : LeafTable (V := V) d)
    (z : StarTuple (V := V) t d m)
    (hacc : accepts C T z) (hjoint : jointlyDirect z) :
    Nat.card {f : Module.Dual (ZMod 2) V // MatchesStar C T z f} =
      2 ^ (Module.finrank (ZMod 2) V - (t + m * (d - t))) := by
  classical
  obtain ⟨f0, hf0⟩ := exists_matching_functional C T z hacc hjoint
  let S := jointStarSpan z
  let g := f0.comp S.subtype
  let e : {f : Module.Dual (ZMod 2) V // MatchesStar C T z f} ≃
      FunctionalExtensionFiber S g :=
    { toFun := fun f => ⟨f.1,
        (matchesStar_iff_restrict_jointSpan C T z f.1 f0 hf0).mp f.2⟩
      invFun := fun f => ⟨f.1,
        (matchesStar_iff_restrict_jointSpan C T z f.1 f0 hf0).mpr f.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  have hc := Nat.card_congr e
  have hs : Module.finrank (ZMod 2) S = t + m * (d - t) :=
    jointStarSpan_finrank z hjoint
  rw [hc, Nat.card_eq_fintype_card,
    functionalExtensionFiber_card S g hs]

end
end PvNP.RealizableHardness.ActualOrdinaryStarMatchingFiber
