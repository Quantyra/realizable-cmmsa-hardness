import PvNP.RealizableHardness.ActualQuestionCenterSourceLaw
import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualOrderedQuestionSourceBridge

/-! Construct a transverse center from each legitimate question's actual
coordinate/equation geometry when its requested dimension is at most 2J. -/

namespace PvNP.RealizableHardness.ActualQuestionCenterNonempty

open PvNP.RealizableHardness.ActualQuestionCenterSourceLaw
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.ActualStarAcceptedGoodMass
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
open PvNP.RealizableHardness.ActualOrderedQuestionSourceBridge
open PvNP.RealizableHardness.ActualQuestionMassBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N m J : Nat} (I : ActualOccurrenceAllocation.Instance N m)

/-- The existing bad-tuple count yields at least one legitimate U once the
actual row count exceeds its explicit collision threshold. -/
theorem goodU_nonempty_of_rowCount
    (hrows : J * (J - 1) * 157 < Fintype.card I.RowId) :
    Nonempty (GoodU I J) := by
  classical
  let B := J * (J - 1) * 157
  let R := Fintype.card I.RowId
  let T := Fintype.card (Fin J → I.RowId)
  let bad := ((Finset.univ : Finset (Fin J → I.RowId)).filter
    (fun u => ¬ GoodOrderedQuestion I.support u)).card
  let good := ((Finset.univ : Finset (Fin J → I.RowId)).filter
    (fun u => GoodOrderedQuestion I.support u)).card
  have hR : 0 < R := by omega
  have hT : 0 < T := by
    dsimp [T]
    rw [Fintype.card_fun]
    exact pow_pos hR _
  have hbadmul : bad * R ≤ B * T :=
    actual_bad_ordered_question_count_mul_rowCard_le I J
  have hB : B < R := hrows
  have hlt : B * T < R * T := Nat.mul_lt_mul_of_pos_right hB hT
  have hbad : bad < T := by nlinarith
  have hsum : good + bad = T := ordered_good_bad_card_add_eq_total I.support
  have hgood : 0 < good := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hgood
  exact ⟨orderedToGoodU I J ⟨u, (Finset.mem_filter.mp hu).2⟩⟩

def zeroCenter (U : GoodU I J) : QuestionCenter I J 0 :=
  { U := U.1
    goodU := U.2.1
    card_U := U.2.2
    K := ⊥
    K_le := bot_le
    finrank_K := finrank_bot _ _
    transverse := by simp }

theorem centerOver_nonempty (U : GoodU I J) {t : Nat} (ht : t ≤ 2 * J) :
    Nonempty (CenterOver I t U) := by
  let q := zeroCenter I U
  let C := transverseComplement q
  have hC : Module.finrank (ZMod 2) C = 2 * J :=
    transverseComplement_finrank q
  have hgrass : Nonempty (Grass C t) := by
    apply Fintype.card_pos_iff.mp
    rw [card_grass, hC]
    exact gaussian_pos ht
  let g : Grass C t := Classical.choice hgrass
  let K : Submodule (ZMod 2) (I.GlobalVar → ZMod 2) :=
    (g.val.map C.subtype).map (questionCoordinateSpace q).subtype
  refine ⟨⟨K, ?_, ?_, ?_⟩⟩
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  · dsimp [K]
    rw [Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
    exact g.property
  · apply le_antisymm
    · intro x hx
      rcases Submodule.mem_map.mp hx.1 with ⟨y, hy, rfl⟩
      rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
      have he : (z : questionCoordinateSpace q) ∈ equationInCoordinate q := hx.2
      have hb : (z : questionCoordinateSpace q) ∈
          equationInCoordinate q ⊓ C := ⟨he, z.2⟩
      rw [(transverseComplement_isCompl q).disjoint.eq_bot] at hb
      simpa using hb
    · exact bot_le

theorem centerOver_nonempty_of_manuscript_bounds
    (U : GoodU I J) {t h : Nat} (ht : t ≤ 2 * h) (hh : h ≤ J) :
    Nonempty (CenterOver I t U) :=
  centerOver_nonempty I U (by omega)

/-- The row-count and geometric bounds jointly remove both nonemptiness
premises from the source question law. -/
def actualSourceQuestionLaw {t : Nat}
    (hrows : J * (J - 1) * 157 < Fintype.card I.RowId)
    (ht : t ≤ 2 * J) :
    ActualFiniteLaw.FiniteLaw (QuestionCenter I J t) := by
  letI : Nonempty (GoodU I J) := goodU_nonempty_of_rowCount I hrows
  exact sourceQuestionLaw I (fun U => centerOver_nonempty I U ht)

/-- Ordered legitimate U and a center sampled in its actual transverse fibre. -/
abbrev OrderedCenter (J t : Nat) :=
  Σ u : OrderedGood I J, CenterOver I t (orderedToGoodU I J u)

def actualOrderedCenterLaw {t : Nat}
    (hrows : J * (J - 1) * 157 < Fintype.card I.RowId)
    (ht : t ≤ 2 * J) :
    ActualFiniteLaw.FiniteLaw (OrderedCenter I J t) := by
  classical
  letI : Nonempty (GoodU I J) := goodU_nonempty_of_rowCount I hrows
  let muU := orderedGoodLaw I J
  let muK (u : OrderedGood I J) :
      ActualFiniteLaw.FiniteLaw (CenterOver I t (orderedToGoodU I J u)) :=
    @ActualFiniteLaw.uniformLaw _ inferInstance
      (centerOver_nonempty I (orderedToGoodU I J u) ht)
  exact
    { mass := fun p => muU.mass p.1 * (muK p.1).mass p.2
      nonneg := by
        intro p
        exact mul_nonneg (muU.nonneg p.1) ((muK p.1).nonneg p.2)
      normalized := by
        simp only [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum]
        simp only [(muK _).normalized, mul_one]
        exact muU.normalized }

theorem actualOrderedCenterLaw_atom {t : Nat}
    (hrows : J * (J - 1) * 157 < Fintype.card I.RowId)
    (ht : t ≤ 2 * J) (p : OrderedCenter I J t) :
    (actualOrderedCenterLaw I hrows ht).mass p =
      1 / ((Fintype.card (OrderedGood I J) : ℚ) *
        (Fintype.card (CenterOver I t (orderedToGoodU I J p.1)) : ℚ)) := by
  classical
  letI : Nonempty (GoodU I J) := goodU_nonempty_of_rowCount I hrows
  change (orderedGoodLaw I J).mass p.1 *
    (@ActualFiniteLaw.uniformLaw _ inferInstance
      (centerOver_nonempty I (orderedToGoodU I J p.1) ht)).mass p.2 = _
  rw [orderedGoodLaw, ActualFiniteLaw.uniformLaw_apply,
    ActualFiniteLaw.uniformLaw_apply]
  ring

end
end PvNP.RealizableHardness.ActualQuestionCenterNonempty
