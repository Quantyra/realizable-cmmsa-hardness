import PvNP.RealizableHardness.ActualMZ24FixedZoomListBound

namespace PvNP.RealizableHardness.ActualMZ24FixedZoomListBoundChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

/- D3b1/D3b2 checks cover tuple/quotient/fibre counting, mass, received-word
transfer, and fixed-W functional-list bounds. They do not formalize or claim
MZ24 Theorem 5.26, CMMSA, or the many-W extraction. -/

#check wordAgreement
#check finite_qary_list_bound
#check Tuple
#check TupleAlphabet
#check linearTupleCodeword
#check card_tupleAlphabet
#check linearTupleCodeword_injective
#check distinct_linearTupleCodeword_agreement
#check qInW
#check qInW_finrank
#check quotientRepresentative
#check quotientRepresentative_mkQ
#check quotientTuple
#check FullRankTuple
#check FullRankQuotientTuple
#check tupleSplitEquiv
#check fullRankTupleSplitEquiv
#check tupleQuotientGrass
#check fullRankTupleZoom
#check card_fullRankTuple_eq
#check fullRankTupleZoom_fiber_card
#check fullRankTupleMass_ge_half
#check FixedZoom
#check fixedZoomQuotientEquiv
#check fullRankTupleZoom_val_eq_generated
#check fullRankTupleZoom_coordinate_mem
#check zoomReceivedWord
#check zoomAgreement_to_wordAgreement
#check fixedZoom_function_list_le_four_div_sq
#check fixedZoom_function_list_le_sixteen_div_sq
#check AgreeingFunctional
#check card_agreeingFunctional_le_sixteen_div_sq

#print axioms finite_qary_list_bound
#print axioms card_tupleAlphabet
#print axioms linearTupleCodeword_injective
#print axioms distinct_linearTupleCodeword_agreement
#print axioms quotientRepresentative_mkQ
#print axioms tupleSplitEquiv
#print axioms fullRankTupleSplitEquiv
#print axioms fullRankTupleZoom
#print axioms card_fullRankTuple_eq
#print axioms fullRankTupleZoom_fiber_card
#print axioms fullRankTupleMass_ge_half
#print axioms fixedZoomQuotientEquiv
#print axioms fullRankTupleZoom_val_eq_generated
#print axioms zoomAgreement_to_wordAgreement
#print axioms fixedZoom_function_list_le_four_div_sq
#print axioms fixedZoom_function_list_le_sixteen_div_sq
#print axioms card_agreeingFunctional_le_sixteen_div_sq

example :
    (Fintype.card (Fin 1) : Rat) <= 1 / (1 / 4 : Rat)^2 := by
  apply finite_qary_list_bound
    (code := fun _ : Fin 1 => fun _ : Fin 1 => (0 : Fin 2))
    (received := fun _ : Fin 1 => (0 : Fin 2))
    (c := (1 / 4 : Rat))
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    norm_num [wordAgreement]

def projectionZero : Module.Dual (ZMod 2) (Fin 4 -> ZMod 2) :=
  { toFun := fun x => x 0
    map_add' := by intro x y; simp
    map_smul' := by intro c x; simp }

def zeroFunctional : Module.Dual (ZMod 2) (Fin 4 -> ZMod 2) := 0

example : projectionZero ≠ zeroFunctional := by
  intro h
  have hz := congrArg (fun g : Module.Dual (ZMod 2) (Fin 4 -> ZMod 2) =>
    g (fun i => if i = 0 then 1 else 0)) h
  simp [projectionZero, zeroFunctional] at hz

example :
    wordAgreement
        (linearTupleCodeword (W := Fin 4 -> ZMod 2) 2 projectionZero)
        (linearTupleCodeword (W := Fin 4 -> ZMod 2) 2 zeroFunctional) =
      1 / (2^2 : Rat) := by
  exact distinct_linearTupleCodeword_agreement
    (W := Fin 4 -> ZMod 2) 2 (by exact Nat.zero_lt_succ 1)
    (by
      intro h
      have hz := congrArg
        (fun g : Module.Dual (ZMod 2) (Fin 4 -> ZMod 2) =>
          g (fun i => if i = 0 then 1 else 0)) h
      simp [projectionZero, zeroFunctional] at hz)

/- A concrete inhabited three-dimensional zoom over the explicit
F₂-vector space `Fin 30 → ZMod 2`; this supplies the positive-beta
received-word fixture without reducing to an empty or singleton fibre. -/
abbrev d3V := Fin 30 → ZMod 2

def d3Index : Fin 3 → Fin 30 :=
  Fin.castLE (by norm_num)

def d3frame : Fin 3 → d3V :=
  fun j i => if i = d3Index j then 1 else 0

theorem d3frame_li : LinearIndependent (ZMod 2) d3frame := by
  rw [Fintype.linearIndependent_iff]
  intro c h i
  have hi := congrFun h (d3Index i)
  simpa [d3frame, d3Index] using hi

def d3Q0 : Grass d3V 0 :=
  ⟨⊥, by simp⟩

def d3L3 : Grass d3V 3 :=
  ⟨Submodule.span (ZMod 2) (Set.range d3frame), by
    simpa using finrank_span_eq_card d3frame_li⟩

def d3Pair : DecodedPair d3Q0 3 :=
  { W := ⊤
    hQW := le_top
    g := 0 }

def d3Table : (L : Grass d3V 3) → Module.Dual (ZMod 2) L.val :=
  fun _ => 0

def d3Zoom : Zoom d3Q0 d3Pair := by
  refine ⟨d3L3, ?_⟩
  constructor
  · exact bot_le
  · simpa [d3Pair] using (le_top : d3L3.val ≤ (⊤ : Submodule (ZMod 2) d3V))

example : Nonempty (Zoom d3Q0 d3Pair) := ⟨d3Zoom⟩

theorem d3_agrees : ∀ z : Zoom d3Q0 d3Pair,
    AgreesOn d3Table z.1 z.2.2 := by
  intro z x
  change (0 : ZMod 2) = 0
  rfl

theorem d3_agreement : (1 : Rat) ≤ agreement d3Table d3Q0 d3Pair := by
  let e : AgreeingZoom d3Table d3Q0 d3Pair ≃ Zoom d3Q0 d3Pair :=
    { toFun := fun z => z.1
      invFun := fun z => ⟨z, d3_agrees z⟩
      left_inv := by intro z; apply Subtype.ext; rfl
      right_inv := by intro z; rfl }
  have hzoom : Fintype.card (Zoom d3Q0 d3Pair) ≠ 0 := by
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨d3Zoom⟩)
  have hcard := Fintype.card_congr e
  have hzoomRat : (Fintype.card (Zoom d3Q0 d3Pair) : Rat) ≠ 0 := by
    exact_mod_cast hzoom
  rw [agreement_eq_fraction_of_nonempty d3Table d3Q0 d3Pair hzoom, hcard]
  simp [hzoomRat]

example :
    (1 / 2 : Rat) ≤
      wordAgreement
        (linearTupleCodeword (W := (⊤ : Submodule (ZMod 2) d3V)) 3 0)
        (zoomReceivedWord d3Table d3Q0 (⊤ : Submodule (ZMod 2) d3V) le_top) := by
  exact zoomAgreement_to_wordAgreement
    (T := d3Table) (Q := d3Q0) (W := (⊤ : Submodule (ZMod 2) d3V))
    (hQW := le_top) (had := by norm_num)
    (hlarge := by norm_num [Module.finrank_fin_fun])
    (g := 0) (beta := 1) (by simpa [d3Pair] using d3_agreement)

def d3Singleton : Fin 1 →
    Module.Dual (ZMod 2) (⊤ : Submodule (ZMod 2) d3V) :=
  fun _ => 0

theorem d3Singleton_injective : Function.Injective d3Singleton := by
  intro i j h
  exact Fin.eq_zero i |>.trans (Fin.eq_zero j).symm

def d3AgreeingZero : AgreeingFunctional d3Table d3Q0
    (⊤ : Submodule (ZMod 2) d3V) le_top 1 :=
  ⟨0, by simpa [d3Pair] using d3_agreement⟩

example : Nonempty (AgreeingFunctional d3Table d3Q0
    (⊤ : Submodule (ZMod 2) d3V) le_top 1) :=
  ⟨d3AgreeingZero⟩

example :
    (Fintype.card (Fin 1) : Rat) ≤ 16 / (1 : Rat)^2 := by
  exact fixedZoom_function_list_le_sixteen_div_sq
    (T := d3Table) (Q := d3Q0) (W := (⊤ : Submodule (ZMod 2) d3V))
    (hQW := le_top) (Iota := Fin 1) (g := d3Singleton)
    (hinj := d3Singleton_injective) (beta := 1)
    (had := by norm_num) (hgap := by norm_num)
    (hlarge := by norm_num [Module.finrank_fin_fun])
    (hbeta := by norm_num) (hthreshold := by norm_num)
    (hagrees := fun _ => by
      simpa [d3Pair, d3Singleton] using d3_agreement)

example :
    (Fintype.card (AgreeingFunctional d3Table d3Q0
      (⊤ : Submodule (ZMod 2) d3V) le_top 1) : Rat) ≤
      16 / (1 : Rat)^2 := by
  exact card_agreeingFunctional_le_sixteen_div_sq
    (T := d3Table) (Q := d3Q0) (W := (⊤ : Submodule (ZMod 2) d3V))
    (hQW := le_top) (beta := 1) (had := by norm_num)
    (hgap := by norm_num)
    (hlarge := by norm_num [Module.finrank_fin_fun])
    (hbeta := by norm_num)
    (hthreshold := by norm_num)

end
end PvNP.RealizableHardness.ActualMZ24FixedZoomListBoundChecks
