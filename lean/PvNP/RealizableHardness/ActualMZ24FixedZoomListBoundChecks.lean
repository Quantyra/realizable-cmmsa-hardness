import PvNP.RealizableHardness.ActualMZ24FixedZoomListBound

namespace PvNP.RealizableHardness.ActualMZ24FixedZoomListBoundChecks

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualMZ24FixedZoomListBound
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

/- D3b1 checks cover only tuple/quotient/fibre counting and mass. They do not
formalize or claim MZ24 Lemma 5.25, a full fixed-zoom list bound, or CMMSA;
D3b2 predicate/received-word/list-bound transfer remains outstanding. -/

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

end
end PvNP.RealizableHardness.ActualMZ24FixedZoomListBoundChecks
