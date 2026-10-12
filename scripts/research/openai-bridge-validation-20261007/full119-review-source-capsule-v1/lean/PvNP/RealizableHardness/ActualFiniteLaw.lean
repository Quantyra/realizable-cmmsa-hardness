import PvNP.RealizableHardness.ActualMaximalPairLadder
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
Finite rational probability laws and their elementary transport calculus.

This file is a foundation only.  It is not the MZ24 sampling lemma, Section 8,
an advised mixture theorem, or a CMMSA theorem.  In particular, no sampling,
incidence, concentration, posterior, Gaussian, genericity, or extraction claim
is made here.
-/

namespace PvNP.RealizableHardness.ActualFiniteLaw

open scoped BigOperators
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

structure FiniteLaw (Omega : Type*) [Fintype Omega] where
  mass : Omega → ℚ
  nonneg : ∀ x, 0 ≤ mass x
  normalized : ∑ x, mass x = 1

@[ext] theorem FiniteLaw.ext {Omega : Type*} [Fintype Omega]
    {mu nu : FiniteLaw Omega} (h : ∀ x, mu.mass x = nu.mass x) : mu = nu := by
  cases mu with
  | mk mm hm hmn =>
    cases nu with
    | mk nn hn hnn =>
      have hmass : mm = nn := funext h
      cases hmass
      rfl

lemma mass_nonneg {Omega : Type*} [Fintype Omega] (mu : FiniteLaw Omega) (x : Omega) :
    0 ≤ mu.mass x := mu.nonneg x

lemma mass_sum {Omega : Type*} [Fintype Omega] (mu : FiniteLaw Omega) :
    ∑ x, mu.mass x = 1 := mu.normalized

def eventMass {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (E : Finset Omega) : ℚ :=
  ∑ x ∈ E, mu.mass x

lemma eventMass_empty {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) : eventMass mu ∅ = 0 := by
  simp [eventMass]

lemma eventMass_univ {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) : eventMass mu Finset.univ = 1 := by
  simpa [eventMass] using mu.normalized

def totalVariation {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) : ℚ :=
  (∑ x, |mu.mass x - nu.mass x|) / 2

lemma totalVariation_nonneg {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) : 0 ≤ totalVariation mu nu := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => abs_nonneg _)) (by norm_num)

lemma totalVariation_self {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) : totalVariation mu mu = 0 := by
  simp [totalVariation]

lemma totalVariation_symm {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) : totalVariation mu nu = totalVariation nu mu := by
  simp [totalVariation, abs_sub_comm]

def eventSub {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) (E : Finset Omega) : ℚ :=
  eventMass mu E - eventMass nu E

lemma eventSub_le_totalVariation {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) (E : Finset Omega) :
    eventSub mu nu E ≤ totalVariation mu nu := by
  have hpoint (x : Omega) :
      2 * (if x ∈ E then (mu.mass x - nu.mass x) else 0) ≤
        |mu.mass x - nu.mass x| + (mu.mass x - nu.mass x) := by
    by_cases hx : x ∈ E
    · simp only [hx, if_true]
      linarith [le_abs_self (mu.mass x - nu.mass x)]
    · simp only [hx, if_false, zero_mul]
      linarith [neg_abs_le (mu.mass x - nu.mass x)]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Omega)) => hpoint x)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  have hnorm : (∑ x, mu.mass x) - (∑ x, nu.mass x) = 0 := by
    rw [mu.normalized, nu.normalized, sub_self]
  rw [hnorm, add_zero] at hs
  have hs' : 2 * eventSub mu nu E ≤
      ∑ x, |mu.mass x - nu.mass x| := by
    simpa [eventSub, eventMass, add_comm] using hs
  unfold totalVariation
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2
  simpa [eventSub, mul_comm] using hs'

lemma totalVariation_eventSub_le {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) (E : Finset Omega) :
    eventSub nu mu E ≤ totalVariation mu nu := by
  simpa [eventSub, totalVariation, abs_sub_comm] using
    (eventSub_le_totalVariation nu mu E)

theorem abs_eventMass_sub_le_totalVariation {Omega : Type*} [Fintype Omega]
  (mu nu : FiniteLaw Omega) (E : Finset Omega) :
    |eventMass mu E - eventMass nu E| ≤ totalVariation mu nu := by
  apply abs_le.mpr
  exact ⟨by
      have h := totalVariation_eventSub_le mu nu E
      have h' : eventMass nu E - eventMass mu E ≤ totalVariation mu nu := by
        simpa [eventSub] using h
      linarith,
    eventSub_le_totalVariation mu nu E⟩

theorem eventMass_sub_le_totalVariation {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) (E : Finset Omega) :
    eventMass mu E - eventMass nu E ≤ totalVariation mu nu :=
  eventSub_le_totalVariation mu nu E

theorem eventMass_sub_ge_neg_totalVariation {Omega : Type*} [Fintype Omega]
    (mu nu : FiniteLaw Omega) (E : Finset Omega) :
    -totalVariation mu nu ≤ eventMass mu E - eventMass nu E := by
  have h := totalVariation_eventSub_le mu nu E
  have h' : eventMass nu E - eventMass mu E ≤ totalVariation mu nu := by
    simpa [eventSub] using h
  linarith

def uniformLaw (Omega : Type*) [Fintype Omega] [Nonempty Omega] : FiniteLaw Omega := by
  let n : ℚ := Fintype.card Omega
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Omega ≠ 0)
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Omega)
  refine { mass := fun _ => 1 / n, nonneg := ?_, normalized := ?_ }
  · intro x
    exact div_nonneg (by norm_num) hnpos.le
  · dsimp [n]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hn]

lemma uniformLaw_apply (Omega : Type*) [Fintype Omega] [Nonempty Omega] (x : Omega) :
    (uniformLaw Omega).mass x = (1 : ℚ) / Fintype.card Omega := by
  rfl

def dirac {Omega : Type*} [Fintype Omega] (x : Omega) : FiniteLaw Omega :=
  { mass := fun y => if y = x then 1 else 0
    nonneg := by intro y; split_ifs <;> norm_num
    normalized := by simp }

lemma dirac_apply {Omega : Type*} [Fintype Omega] (x y : Omega) :
    (dirac x).mass y = if y = x then 1 else 0 := rfl

def pushforward {Omega Gamma : Type*} [Fintype Omega] [Fintype Gamma]
    (f : Omega → Gamma) (mu : FiniteLaw Omega) : FiniteLaw Gamma :=
  { mass := fun y => ∑ x, if f x = y then mu.mass x else 0
    nonneg := by
      intro y
      apply Finset.sum_nonneg
      intro x hx
      by_cases h : f x = y
      · simp [h, mu.nonneg x]
      · simp [h]
    normalized := by
      calc
        (∑ y, ∑ x, if f x = y then mu.mass x else 0) =
            ∑ x, ∑ y, if f x = y then mu.mass x else 0 := by
              rw [Finset.sum_comm]
        _ = ∑ x, mu.mass x := by
              apply Finset.sum_congr rfl
              intro x hx
              simp
        _ = 1 := mu.normalized }

lemma pushforward_apply {Omega Gamma : Type*} [Fintype Omega] [Fintype Gamma]
    (f : Omega → Gamma) (mu : FiniteLaw Omega) (y : Gamma) :
    (pushforward f mu).mass y = ∑ x, if f x = y then mu.mass x else 0 := rfl

def preimageEvent {Omega Gamma : Type*} [Fintype Omega] [Fintype Gamma]
    (f : Omega → Gamma) (E : Finset Gamma) : Finset Omega :=
  Finset.univ.filter (fun x => f x ∈ E)

lemma eventMass_pushforward {Omega Gamma : Type*} [Fintype Omega] [Fintype Gamma]
    (f : Omega → Gamma) (mu : FiniteLaw Omega) (E : Finset Gamma) :
    eventMass (pushforward f mu) E = eventMass mu (preimageEvent f E) := by
  classical
  unfold eventMass pushforward preimageEvent
  rw [Finset.sum_comm, Finset.sum_filter]
  simp

theorem pushforward_id {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) : pushforward id mu = mu := by
  apply FiniteLaw.ext
  intro x
  simp [pushforward]

theorem pushforward_comp {Omega Gamma Delta : Type*}
    [Fintype Omega] [Fintype Gamma] [Fintype Delta]
    (f : Omega → Gamma) (g : Gamma → Delta) (mu : FiniteLaw Omega) :
    pushforward g (pushforward f mu) = pushforward (g ∘ f) mu := by
  classical
  apply FiniteLaw.ext
  intro z
  calc
    (pushforward g (pushforward f mu)).mass z =
        ∑ y, if g y = z then (∑ x, if f x = y then mu.mass x else 0) else 0 := rfl
    _ = ∑ y, ∑ x, if g y = z then (if f x = y then mu.mass x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : g y = z <;> simp [h]
    _ = ∑ x, ∑ y, if g y = z then (if f x = y then mu.mass x else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = (pushforward (g ∘ f) mu).mass z := by
      change (∑ x, ∑ y, if g y = z then (if f x = y then mu.mass x else 0) else 0) =
        ∑ x, if g (f x) = z then mu.mass x else 0
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_eq_single (f x)]
      · by_cases h : g (f x) = z <;> simp [h]
      · intro y hy
        simp [Ne.symm hy]

def uniformMixture {I Omega : Type*} [Fintype I] [Fintype Omega] [Nonempty I]
    (mus : I → FiniteLaw Omega) : FiniteLaw Omega := by
  let n : ℚ := Fintype.card I
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  refine { mass := fun x => (∑ i, (mus i).mass x) / n, nonneg := ?_, normalized := ?_ }
  · intro x
    exact div_nonneg (Finset.sum_nonneg (fun i _ => (mus i).nonneg x)) hnpos.le
  · dsimp [n]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [FiniteLaw.normalized]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]

lemma eventMass_uniformMixture {I Omega : Type*} [Fintype I] [Fintype Omega]
    [Nonempty I] (mus : I → FiniteLaw Omega) (E : Finset Omega) :
    eventMass (uniformMixture mus) E =
      (∑ i, eventMass (mus i) E) / Fintype.card I := by
  classical
  unfold eventMass uniformMixture
  dsimp
  rw [← Finset.sum_div]
  rw [Finset.sum_comm]

lemma pushforward_uniformMixture {I Omega Gamma : Type*}
    [Fintype I] [Fintype Omega] [Fintype Gamma] [Nonempty I]
    (f : Omega → Gamma) (mus : I → FiniteLaw Omega) :
    pushforward f (uniformMixture mus) =
      uniformMixture (fun i => pushforward f (mus i)) := by
  classical
  apply FiniteLaw.ext
  intro y
  let n : ℚ := Fintype.card I
  change (∑ x, if f x = y then (∑ i, (mus i).mass x) / n else 0) =
    (∑ i, ∑ x, if f x = y then (mus i).mass x else 0) / n
  calc
    (∑ x, if f x = y then (∑ i, (mus i).mass x) / n else 0) =
        ∑ x, ∑ i, (if f x = y then (mus i).mass x else 0) / n := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : f x = y <;> simp [h, Finset.sum_div]
    _ = ∑ i, ∑ x, (if f x = y then (mus i).mass x else 0) / n := by
          rw [Finset.sum_comm]
    _ = (∑ i, ∑ x, if f x = y then (mus i).mass x else 0) / n := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_div]

theorem totalVariation_pushforward_le {Omega Gamma : Type*}
    [Fintype Omega] [Fintype Gamma]
    (f : Omega → Gamma) (mu nu : FiniteLaw Omega) :
    totalVariation (pushforward f mu) (pushforward f nu) ≤ totalVariation mu nu := by
  classical
  unfold totalVariation pushforward
  have hpoint (y : Gamma) :
      |(∑ x, if f x = y then mu.mass x else 0) -
        ∑ x, if f x = y then nu.mass x else 0| ≤
        ∑ x, if f x = y then |mu.mass x - nu.mass x| else 0 := by
    calc
      _ = |∑ x, ((if f x = y then mu.mass x else 0) -
          (if f x = y then nu.mass x else 0))| := by
            rw [Finset.sum_sub_distrib]
      _ ≤ ∑ x, |(if f x = y then mu.mass x else 0) -
          (if f x = y then nu.mass x else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : f x = y <;> simp [h]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset Gamma))
    (fun y _ => hpoint y)
  rw [Finset.sum_comm] at hs
  have hs' :
      ∑ y, |(∑ x, if f x = y then mu.mass x else 0) -
        ∑ x, if f x = y then nu.mass x else 0| ≤
        ∑ x, |mu.mass x - nu.mass x| := by
    calc
      _ ≤ ∑ x, ∑ y, if f x = y then |mu.mass x - nu.mass x| else 0 := hs
      _ = ∑ x, |mu.mass x - nu.mass x| := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
  change
    (∑ y, |(∑ x, if f x = y then mu.mass x else 0) -
      ∑ x, if f x = y then nu.mass x else 0|) / 2 ≤
      (∑ x, |mu.mass x - nu.mass x|) / 2
  exact div_le_div_of_nonneg_right hs' (by norm_num)

theorem pushforward_uniformLaw_equiv {Omega Gamma : Type*}
    [Fintype Omega] [Fintype Gamma] [Nonempty Omega] [Nonempty Gamma]
    (e : Omega ≃ Gamma) :
    pushforward e (uniformLaw Omega) = uniformLaw Gamma := by
  classical
  apply FiniteLaw.ext
  intro y
  change (∑ x, if e x = y then (1 : ℚ) / Fintype.card Omega else 0) =
    (1 : ℚ) / Fintype.card Gamma
  rw [Fintype.sum_eq_single (e.symm y)]
  · simp [Fintype.card_congr e]
  · intro x hx
    have hne : ¬ e x = y := by
      intro hxy
      apply hx
      simpa using congrArg e.symm hxy
    simp [hne]

theorem totalVariation_equiv {Omega Gamma : Type*}
    [Fintype Omega] [Fintype Gamma]
  (e : Omega ≃ Gamma) (mu nu : FiniteLaw Omega) :
    totalVariation (pushforward e mu) (pushforward e nu) = totalVariation mu nu := by
  have h₁ := totalVariation_pushforward_le e mu nu
  have h₂ := totalVariation_pushforward_le e.symm (pushforward e mu) (pushforward e nu)
  have he : e.symm ∘ e = id := by
    funext x
    simp
  have hmu : pushforward e.symm (pushforward e mu) = mu := by
    rw [pushforward_comp, he, pushforward_id]
  have hnu : pushforward e.symm (pushforward e nu) = nu := by
    rw [pushforward_comp, he, pushforward_id]
  rw [hmu, hnu] at h₂
  exact le_antisymm h₁ h₂

lemma uniformLaw_atom {Omega : Type*} [Fintype Omega] [Nonempty Omega] (x : Omega) :
    (uniformLaw Omega).mass x = (1 : ℚ) / Fintype.card Omega :=
  uniformLaw_apply Omega x

def agreeingEvent {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d) : Finset (Zoom Q P) :=
  Finset.univ.filter (fun z => AgreesOn T z.1 z.2.2)

lemma agreement_eq_uniform_eventMass
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a d : Nat} (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (P : DecodedPair Q d)
    (hzoom : Nonempty (Zoom Q P)) :
    agreement T Q P =
      eventMass (uniformLaw (Zoom Q P)) (agreeingEvent T Q P) := by
  letI := hzoom
  have hc : Fintype.card (Zoom Q P) ≠ 0 := Fintype.card_ne_zero
  rw [agreement_eq_fraction_of_nonempty T Q P hc]
  unfold eventMass
  simp_rw [uniformLaw_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      Fintype.card (agreeingEvent T Q P) = Fintype.card (AgreeingZoom T Q P) := by
    let e : agreeingEvent T Q P ≃ AgreeingZoom T Q P :=
      { toFun := fun z => ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
        invFun := fun z => ⟨z.1, by simp [agreeingEvent, z.2]⟩
        left_inv := by intro z; cases z; rfl
        right_inv := by intro z; cases z; rfl }
    exact Fintype.card_congr e
  have hcard' : (agreeingEvent T Q P).card = Fintype.card (AgreeingZoom T Q P) := by
    simpa using hcard
  rw [hcard']
  simp [div_eq_mul_inv]

end
end PvNP.RealizableHardness.ActualFiniteLaw
