import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
import PvNP.RealizableHardness.ActualCliqueScoreTransfer
import PvNP.RealizableHardness.GaussianRatio

namespace PvNP.RealizableHardness.ActualQuestionCenterCollisionBound

open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualStarQuestionSupport
open PvNP.RealizableHardness.ActualPresentedLeafGluing
open PvNP.RealizableHardness.ActualCliqueCollisionTransfer
open PvNP.RealizableHardness.ActualQuestionCenterDomainDraw
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GaussianRatio
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

local instance rowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

abbrev IndexPair (k : Nat) :=
  {p : Fin k × Fin k // p.1 < p.2}

abbrev DomainTuple
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h k : Nat) :=
  Fin k → DomainDraw q h

noncomputable def actualStarLeafVertices
    {N m J t k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (draws : DomainTuple q h k) :
    Fin k → LeafVertex I J h :=
  fun i => drawVertex q h (draws i)

noncomputable def domainTupleNonempty
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
    Nonempty (DomainTuple q h k) := by
  letI : Nonempty (DomainDraw q h) := domainDraw_nonempty q h ht hh
  exact ⟨fun _ => Classical.choice inferInstance⟩

noncomputable def domainTupleMean
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (f : DomainTuple q h k → ℚ) : ℚ := by
  letI : Nonempty (DomainTuple q h k) :=
    domainTupleNonempty q h k ht hh
  exact uniformMean (DomainTuple q h k) f

noncomputable def pairCollisionMass
    {N m J t k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (p : IndexPair k) : ℚ :=
  domainTupleMean q h k ht hh (fun draws =>
    if cliqueOf (actualStarLeafVertices q h draws p.1.1) =
        cliqueOf (actualStarLeafVertices q h draws p.1.2) then 1 else 0)

noncomputable def actualCliqueCollisionMass
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) : ℚ :=
  domainTupleMean q h k ht hh (fun draws =>
    if CliqueCollision (actualStarLeafVertices q h draws) then 1 else 0)

theorem actualCliqueCollisionMass_eq_collisionMass
    {N m J t : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
  actualCliqueCollisionMass q h k ht hh = (by
    letI : Nonempty (DomainTuple q h k) :=
      domainTupleNonempty q h k ht hh
    exact collisionMass
      (fun draws : DomainTuple q h k => actualStarLeafVertices q h draws)) := by
  rfl

theorem drawPair_clique_eq_iff
    {N m J t k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (draws : DomainTuple q h k) (p : IndexPair k) :
  cliqueOf (actualStarLeafVertices q h draws p.1.1) =
      cliqueOf (actualStarLeafVertices q h draws p.1.2) ↔
    draws p.1.1 = draws p.1.2 := by
  constructor
  · intro hC
    exact Subtype.ext ((cliqueOf_drawVertex_eq_iff q h (draws p.1.1)
      (draws p.1.2)).mp hC)
  · intro hD
    exact (cliqueOf_drawVertex_eq_iff q h (draws p.1.1)
      (draws p.1.2)).mpr (congrArg Subtype.val hD)

private theorem uniformMean_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : β → ℚ) :
  uniformMean α (fun x => f (e x)) = uniformMean β f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

private theorem uniformMean_prod_fst
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℚ) :
  uniformMean (α × β) (fun x => f x.1) = uniformMean α f := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp
  simp only [Fintype.card]
  ring

private theorem uniformMean_restrict_injective
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → Type*) [∀ c, Fintype (A c)]
    [∀ c, Nonempty (A c)]
    (key : ι → κ) (hkey : Function.Injective key)
    (g : ((i : ι) → A (key i)) → ℚ) :
  uniformMean ((c : κ) → A c)
      (fun s => g (fun i => s (key i))) =
    uniformMean ((i : ι) → A (key i)) g := by
  classical
  let p : κ → Prop := fun c => c ∈ Set.range key
  let e : ι ≃ Set.range key := Equiv.ofInjective key hkey
  let Unused := (c : {c : κ // c ∉ Set.range key}) → A c.1
  let split := Equiv.piEquivPiSubtypeProd p A
  let used : ((i : ι) → A (key i)) ≃
      ((c : Set.range key) → A c.1) :=
    Equiv.piCongrLeft (fun c : Set.range key => A c.1) e
  let total : ((c : κ) → A c) ≃
      (((i : ι) → A (key i)) × Unused) :=
    split.trans (Equiv.prodCongr used.symm (Equiv.refl Unused))
  have hrestrict (s : (c : κ) → A c) :
      (total s).1 = (fun i => s (key i)) := by
    funext i
    change
      (Equiv.piCongrLeft (fun c : Set.range key => A c.1) e).symm
          (fun c : Set.range key => s c.1) i = s (key i)
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  calc
    uniformMean ((c : κ) → A c)
        (fun s => g (fun i => s (key i))) =
        uniformMean ((c : κ) → A c)
          (fun s => (fun x => g x.1) (total s)) := by
      apply congrArg (uniformMean ((c : κ) → A c))
      funext s
      exact congrArg g (hrestrict s).symm
    _ = uniformMean
          (((i : ι) → A (key i)) × Unused)
          (fun x => g x.1) :=
      uniformMean_equiv total (fun x => g x.1)
    _ = uniformMean ((i : ι) → A (key i)) g :=
      uniformMean_prod_fst g

private theorem uniform_pi_pair_eq_mass
    {α : Type*} [Fintype α] [Nonempty α]
    {k : Nat} (i j : Fin k) (hij : i ≠ j) :
  uniformMean (Fin k → α)
      (fun f => if f i = f j then 1 else 0) =
    1 / (Fintype.card α : ℚ) := by
  let key : Fin 2 → Fin k := ![i, j]
  have hkey : Function.Injective key := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hij (by simpa [key] using hab)).elim
    · exact (hij (by simpa [key] using hab.symm)).elim
    · rfl
  have hrestrict := uniformMean_restrict_injective
    (A := fun _ : Fin k => α) key hkey
    (fun f : Fin 2 → α => if f 0 = f 1 then 1 else 0)
  have htwo :
      uniformMean (Fin 2 → α) (fun f => if f 0 = f 1 then 1 else 0) =
        1 / (Fintype.card α : ℚ) := by
    have he := (finTwoArrowEquiv α).symm.sum_comp
      (fun f : Fin 2 → α => if f 0 = f 1 then (1 : ℚ) else 0)
    calc
      uniformMean (Fin 2 → α)
          (fun f => if f 0 = f 1 then 1 else 0) =
          uniformMean (α × α)
            (fun x => if x.1 = x.2 then 1 else 0) := by
        unfold uniformMean
        rw [← he, Fintype.card_congr (finTwoArrowEquiv α)]
        simp [finTwoArrowEquiv]
      _ = 1 / (Fintype.card α : ℚ) := by
        unfold uniformMean
        rw [Fintype.sum_prod_type, Fintype.card_prod]
        simp
  simpa [key] using hrestrict.trans htwo

theorem pairCollisionMass_eq_card
    {N m J t h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t)
    (ht : t ≤ 2*h) (hh : h ≤ J) (p : IndexPair k) :
  pairCollisionMass q h ht hh p =
    1 / (Fintype.card (DomainDraw q h) : ℚ) := by
  letI : Nonempty (DomainDraw q h) := domainDraw_nonempty q h ht hh
  letI : Nonempty (DomainTuple q h k) :=
    domainTupleNonempty q h k ht hh
  have hp : p.1.1 ≠ p.1.2 := p.property.ne
  unfold pairCollisionMass domainTupleMean
  calc
    uniformMean (Fin k → DomainDraw q h)
        (fun draws => if cliqueOf (actualStarLeafVertices q h draws p.1.1) =
          cliqueOf (actualStarLeafVertices q h draws p.1.2) then 1 else 0) =
      uniformMean (Fin k → DomainDraw q h)
        (fun draws => if draws p.1.1 = draws p.1.2 then 1 else 0) := by
      apply congrArg (uniformMean (Fin k → DomainDraw q h))
      funext draws
      simp only [drawPair_clique_eq_iff q h draws p]
    _ = 1 / (Fintype.card (DomainDraw q h) : ℚ) :=
      uniform_pi_pair_eq_mass p.1.1 p.1.2 hp

theorem pairCollisionMass_eq
    {N m J t h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t)
    (ht : t ≤ 2*h) (hh : h ≤ J) (p : IndexPair k) :
  pairCollisionMass q h ht hh p =
    1 / (gaussian (2*J - t) (2*h - t) : ℚ) := by
  rw [pairCollisionMass_eq_card, domainDraw_card q h ht hh]

def cliqueGaussianRatio (J h t : Nat) : ℚ :=
  (gaussian (J + 2*h - t) (2*h - t) : ℚ) /
    gaussian (3*J - t) (2*h - t)

theorem normalizedFrame_pos {n a : Nat} (ha : a ≤ n) :
    0 < normalizedFrame n a := by
  unfold normalizedFrame
  apply Finset.prod_pos
  intro i hi
  have hi' : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) ha
  apply sub_pos.mpr
  apply (div_lt_one (by positivity)).mpr
  have hpow : ((2^i : Nat) : ℚ) < ((2^n : Nat) : ℚ) :=
    Nat.cast_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two hi')
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow

theorem normalizedFrame_mono_ambient {a m n : Nat}
    (ha : a ≤ m) (hm : m ≤ n) :
    normalizedFrame m a ≤ normalizedFrame n a := by
  unfold normalizedFrame
  apply Finset.prod_le_prod
  · intro i hi
    have hi' : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) ha
    have hpow : (2 : ℚ)^i ≤ (2 : ℚ)^m := by
      have hNat : 2^i ≤ 2^m :=
        Nat.pow_le_pow_right Nat.zero_lt_two
          (Nat.le_of_lt hi')
      exact_mod_cast hNat
    have hpow' : (2 : ℚ)^i ≤ (2 : ℚ)^n := hpow.trans
      (by
        have hNat : 2^m ≤ 2^n :=
          Nat.pow_le_pow_right Nat.zero_lt_two hm
        exact_mod_cast hNat)
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow)
  · intro i hi
    have hi' : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) ha
    have hpow_i : (2 : ℚ)^i ≤ (2 : ℚ)^m := by
      have hNat : 2^i ≤ 2^m :=
        Nat.pow_le_pow_right Nat.zero_lt_two
          (Nat.le_of_lt hi')
      exact_mod_cast hNat
    have hpow_m : (2 : ℚ)^m ≤ (2 : ℚ)^n := by
      have hNat : 2^m ≤ 2^n :=
          Nat.pow_le_pow_right Nat.zero_lt_two hm
      exact_mod_cast hNat
    have hquot : (2 : ℚ)^i / 2^n ≤ (2 : ℚ)^i / 2^m := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hxi : (0 : ℚ) ≤ 2^i := by positivity
      exact mul_le_mul_of_nonneg_left hpow_m hxi
    exact sub_le_sub_left hquot 1

private theorem actual_frameProduct_pos {a r : Nat} (hr : a ≤ r) :
    0 < frameProduct r a := by
  unfold frameProduct
  apply Finset.prod_pos
  intro i hi
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right Nat.one_lt_two
    (lt_of_lt_of_le i.isLt hr)

private theorem actual_frameProduct_cast {a r : Nat} (hr : a ≤ r) :
    (frameProduct r a : ℚ) =
      (2 : ℚ)^(r*a) * normalizedFrame r a := by
  have hfactor : ∀ i ∈ Finset.range a,
      ((2^r - 2^i : Nat) : ℚ) =
        (2 : ℚ)^r * (1 - (2 : ℚ)^i / 2^r) := by
    intro i hi
    have hi' : i ≤ r :=
      (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hr
    rw [Nat.cast_sub (Nat.pow_le_pow_right Nat.zero_lt_two hi')]
    push_cast
    have hpow : (2 : ℚ)^r ≠ 0 := by positivity
    rw [mul_sub, mul_one, mul_div_cancel₀ ((2 : ℚ)^i) hpow]
  unfold frameProduct
  rw [Fin.prod_univ_eq_prod_range (fun i => 2^r - 2^i) a]
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ Finset.range a, ((2^r - 2^i : Nat) : ℚ)) =
        ∏ i ∈ Finset.range a, (2 : ℚ)^r *
          (1 - (2 : ℚ)^i / 2^r) :=
      Finset.prod_congr rfl hfactor
    _ = (2 : ℚ)^(r*a) * normalizedFrame r a := by
      rw [Finset.prod_mul_distrib]
      simp [normalizedFrame, ← pow_mul]

private theorem actual_gaussian_mul_frame_nat {a r : Nat} (hr : a ≤ r) :
    gaussian r a * frameProduct a a = frameProduct r a := by
  have hmul := card_grass_mul
    (V := Fin r → ZMod 2) (a := a) (by simpa using hr)
  have hdiv : frameProduct a a ∣ frameProduct r a := by
    refine ⟨Fintype.card (Grass (Fin r → ZMod 2) a), ?_⟩
    simpa [Nat.mul_comm] using hmul.symm
  rw [gaussian, if_pos hr]
  exact Nat.div_mul_cancel hdiv

private theorem actual_gaussian_ne_zero {a r : Nat} (hr : a ≤ r) :
    gaussian r a ≠ 0 := by
  intro hz
  have hzero : frameProduct r a = 0 := by
    simpa [hz] using (actual_gaussian_mul_frame_nat hr).symm
  exact (Nat.ne_of_gt (actual_frameProduct_pos hr)) hzero

private theorem actual_gaussian_frame_cast {a r : Nat} (hr : a ≤ r) :
    (gaussian r a : ℚ) * (frameProduct a a : ℚ) =
      (2 : ℚ)^(r*a) * normalizedFrame r a := by
  have h := congrArg (fun z : Nat => (z : ℚ))
    (actual_gaussian_mul_frame_nat hr)
  simpa [Nat.cast_mul,
    actual_frameProduct_cast (a := a) (r := r) hr] using h

private theorem actual_gaussian_forward_ratio {a m n : Nat}
    (ha : a ≤ m) (hm : m ≤ n) :
  (gaussian n a : ℚ) / gaussian m a =
    ((2 : ℚ) ^ (a * (n - m)) * normalizedFrame n a) /
      normalizedFrame m a := by
  have hn : a ≤ n := ha.trans hm
  have hgm : (gaussian m a : ℚ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (actual_gaussian_ne_zero ha)))
  have hfm : normalizedFrame m a ≠ 0 :=
    ne_of_gt (normalizedFrame_pos ha)
  have hf : (frameProduct a a : ℚ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (actual_frameProduct_pos le_rfl))
  have h1 := actual_gaussian_frame_cast hn
  have h2 := actual_gaussian_frame_cast ha
  have hexp : n*a = a*(n-m) + m*a := by
    calc
      n*a = ((n-m)+m)*a := by rw [Nat.sub_add_cancel hm]
      _ = a*(n-m) + m*a := by ring
  rw [hexp, pow_add] at h1
  apply (div_eq_iff hgm).mpr
  apply (mul_right_cancel₀ hf)
  rw [h1]
  field_simp [hfm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun x : ℚ => normalizedFrame n a * x) h2.symm

private theorem actual_gaussian_inversion {a m n : Nat}
    (ha : a ≤ m) (hm : m ≤ n) :
  (gaussian m a : ℚ) / gaussian n a =
    (1 / 2 : ℚ) ^ (a * (n - m)) *
      (normalizedFrame m a / normalizedFrame n a) := by
  have hn : a ≤ n := ha.trans hm
  have hgm : (gaussian m a : ℚ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (actual_gaussian_ne_zero ha)))
  have hgn : (gaussian n a : ℚ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (actual_gaussian_ne_zero hn)))
  have hfm : normalizedFrame m a ≠ 0 :=
    ne_of_gt (normalizedFrame_pos ha)
  have hfn : normalizedFrame n a ≠ 0 :=
    ne_of_gt (normalizedFrame_pos hn)
  have hratio' := actual_gaussian_forward_ratio ha hm
  have hpow : (2 : ℚ) ^ (a * (n - m)) *
      (1 / 2 : ℚ) ^ (a * (n - m)) = 1 := by
    have hbase : (2 : ℚ) * (1 / 2 : ℚ) = 1 := by ring
    rw [← mul_pow, hbase, one_pow]
  have hcross := (div_eq_div_iff hgm hfm).mp hratio'
  have hcross' :
      (gaussian m a : ℚ) * normalizedFrame n a =
        (1 / 2 : ℚ) ^ (a * (n - m)) *
          normalizedFrame m a * (gaussian n a : ℚ) := by
    calc
      (gaussian m a : ℚ) * normalizedFrame n a =
          ((1 / 2 : ℚ) ^ (a * (n - m)) *
            (2 : ℚ) ^ (a * (n - m))) *
            ((gaussian m a : ℚ) * normalizedFrame n a) := by
              have hpow' : (1 / 2 : ℚ) ^ (a * (n - m)) *
                  (2 : ℚ) ^ (a * (n - m)) = 1 := by
                simpa [mul_comm] using hpow
              rw [hpow']
              simp
      _ = (1 / 2 : ℚ) ^ (a * (n - m)) *
            ((2 : ℚ) ^ (a * (n - m)) * normalizedFrame n a) *
              (gaussian m a : ℚ) := by ring
      _ = (1 / 2 : ℚ) ^ (a * (n - m)) *
            ((gaussian n a : ℚ) * normalizedFrame m a) := by
              simpa [mul_assoc] using
                congrArg
                  (fun x : ℚ => (1 / 2 : ℚ) ^ (a * (n - m)) * x)
                  hcross.symm
      _ = (1 / 2 : ℚ) ^ (a * (n - m)) *
            normalizedFrame m a * (gaussian n a : ℚ) := by ring
  apply (div_eq_iff hgn).2
  calc
    (gaussian m a : ℚ) =
        ((gaussian m a : ℚ) * normalizedFrame n a) /
          normalizedFrame n a := by
      exact (mul_div_cancel_right₀ (gaussian m a : ℚ) hfn).symm
    _ = ((1 / 2 : ℚ) ^ (a * (n - m)) *
          normalizedFrame m a * (gaussian n a : ℚ)) /
          normalizedFrame n a := by rw [hcross']
    _ = (1 / 2 : ℚ) ^ (a * (n - m)) *
          (normalizedFrame m a / normalizedFrame n a) *
            (gaussian n a : ℚ) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem gaussian_small_over_large_eq {a m n : Nat}
    (ha : a ≤ m) (hm : m ≤ n) :
  (gaussian m a : ℚ) / gaussian n a =
    (1 / 2 : ℚ) ^ (a * (n - m)) *
      (normalizedFrame m a / normalizedFrame n a) :=
  actual_gaussian_inversion ha hm

theorem gaussian_small_over_large_le {a m n : Nat}
    (ha : a ≤ m) (hm : m ≤ n) :
  (gaussian m a : ℚ) / gaussian n a ≤
    (1 / 2 : ℚ) ^ (a * (n - m)) := by
  rw [gaussian_small_over_large_eq ha hm]
  have hframe : normalizedFrame m a / normalizedFrame n a ≤ 1 := by
    apply (div_le_one (normalizedFrame_pos (ha.trans hm))).mpr
    exact normalizedFrame_mono_ambient ha hm
  have hp : 0 ≤ (1 / 2 : ℚ) ^ (a * (n - m)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hframe hp]

theorem normalizedFrame_relative_mono {a m : Nat}
    (ha : a ≤ m) (c : Nat) :
  normalizedFrame a a / normalizedFrame (a + c) a ≤
    normalizedFrame m a / normalizedFrame (m + c) a := by
  have hB : 0 < normalizedFrame (a + c) a :=
    normalizedFrame_pos (Nat.le_add_right a c)
  have hM : 0 < normalizedFrame m a := normalizedFrame_pos ha
  have hN : 0 < normalizedFrame (m + c) a :=
    normalizedFrame_pos (ha.trans (Nat.le_add_right m c))
  apply (div_le_div_iff₀ hB hN).mpr
  unfold normalizedFrame
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i hi
    have hi' : i < a := Finset.mem_range.mp hi
    have hia : i ≤ a := Nat.le_of_lt hi'
    have him : i ≤ m := hia.trans ha
    have hpow_a : (2 : ℚ)^i ≤ 2^a := by
      exact_mod_cast Nat.pow_le_pow_right Nat.zero_lt_two hia
    have hpow_mc : (2 : ℚ)^i ≤ 2^(m+c) := by
      exact_mod_cast Nat.pow_le_pow_right Nat.zero_lt_two
        (hia.trans (ha.trans (Nat.le_add_right m c)))
    exact mul_nonneg
      (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow_a))
      (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow_mc))
  · intro i hi
    have hi' : i < a := Finset.mem_range.mp hi
    have hia : i ≤ a := Nat.le_of_lt hi'
    have him : i ≤ m := hia.trans ha
    have hpow_a : (2 : ℚ)^i ≤ 2^a := by
      exact_mod_cast Nat.pow_le_pow_right Nat.zero_lt_two hia
    have hpow_m : (2 : ℚ)^i ≤ 2^m := by
      exact_mod_cast Nat.pow_le_pow_right Nat.zero_lt_two him
    have hpow_ac : (2 : ℚ)^i ≤ 2^(a+c) := by
      exact_mod_cast Nat.pow_le_pow_right Nat.zero_lt_two
        (hia.trans (Nat.le_add_right a c))
    have hpow_mc : (2 : ℚ)^i ≤ 2^(m+c) := by
      exact_mod_cast Nat.pow_le_pow_right Nat.zero_lt_two
        (him.trans (Nat.le_add_right m c))
    have hfactor :
        (1 - (2 : ℚ)^i / 2^a) * (1 - (2 : ℚ)^i / 2^(m+c)) ≤
          (1 - (2 : ℚ)^i / 2^(a+c)) * (1 - (2 : ℚ)^i / 2^m) := by
      have hnonneg_a : 0 ≤ 1 - (2 : ℚ)^i / 2^a := by
        exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow_a)
      have hnonneg_m : 0 ≤ 1 - (2 : ℚ)^i / 2^m := by
        exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow_m)
      have hnonneg_ac : 0 ≤ 1 - (2 : ℚ)^i / 2^(a+c) := by
        exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow_ac)
      have hnonneg_mc : 0 ≤ 1 - (2 : ℚ)^i / 2^(m+c) := by
        exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow_mc)
      have hpow_am : (2 : ℚ)^a ≤ 2^m := by
        have hNat : 2^a ≤ 2^m :=
          Nat.pow_le_pow_right Nat.zero_lt_two ha
        exact_mod_cast hNat
      have hpow_c1 : (1 : ℚ) ≤ 2^c := by
        exact_mod_cast (Nat.one_le_pow c 2 Nat.zero_lt_two)
      have hprod : 0 ≤
          (2 : ℚ)^i * (2^c - 1) * ((2 : ℚ)^m - 2^a) := by
        exact mul_nonneg
          (mul_nonneg (by positivity) (sub_nonneg.mpr hpow_c1))
          (sub_nonneg.mpr hpow_am)
      have hquot : 0 ≤
          ((2 : ℚ)^i * (2^c - 1) * ((2 : ℚ)^m - 2^a)) /
            ((2 : ℚ)^a * 2^m * 2^c) := by
        exact div_nonneg hprod (by positivity)
      have hdiff :
          (1 - (2 : ℚ)^i / 2^(a+c)) * (1 - (2 : ℚ)^i / 2^m) -
              (1 - (2 : ℚ)^i / 2^a) * (1 - (2 : ℚ)^i / 2^(m+c)) =
            ((2 : ℚ)^i * (2^c - 1) * ((2 : ℚ)^m - 2^a)) /
              ((2 : ℚ)^a * 2^m * 2^c) := by
        rw [show (2 : ℚ)^(a+c) = 2^a * 2^c by rw [pow_add],
          show (2 : ℚ)^(m+c) = 2^m * 2^c by rw [pow_add]]
        field_simp
        ring
      nlinarith [hquot, hdiff]
    simpa [mul_comm] using hfactor

theorem gaussian_reciprocal_le_shifted_ratio {a m c : Nat}
    (ha : a ≤ m) :
  1 / (gaussian (a + c) a : ℚ) ≤
    (gaussian m a : ℚ) / gaussian (m + c) a := by
  have hleft := gaussian_small_over_large_eq (a := a) (m := a) (n := a+c)
    le_rfl (Nat.le_add_right a c)
  have hright := gaussian_small_over_large_eq (a := a) (m := m) (n := m+c)
    ha (Nat.le_add_right m c)
  have hself : (gaussian a a : ℚ) = 1 := by
    exact_mod_cast gaussian_self a
  rw [hself] at hleft
  have hleft' :
      1 / (gaussian (a + c) a : ℚ) =
        (1 / 2 : ℚ) ^ (a*c) *
          (normalizedFrame a a / normalizedFrame (a+c) a) := by
    simpa [Nat.add_sub_cancel_left] using hleft
  have hright' :
      (gaussian m a : ℚ) / gaussian (m + c) a =
        (1 / 2 : ℚ) ^ (a*c) *
          (normalizedFrame m a / normalizedFrame (m+c) a) := by
    simpa [Nat.add_sub_cancel_left] using hright
  rw [hleft', hright']
  have hrel := normalizedFrame_relative_mono ha c
  have hp : 0 ≤ (1 / 2 : ℚ) ^ (a*c) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hrel hp]

theorem pairCollisionMass_le_gaussianRatio
    {N m J t h k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t)
    (ht : t ≤ 2*h) (hh : h ≤ J) (p : IndexPair k) :
  pairCollisionMass q h ht hh p ≤ cliqueGaussianRatio J h t := by
  rw [pairCollisionMass_eq]
  unfold cliqueGaussianRatio
  have ham : 2*h - t ≤ J + 2*h - t := by
    exact Nat.sub_le_sub_right (Nat.le_add_left (2*h) J) t
  have hmain := gaussian_reciprocal_le_shifted_ratio
    (a := 2*h - t) (m := J + 2*h - t) (c := 2*J - 2*h)
    ham
  have h2h_le_2J : 2*h ≤ 2*J := Nat.mul_le_mul_left 2 hh
  have h1 : (2*h - t) + (2*J - 2*h) = 2*J - t := by
    simpa [add_comm] using tsub_add_tsub_cancel h2h_le_2J ht
  have h2 : (J + 2*h - t) + (2*J - 2*h) = 3*J - t := by
    have hupper : J + 2*h ≤ 3*J := by
      calc
        J + 2*h ≤ J + 2*J := Nat.add_le_add_left h2h_le_2J J
        _ = 3*J := by ring
    have hbase : 3*J - (J + 2*h) = 2*J - 2*h := by
      calc
        3*J - (J + 2*h) = (J + 2*J) - (J + 2*h) := by
          rw [show 3*J = J + 2*J by ring]
        _ = 2*J - 2*h := by rw [Nat.add_sub_add_left]
    calc
      (J + 2*h - t) + (2*J - 2*h) =
          (2*J - 2*h) + (J + 2*h - t) := by ac_rfl
      _ = (3*J - (J + 2*h)) + (J + 2*h - t) := by rw [hbase]
      _ = 3*J - t := tsub_add_tsub_cancel hupper (ht.trans (Nat.le_add_left (2*h) J))
  simpa [h1, h2] using hmain

theorem cliqueGaussianRatio_le_twoNegTwoJ {J h t : Nat}
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (hexp : 2*J ≤ (2*h - t) * (2*J - 2*h)) :
  cliqueGaussianRatio J h t ≤ (1 / 2 : ℚ) ^ (2*J) := by
  have hsmall := gaussian_small_over_large_le
    (a := 2*h - t) (m := J + 2*h - t) (n := 3*J - t)
    (by
      exact Nat.sub_le_sub_right (Nat.le_add_left (2*h) J) t)
    (by
      have h2h_le_2J : 2*h ≤ 2*J := Nat.mul_le_mul_left 2 hh
      have hupper : J + 2*h ≤ 3*J := by
        calc
          J + 2*h ≤ J + 2*J := Nat.add_le_add_left h2h_le_2J J
          _ = 3*J := by ring
      exact Nat.sub_le_sub_right hupper t)
  unfold cliqueGaussianRatio
  have hpow : (1 / 2 : ℚ) ^ ((2*h - t) * (2*J - 2*h)) ≤
      (1 / 2 : ℚ) ^ (2*J) := by
    have hb0 : (0 : ℚ) ≤ 1 / 2 := one_div_nonneg.mpr (by norm_num)
    have hb1 : (1 / 2 : ℚ) ≤ 1 := by norm_num
    exact pow_le_pow_of_le_one hb0 hb1 hexp
  have h2h_le_2J : 2*h ≤ 2*J := Nat.mul_le_mul_left 2 hh
  have hupper : J + 2*h ≤ 3*J := by
    calc
      J + 2*h ≤ J + 2*J := Nat.add_le_add_left h2h_le_2J J
      _ = 3*J := by ring
  have htupper : t ≤ J + 2*h :=
    ht.trans (Nat.le_add_left (2*h) J)
  have hident : (3*J - t) - (J + 2*h - t) = 2*J - 2*h := by
    have hbase : 3*J - (J + 2*h) = 2*J - 2*h := by
      calc
        3*J - (J + 2*h) = (J + 2*J) - (J + 2*h) := by
          rw [show 3*J = J + 2*J by ring]
        _ = 2*J - 2*h := by rw [Nat.add_sub_add_left]
    calc
      (3*J - t) - (J + 2*h - t) = 3*J - (J + 2*h) :=
        tsub_tsub_tsub_cancel_right htupper
      _ = 2*J - 2*h := hbase
  rw [hident] at hsmall
  exact hsmall.trans hpow

theorem card_indexPair (k : Nat) :
    Fintype.card (IndexPair k) = Nat.choose k 2 := by
  classical
  unfold IndexPair
  rw [Fintype.card_subtype]
  simpa using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k))))

theorem cliqueCollision_iff_exists_indexPair
    {N m J t k : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (h : Nat)
    (draws : DomainTuple q h k) :
  CliqueCollision (actualStarLeafVertices q h draws) ↔
    ∃ p : IndexPair k,
      cliqueOf (actualStarLeafVertices q h draws p.1.1) =
        cliqueOf (actualStarLeafVertices q h draws p.1.2) := by
  constructor
  · intro hcoll
    by_contra hnone
    apply hcoll
    intro i j hij
    by_contra hneq
    by_cases hlt : i < j
    · apply hnone
      refine ⟨⟨(i, j), hlt⟩, ?_⟩
      exact hij
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hneq)
      apply hnone
      refine ⟨⟨(j, i), hgt⟩, ?_⟩
      exact hij.symm
  · rintro ⟨p, hp⟩ hdist
    exact p.property.ne (hdist hp)

theorem actualCliqueCollisionMass_le_pairSum
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
  actualCliqueCollisionMass q h k ht hh ≤
    ∑ p : IndexPair k, pairCollisionMass q h ht hh p := by
  letI : Nonempty (DomainTuple q h k) := domainTupleNonempty q h k ht hh
  have hpoint (draws : DomainTuple q h k) :
      (if CliqueCollision (actualStarLeafVertices q h draws) then (1 : ℚ) else 0) ≤
        ∑ p : IndexPair k,
          if cliqueOf (actualStarLeafVertices q h draws p.1.1) =
              cliqueOf (actualStarLeafVertices q h draws p.1.2) then 1 else 0 := by
    by_cases hc : CliqueCollision (actualStarLeafVertices q h draws)
    · obtain ⟨p, hp⟩ :=
        (cliqueCollision_iff_exists_indexPair q h draws).mp hc
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset (IndexPair k)))
        (f := fun r : IndexPair k =>
          if cliqueOf (actualStarLeafVertices q h draws r.1.1) =
              cliqueOf (actualStarLeafVertices q h draws r.1.2) then
            (1 : ℚ) else 0)
        (fun r _ => by
          by_cases hr :
              cliqueOf (actualStarLeafVertices q h draws r.1.1) =
                cliqueOf (actualStarLeafVertices q h draws r.1.2)
          · rw [if_pos hr]
            norm_num
          · rw [if_neg hr])
        (Finset.mem_univ p)
      rw [if_pos hp] at hs
      rw [if_pos hc]
      exact hs
    · simp [hc]
  unfold actualCliqueCollisionMass pairCollisionMass domainTupleMean uniformMean
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right
  · calc
      (∑ x, if CliqueCollision (actualStarLeafVertices q h x) then (1 : ℚ) else 0) ≤
          ∑ x, ∑ p : IndexPair k,
            (if cliqueOf (actualStarLeafVertices q h x p.1.1) =
                cliqueOf (actualStarLeafVertices q h x p.1.2) then 1 else 0) :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = ∑ p : IndexPair k, ∑ x,
          (if cliqueOf (actualStarLeafVertices q h x p.1.1) =
              cliqueOf (actualStarLeafVertices q h x p.1.2) then 1 else 0) := by
        rw [Finset.sum_comm]
  · exact_mod_cast (Nat.zero_le (Fintype.card (DomainTuple q h k)))

theorem actualCliqueCollisionMass_le_choose_mul_ratio
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J) :
  actualCliqueCollisionMass q h k ht hh ≤
    (Nat.choose k 2 : ℚ) * cliqueGaussianRatio J h t := by
  calc
      actualCliqueCollisionMass q h k ht hh ≤
        ∑ p : IndexPair k, pairCollisionMass q h ht hh p :=
      actualCliqueCollisionMass_le_pairSum q k ht hh
    _ ≤ ∑ p : IndexPair k, cliqueGaussianRatio J h t :=
      Finset.sum_le_sum (fun p _ => pairCollisionMass_le_gaussianRatio q ht hh p)
    _ = (Fintype.card (IndexPair k) : ℚ) * cliqueGaussianRatio J h t := by
      simp [Finset.sum_const]
    _ = (Nat.choose k 2 : ℚ) * cliqueGaussianRatio J h t := by
      rw [card_indexPair]

theorem choose_two_le_sq (k : Nat) :
    Nat.choose k 2 ≤ k^2 := by
  rw [Nat.choose_two_right]
  calc
    k * (k - 1) / 2 ≤ k * (k - 1) := Nat.div_le_self _ _
    _ ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le _ _)
    _ = k^2 := by simp [pow_two]

theorem choose_mul_twoNegTwoJ_le_twoNegJ (k J : Nat)
    (hk : k^2 ≤ 2^J) :
  (Nat.choose k 2 : ℚ) * (1 / 2 : ℚ)^(2*J) ≤
    (1 / 2 : ℚ)^J := by
  have hc : (Nat.choose k 2 : ℚ) ≤ (k^2 : ℚ) := by
    exact_mod_cast choose_two_le_sq k
  have hkq : (k^2 : ℚ) ≤ (2^J : ℚ) := by exact_mod_cast hk
  have hpow : (2 : ℚ)^J * (1 / 2 : ℚ)^J = 1 := by
    rw [← mul_pow]
    norm_num
  have htwo : (1 / 2 : ℚ)^(2*J) = (1 / 2 : ℚ)^J * (1 / 2 : ℚ)^J := by
    rw [← pow_add]
    simp [two_mul]
  rw [htwo]
  have hnonneg : 0 ≤ (1 / 2 : ℚ)^J := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (hc.trans hkq) hnonneg]

theorem actualCliqueCollisionMass_le_twoNegJ
    {N m J t h : Nat} {I : ActualOccurrenceAllocation.Instance N m}
    (q : QuestionCenter I J t) (k : Nat)
    (ht : t ≤ 2*h) (hh : h ≤ J)
    (hexp : 2*J ≤ (2*h - t) * (2*J - 2*h))
    (hk : k^2 ≤ 2^J) :
  actualCliqueCollisionMass q h k ht hh ≤
    (1 / 2 : ℚ)^J := by
  calc
    actualCliqueCollisionMass q h k ht hh ≤
        (Nat.choose k 2 : ℚ) * cliqueGaussianRatio J h t :=
      actualCliqueCollisionMass_le_choose_mul_ratio q k ht hh
    _ ≤ (Nat.choose k 2 : ℚ) * (1 / 2 : ℚ)^(2*J) := by
      gcongr
      exact cliqueGaussianRatio_le_twoNegTwoJ ht hh hexp
    _ ≤ (1 / 2 : ℚ)^J := choose_mul_twoNegTwoJ_le_twoNegJ k J hk

end
end PvNP.RealizableHardness.ActualQuestionCenterCollisionBound
