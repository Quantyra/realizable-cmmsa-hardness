import PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
import PvNP.RealizableHardness.GrassmannFlagPosterior

/-! Finite exact source bounds underlying the robust transverse-loss estimate.

This module proves the quotient interval equivalence, quotient-image
intersection transport, the line-union exceptional-mass bound, and its dyadic
consumer.  It does not assert a robust decoder or any CMMSA consequence.
-/

namespace PvNP.RealizableHardness.RobustSourceLineContainment

open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- A fixed line is contained in a uniformly selected `d`-space with the
exact Gaussian ratio.  This is the one-vector incidence estimate used after
passing to the quotient by the fixed advice space in the robust transverse
argument. -/
theorem singleton_upperCount_ratio (K : Grass V 1) {d : ℕ}
    (hd₁ : 1 ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    (upperCount K d : ℚ) / gaussian (Module.finrank (ZMod 2) V) d =
      (gaussian d 1 : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) 1 := by
  let n := Module.finrank (ZMod 2) V
  have hflag := GrassmannFlagPosterior.flag_product
    (V := V) (a := 1) (d := d) (by omega : 1 ≤ d)
  have hcount := GrassmannFlagPosterior.upperCount_eq K hd₁
  have hcast : (gaussian n 1 : ℚ) *
      (gaussian (n - 1) (d - 1) : ℚ) =
        (gaussian n d : ℚ) * (gaussian d 1 : ℚ) := by
    exact_mod_cast hflag
  rw [hcount]
  have hn : gaussian n 1 ≠ 0 := by
    exact Nat.ne_of_gt (gaussian_pos (by omega))
  have hd : gaussian n d ≠ 0 := by
    exact Nat.ne_of_gt (gaussian_pos hdV)
  apply (div_eq_div_iff (by exact_mod_cast hd) (by exact_mod_cast hn)).2
  nlinarith [hcast]

/-- The one-dimensional subspaces of a fixed subspace, represented in the
ambient Grassmann carrier. -/
def linesInside (H : Grass V j) :=
  {K : Grass V 1 // K.val ≤ H.val}

noncomputable instance linesInsideFinite (H : Grass V j) :
    Finite (linesInside H) :=
  Finite.of_injective (fun K : linesInside H => K.val) Subtype.val_injective

noncomputable instance linesInsideFintype (H : Grass V j) :
    Fintype (linesInside H) := Fintype.ofFinite _

/-- The line carrier has the expected Gaussian cardinality. -/
theorem linesInside_card (H : Grass V j) :
    Fintype.card (linesInside H) = gaussian j 1 := by
  classical
  let Q0 : Grass V 0 := ⟨⊥, by simp⟩
  letI : Finite {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val} :=
    Finite.of_injective (fun K : {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val} => K.val)
      Subtype.val_injective
  let e : linesInside H ≃ {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val} := {
    toFun := fun (K : linesInside H) =>
      (⟨K.val, ⟨(show (⊥ : Submodule (ZMod 2) V) ≤ K.val.val from bot_le), K.property⟩⟩ :
        {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val})
    invFun := fun (K : {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val}) =>
      (⟨K.val, K.property.2⟩ : linesInside H)
    left_inv := fun K => rfl
    right_inv := fun K => rfl
  }
  have hcount := GrassmannFlagPosterior.card_relativeUpper H.val Q0 bot_le
    (by omega : 0 ≤ 1)
  have hcardEquiv : Nat.card (linesInside H) =
      Nat.card {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val} := Nat.card_congr e
  have hcount' : Nat.card {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val} = gaussian j 1 := by
    simpa [Q0, H.property] using hcount
  calc
    Fintype.card (linesInside H) = Nat.card (linesInside H) := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card {K : Grass V 1 // (⊥ : Submodule (ZMod 2) V) ≤ K.val ∧ K.val ≤ H.val} := hcardEquiv
    _ = gaussian j 1 := hcount'

/-- Flags in an interval `Q ≤ L ≤ W` are exactly subspaces of dimension
`d-a` in the quotient `W/Q`. -/
def relativeIntervalQuotientEquiv {a d : ℕ}
    (W : Submodule (ZMod 2) V) (Q : Grass V a) (hQ : Q.val ≤ W)
    (had : a ≤ d) :
    {L : Grass V d // Q.val ≤ L.val ∧ L.val ≤ W} ≃
      Grass (W ⧸ (insideAdvice W Q hQ).val) (d - a) :=
  (GrassmannFlagPosterior.relativeUpperEquiv W Q hQ).trans
    (GrassmannFlagPosterior.upperQuotientEquiv
      (insideAdvice W Q hQ) had)

/-- Quotienting by Q preserves whether L meets a Q-disjoint H nontrivially,
provided Q is contained in L. -/
theorem nontrivial_inf_iff_quotientImages
    (Q : Grass V a) (L H : Submodule (ZMod 2) V)
    (hQL : Q.val ≤ L) (hQH : Q.val ⊓ H = ⊥) :
    L ⊓ H ≠ ⊥ ↔
      L.map Q.val.mkQ ⊓ H.map Q.val.mkQ ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨x, ⟨hx, hxne⟩⟩ := (L ⊓ H).ne_bot_iff.mp h
    have hqne : Q.val.mkQ x ≠ 0 := by
      intro hzero
      have hxq : x ∈ Q.val := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hzero
        exact hzero
      have hbot : x ∈ Q.val ⊓ H := ⟨hxq, hx.2⟩
      rw [hQH] at hbot
      exact hxne (by simpa only [Submodule.mem_bot] using hbot)
    apply (L.map Q.val.mkQ ⊓ H.map Q.val.mkQ).ne_bot_iff.mpr
    refine ⟨Q.val.mkQ x, ?_, hqne⟩
    exact ⟨Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩,
      Submodule.mem_map.mpr ⟨x, hx.2, rfl⟩⟩
  · intro h
    obtain ⟨z, ⟨hz, hzne⟩⟩ := (L.map Q.val.mkQ ⊓ H.map Q.val.mkQ).ne_bot_iff.mp h
    obtain ⟨x, hxL, hxz⟩ := Submodule.mem_map.mp hz.1
    obtain ⟨y, hyH, hyz⟩ := Submodule.mem_map.mp hz.2
    have hdiff : y - x ∈ Q.val := by
      have hzero : Q.val.mkQ (y - x) = 0 := by
        rw [map_sub, hxz, hyz]
        exact sub_self _
      have hker : LinearMap.ker Q.val.mkQ = Q.val := Submodule.ker_mkQ Q.val
      rw [← LinearMap.mem_ker, hker] at hzero
      exact hzero
    have hyL : y ∈ L := by
      have hsub : y - x ∈ L := hQL hdiff
      have hrewrite : y = (y - x) + x := by abel
      rw [hrewrite]
      exact L.add_mem hsub hxL
    have hyne : y ≠ 0 := by
      intro hyzero
      apply hzne
      calc
        z = Q.val.mkQ y := hyz.symm
        _ = 0 := by simp [hyzero]
    exact (L ⊓ H).ne_bot_iff.mpr ⟨y, ⟨hyL, hyH⟩, hyne⟩

/-- A subspace disjoint from Q retains its dimension in the quotient. -/
def quotientImageGrass (Q : Grass V a) (H : Submodule (ZMod 2) V)
    (hQH : Q.val ⊓ H = ⊥) (hH : Module.finrank (ZMod 2) H = j) :
    Grass (V ⧸ Q.val) j := by
  have hker : LinearMap.ker (Q.val.mkQ.domRestrict H) = Q.val.comap H.subtype := by
    ext x
    simp
  have hcomap : Q.val.comap H.subtype = ⊥ := by
    apply Submodule.ext
    intro x
    change H.subtype x ∈ Q.val ↔ x = 0
    constructor
    · intro hx
      have hxbot : (H.subtype x : V) ∈ Q.val ⊓ H := ⟨hx, x.property⟩
      rw [hQH] at hxbot
      have hz : (H.subtype x : V) = 0 := by
        simpa only [Submodule.mem_bot] using hxbot
      apply Subtype.ext
      exact hz
    · rintro rfl
      simp
  have hrank := (Q.val.mkQ.domRestrict H).finrank_range_add_finrank_ker
  have hdim : Module.finrank (ZMod 2) (H.map Q.val.mkQ) = j := by
    rw [LinearMap.range_domRestrict, hker, hcomap] at hrank
    simpa [hH] using hrank
  exact ⟨H.map Q.val.mkQ, hdim⟩

/-- The actual interval carrier of `d`-spaces extending Q inside W. -/
def intervalCarrier {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (Q : Grass W a) (d : ℕ) :=
  {L : Grass W d // Q.val ≤ L.val}

noncomputable instance intervalCarrierFinite {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : Grass W a) (d : ℕ) : Finite (intervalCarrier Q d) :=
  Finite.of_injective (fun L : intervalCarrier Q d => L.val) Subtype.val_injective

noncomputable instance intervalCarrierFintype {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : Grass W a) (d : ℕ) : Fintype (intervalCarrier Q d) := Fintype.ofFinite _

/-- The exceptional part of that interval for a fixed disjoint subspace H. -/
def intervalTransverseCarrier {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (Q : Grass W a) (H : Grass W j) (d : ℕ) :=
  {L : intervalCarrier Q d // L.val.val ⊓ H.val ≠ ⊥}

noncomputable instance intervalTransverseCarrierFinite {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : Grass W a) (H : Grass W j) (d : ℕ) :
    Finite (intervalTransverseCarrier Q H d) :=
  Finite.of_injective (fun L : intervalTransverseCarrier Q H d => L.val)
    Subtype.val_injective

noncomputable instance intervalTransverseCarrierFintype {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : Grass W a) (H : Grass W j) (d : ℕ) :
    Fintype (intervalTransverseCarrier Q H d) := Fintype.ofFinite _

/-- In a uniform Grassmann carrier, the mass of subspaces meeting a fixed
subspace nontrivially is bounded by the exact first-moment union estimate.
This is stated on the quotient-space carrier: the later interval equivalence
identifies it with flags above a fixed Q inside W. -/
theorem transverseException_mass_le_gaussian (H : Grass V j) {d : ℕ}
    (hd₁ : 1 ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    ((Finset.univ.filter fun L : Grass V d => L.val ⊓ H.val ≠ ⊥).card : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) d ≤
      (gaussian j 1 : ℚ) *
        (gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) : ℚ) /
          gaussian (Module.finrank (ZMod 2) V) d := by
  classical
  let F : linesInside H → Finset (Grass V d) := fun K =>
    Finset.univ.filter fun L => K.val.val ≤ L.val
  let bad : Finset (Grass V d) :=
    Finset.univ.filter fun L => L.val ⊓ H.val ≠ ⊥
  have hfiber (K : linesInside H) :
      (F K).card = gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) := by
    have hc := GrassmannFlagPosterior.card_upper K.val hd₁
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    simpa [F, GrassmannFlagPosterior.upperCount] using hc
  have hcover : bad ⊆ Finset.univ.biUnion F := by
    intro L hL
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    obtain ⟨x, ⟨hx, hxne⟩⟩ := (L.val ⊓ H.val).ne_bot_iff.mp hL
    have hxL : x ∈ L.val := hx.1
    have hxH : x ∈ H.val := hx.2
    let K : Grass V 1 :=
      ⟨Submodule.span (ZMod 2) ({x} : Set V), finrank_span_singleton hxne⟩
    have hKH : K.val ≤ H.val := by
      apply Submodule.span_le.mpr
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      simpa [hyx] using hxH
    have hKL : K.val ≤ L.val := by
      apply Submodule.span_le.mpr
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      simpa [hyx] using hxL
    let Kline : linesInside H := ⟨K, hKH⟩
    have hK : Kline ∈ (Finset.univ : Finset (linesInside H)) := Finset.mem_univ _
    refine Finset.mem_biUnion.mpr ⟨Kline, hK, ?_⟩
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hKL
  have hunion : (Finset.univ.biUnion F).card ≤
      Fintype.card (linesInside H) *
        gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) := by
    calc
      _ ≤ (Finset.univ : Finset (linesInside H)).card *
          gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro K hK
        exact le_of_eq (hfiber K)
      _ = _ := by simp
  have hcard := Finset.card_le_card hcover
  have hcard' : (bad.card : ℚ) ≤
      (gaussian j 1 : ℚ) *
        (gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) : ℚ) := by
    have hline := linesInside_card H
    have hNat : bad.card ≤ Fintype.card (linesInside H) *
        gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) := hcard.trans hunion
    exact_mod_cast (by simpa [bad, hline] using hNat)
  have hden : (0 : ℚ) < gaussian (Module.finrank (ZMod 2) V) d := by
    exact_mod_cast gaussian_pos hdV
  apply (div_le_div_iff_of_pos_right hden).2
  exact hcard'

/-- Simplified first-moment form, obtained by the flag double count. -/
theorem transverseException_mass_le_pointRatio (H : Grass V j) {d : ℕ}
    (hd₁ : 1 ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V) :
    ((Finset.univ.filter fun L : Grass V d => L.val ⊓ H.val ≠ ⊥).card : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) d ≤
      (gaussian j 1 : ℚ) * (gaussian d 1 : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) 1 := by
  have hmass := transverseException_mass_le_gaussian H hd₁ hdV
  have hflag := GrassmannFlagPosterior.flag_product
    (V := V) (a := 1) (d := d) hd₁
  have hcast : (gaussian (Module.finrank (ZMod 2) V) 1 : ℚ) *
      (gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) : ℚ) =
        (gaussian (Module.finrank (ZMod 2) V) d : ℚ) *
          (gaussian d 1 : ℚ) := by
    exact_mod_cast hflag
  have hden : (gaussian (Module.finrank (ZMod 2) V) d : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussian_pos hdV)
  have hden1 : (gaussian (Module.finrank (ZMod 2) V) 1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (gaussian_pos (by have := hd₁; omega : 1 ≤ Module.finrank (ZMod 2) V))
  have hr : (gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) d =
      (gaussian d 1 : ℚ) / gaussian (Module.finrank (ZMod 2) V) 1 := by
    apply (div_eq_div_iff hden hden1).2
    nlinarith [hcast]
  have hmass' :
      ((Finset.univ.filter fun L : Grass V d => L.val ⊓ H.val ≠ ⊥).card : ℚ) /
          gaussian (Module.finrank (ZMod 2) V) d ≤
        (gaussian j 1 : ℚ) *
          ((gaussian d 1 : ℚ) /
            gaussian (Module.finrank (ZMod 2) V) 1) := by
    calc
      _ ≤ (gaussian j 1 : ℚ) *
          ((gaussian (Module.finrank (ZMod 2) V - 1) (d - 1) : ℚ) /
            gaussian (Module.finrank (ZMod 2) V) d) := by
              simpa only [mul_div_assoc] using hmass
      _ = _ := congrArg (fun x : ℚ => (gaussian j 1 : ℚ) * x) hr
  simpa [mul_div_assoc] using hmass'

/-- The one-dimensional Gaussian coefficient is the number of nonzero
vectors over `GF(2)`. -/
theorem gaussian_one_eq_pow_sub_one (n : ℕ) :
    gaussian n 1 = 2 ^ n - 1 := by
  cases n with
  | zero => simp [GrassmannCounting.gaussian]
  | succ n => simp [GrassmannCounting.gaussian, GrassmannCounting.frameProduct]

lemma gaussian_one_cast (n : ℕ) :
    (gaussian n 1 : ℚ) = (2 : ℚ) ^ n - 1 := by
  rw [gaussian_one_eq_pow_sub_one]
  have hpow : (2 : ℕ) ^ n ≠ 0 := by positivity
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hpow)]
  norm_num

lemma one_le_two_pow (n : ℕ) : (1 : ℚ) ≤ (2 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith

/-- Dyadic form consumed by the manuscript's transverse-loss calculation.
When `j+d+1≤n`, the exceptional mass is at most
`2^(-(n-j-d-1))`, written without negative exponents. -/
theorem transverseException_mass_le_dyadic (H : Grass V j) {d : ℕ}
    (hd₁ : 1 ≤ d) (hdV : d ≤ Module.finrank (ZMod 2) V)
    (hslack : j + d + 1 ≤ Module.finrank (ZMod 2) V) :
    ((Finset.univ.filter fun L : Grass V d => L.val ⊓ H.val ≠ ⊥).card : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) d ≤
      1 / (2 : ℚ) ^
        (Module.finrank (ZMod 2) V - j - d - 1) := by
  let n := Module.finrank (ZMod 2) V
  have hratio := transverseException_mass_le_pointRatio H hd₁ hdV
  have hnum : (gaussian j 1 : ℚ) * (gaussian d 1 : ℚ) ≤
      (2 : ℚ) ^ (j + d) := by
    rw [gaussian_one_cast j, gaussian_one_cast d]
    have hjp : (0 : ℚ) ≤ 2 ^ j := by positivity
    have hdp : (0 : ℚ) ≤ 2 ^ d := by positivity
    have hpow : (2 : ℚ) ^ j * 2 ^ d = 2 ^ (j + d) := by rw [← pow_add]
    have hleft : (2 : ℚ) ^ j - 1 ≤ 2 ^ j := by linarith
    have hright : (2 : ℚ) ^ d - 1 ≤ 2 ^ d := by linarith
    have hleft' : 0 ≤ (2 : ℚ) ^ j - 1 := by
      linarith [one_le_two_pow j]
    have hright' : 0 ≤ (2 : ℚ) ^ d - 1 := by
      linarith [one_le_two_pow d]
    calc
      ((2 : ℚ) ^ j - 1) * ((2 : ℚ) ^ d - 1) ≤
          (2 : ℚ) ^ j * (2 : ℚ) ^ d := by nlinarith
      _ = (2 : ℚ) ^ (j + d) := hpow
  have hn₁ : 1 ≤ n := by dsimp [n]; omega
  have hdenpow : (2 : ℚ) ^ (n - 1) ≤ gaussian n 1 := by
    rw [gaussian_one_cast n]
    have hpow : (2 : ℚ) ^ (n - 1 + 1) = 2 ^ (n - 1) * 2 := by
      rw [pow_succ]
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn₁
    rw [hnsub] at hpow
    have hbase := one_le_two_pow (n - 1)
    nlinarith [hpow, hbase]
  have hslack' : j + d + 1 ≤ n := by dsimp [n]; exact hslack
  let k := n - (j + d + 1)
  have hk : k = n - j - d - 1 := by dsimp [k]; omega
  have hsum : n = (j + d + 1) + k := by dsimp [k]; omega
  have hE : n = (j + d) + (n - j - d - 1) + 1 := by
    rw [← hk]
    omega
  have hpowE : (2 : ℚ) ^ (j + d) *
      (2 : ℚ) ^ (n - j - d - 1) = (2 : ℚ) ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have htarget :
      (gaussian j 1 : ℚ) * (gaussian d 1 : ℚ) *
        (2 : ℚ) ^ (n - j - d - 1) ≤ gaussian n 1 := by
    calc
      _ ≤ (2 : ℚ) ^ (j + d) * (2 : ℚ) ^ (n - j - d - 1) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = (2 : ℚ) ^ (n - 1) := hpowE
      _ ≤ gaussian n 1 := hdenpow
  have hden : (0 : ℚ) < gaussian n 1 := by
    rw [gaussian_one_cast n]
    have hp : (1 : ℚ) < (2 : ℚ) ^ n := by
      have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn₁
      rw [← hnsub, pow_succ]
      have hn := one_le_two_pow (n - 1)
      nlinarith
    linarith
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ (n - j - d - 1) := by positivity
  have hbound :
      (gaussian j 1 : ℚ) * (gaussian d 1 : ℚ) / gaussian n 1 ≤
        1 / (2 : ℚ) ^ (n - j - d - 1) := by
    apply (div_le_div_iff₀ hden hpowpos).2
    nlinarith [htarget]
  have hratio' := hratio
  dsimp [n] at hratio'
  exact le_trans hratio' hbound

/-- The manuscript's exceptional-mass bound for the actual interval law above
Q inside the ambient space W.  It is obtained by the quotient interval
equivalence, the quotient-image intersection equivalence, and the proved
line-union estimate; no transverse-mass premise is assumed. -/
theorem intervalTransverseException_mass_le_dyadic
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : Grass W a) (H : Grass W j) {d : ℕ}
    (had : a ≤ d) (hd : d ≤ Module.finrank (ZMod 2) W)
    (hQH : Q.val ⊓ H.val = ⊥)
    (hbd : 1 ≤ d - a)
    (hslack : j + (d - a) + 1 ≤ Module.finrank (ZMod 2) W - a) :
    ((Fintype.card (intervalTransverseCarrier Q H d) : ℚ) /
      (Fintype.card (intervalCarrier Q d) : ℚ)) ≤
      1 / (2 : ℚ) ^
        (Module.finrank (ZMod 2) W - a - j - (d - a) - 1) := by
  classical
  let carrier := intervalCarrier Q d
  let bad := intervalTransverseCarrier Q H d
  let Hq := quotientImageGrass Q H.val hQH H.property
  let e := GrassmannFlagPosterior.upperQuotientEquiv Q had
  have hbad (L : carrier) :
      L.val.val ⊓ H.val ≠ ⊥ ↔ (e L).val ⊓ Hq.val ≠ ⊥ := by
    change L.val.val ⊓ H.val ≠ ⊥ ↔
      L.val.val.map Q.val.mkQ ⊓ H.val.map Q.val.mkQ ≠ ⊥
    exact nontrivial_inf_iff_quotientImages Q L.val.val H.val L.property hQH
  letI : Finite (W ⧸ Q.val) :=
    Finite.of_surjective Q.val.mkQ Q.val.mkQ_surjective
  let badQ := {R : Grass (W ⧸ Q.val) (d - a) // R.val ⊓ Hq.val ≠ ⊥}
  letI : Finite badQ := Finite.of_injective (fun R : badQ => R.val) Subtype.val_injective
  letI : Fintype badQ := Fintype.ofFinite _
  let badEquiv :
      {L : {L : Grass W d // Q.val ≤ L.val} // L.val.val ⊓ H.val ≠ ⊥} ≃
        {R : Grass (W ⧸ Q.val) (d - a) //
          R.val ⊓ (quotientImageGrass Q H.val hQH H.property).val ≠ ⊥} := {
    toFun := fun (L : {L : {L : Grass W d // Q.val ≤ L.val} //
        L.val.val ⊓ H.val ≠ ⊥}) =>
      (⟨GrassmannFlagPosterior.upperQuotientEquiv Q had L.val,
        (hbad L.val).mp L.property⟩ :
          {R : Grass (W ⧸ Q.val) (d - a) //
            R.val ⊓ (quotientImageGrass Q H.val hQH H.property).val ≠ ⊥})
    invFun := fun (R : {R : Grass (W ⧸ Q.val) (d - a) //
        R.val ⊓ (quotientImageGrass Q H.val hQH H.property).val ≠ ⊥}) =>
      ⟨(GrassmannFlagPosterior.upperQuotientEquiv Q had).symm R.val,
        (hbad ((GrassmannFlagPosterior.upperQuotientEquiv Q had).symm R.val)).mpr
        (by
          have hinv := Equiv.apply_symm_apply
            (GrassmannFlagPosterior.upperQuotientEquiv Q had) R.val
          rw [hinv]
          exact R.property)⟩
    left_inv := fun (L : {L : {L : Grass W d // Q.val ≤ L.val} //
        L.val.val ⊓ H.val ≠ ⊥}) => by
      apply Subtype.ext
      exact Equiv.left_inv (GrassmannFlagPosterior.upperQuotientEquiv Q had) L.val
    right_inv := fun (R : {R : Grass (W ⧸ Q.val) (d - a) //
        R.val ⊓ (quotientImageGrass Q H.val hQH H.property).val ≠ ⊥}) => by
      apply Subtype.ext
      exact Equiv.right_inv (GrassmannFlagPosterior.upperQuotientEquiv Q had) R.val
  }
  have hbadCard : Fintype.card bad = Fintype.card badQ := Fintype.card_congr badEquiv
  have hcarrierCard : Fintype.card carrier =
      gaussian (Module.finrank (ZMod 2) W - a) (d - a) := by
    have hc := GrassmannFlagPosterior.card_upper Q had
    calc
      Fintype.card carrier = Nat.card carrier := by rw [Nat.card_eq_fintype_card]
      _ = Nat.card {L : Grass W d // Q.val ≤ L.val} := rfl
      _ = gaussian (Module.finrank (ZMod 2) W - a) (d - a) := hc
  have hbadQCard : Fintype.card badQ =
      (Finset.univ.filter fun R : Grass (W ⧸ Q.val) (d - a) =>
        R.val ⊓ Hq.val ≠ ⊥).card := by
    simp [badQ, Fintype.card_subtype]
  have hmass :
      (Fintype.card bad : ℚ) / Fintype.card carrier =
        ((Finset.univ.filter fun R : Grass (W ⧸ Q.val) (d - a) =>
          R.val ⊓ Hq.val ≠ ⊥).card : ℚ) /
          gaussian (Module.finrank (ZMod 2) W - a) (d - a) := by
    rw [hbadCard, hbadQCard, hcarrierCard]
  have hquot := Q.val.finrank_quotient_add_finrank
  rw [Q.property] at hquot
  have hquotEq : Module.finrank (ZMod 2) (W ⧸ Q.val) =
      Module.finrank (ZMod 2) W - a := by omega
  have hdq : d - a ≤ Module.finrank (ZMod 2) (W ⧸ Q.val) := by
    rw [hquotEq]
    omega
  have hqbound := transverseException_mass_le_dyadic Hq hbd hdq
    (by rw [hquotEq]; exact hslack)
  rw [hmass]
  simpa [hquotEq] using hqbound

end
end PvNP.RealizableHardness.RobustSourceLineContainment
