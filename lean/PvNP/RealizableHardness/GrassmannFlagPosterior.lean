/- UNCOMPILED source draft. All proof scripts below await compilation and independent review. -/
import PvNP.RealizableHardness.GrassmannCounting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PvNP.RealizableHardness.GrassmannFlagPosterior
open scoped BigOperators
open TripleRestrictionRank GrassmannCounting
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Rank-nullity for the actual quotient map restricted to a containing space. -/
lemma quotient_map_dimension (Q L : Submodule (ZMod 2) V) (hQL : Q ≤ L) :
    Module.finrank (ZMod 2) (L.map Q.mkQ) + Module.finrank (ZMod 2) Q =
      Module.finrank (ZMod 2) L := by
  have h := (Q.mkQ.domRestrict L).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (Q.mkQ.domRestrict L) = Q.comap L.subtype := by
    ext x
    simp
  rw [LinearMap.range_domRestrict, hk] at h
  rw [(Submodule.comapSubtypeEquivOfLe hQL).finrank_eq] at h
  exact h

/-- Dimension-filtered correspondence theorem: no fibre-count assumption. -/
def upperQuotientEquiv (Q : Grass V a) (had : a ≤ d) :
    {L : Grass V d // Q.val ≤ L.val} ≃ Grass (V ⧸ Q.val) (d - a) where
  toFun L := ⟨L.val.val.map Q.val.mkQ, by
    have h := quotient_map_dimension Q.val L.val.val L.property
    rw [Q.property, L.val.property] at h
    omega⟩
  invFun R := ⟨⟨R.val.comap Q.val.mkQ, by
    have h := quotient_map_dimension Q.val (R.val.comap Q.val.mkQ)
      (Submodule.le_comap_mkQ Q.val R.val)
    have hm : (R.val.comap Q.val.mkQ).map Q.val.mkQ = R.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [hm, R.property, Q.property] at h
    omega⟩, Submodule.le_comap_mkQ Q.val R.val⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Submodule.comap_map_mkQ] using
      (sup_eq_right.mpr L.property : Q.val ⊔ L.val.val = L.val.val)
  right_inv R := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

/-- Per-Q upper fibre count obtained from an actual quotient equivalence. -/
lemma card_upper (Q : Grass V a) (had : a ≤ d) :
    Nat.card {L : Grass V d // Q.val ≤ L.val} =
      gaussian (Module.finrank (ZMod 2) V - a) (d - a) := by
  letI : Finite (V ⧸ Q.val) := Finite.of_surjective Q.val.mkQ Q.val.mkQ_surjective
  rw [Nat.card_congr (upperQuotientEquiv Q had), Nat.card_eq_fintype_card, card_grass]
  have h := Q.val.finrank_quotient_add_finrank
  rw [Q.property] at h
  congr 1
  omega

/-- Number of actual d-subspaces containing the fixed actual a-subspace. -/
def upperCount (Q : Grass V a) (d : ℕ) : ℕ :=
  ∑ L : Grass V d, if Q.val ≤ L.val then 1 else 0

lemma upperCount_eq (Q : Grass V a) (had : a ≤ d) :
    upperCount Q d = gaussian (Module.finrank (ZMod 2) V - a) (d - a) := by
  have h := card_upper Q had
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa only [upperCount, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, Nat.cast_id, mul_one] using h

lemma lowerCount (L : Grass V d) :
    (∑ Q : Grass V a, if Q.val ≤ L.val then (1 : ℕ) else 0) = gaussian d a := by
  have h := card_contained (a := a) L.val
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa only [L.property, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, Nat.cast_id, mul_one] using h

/-- Aggregate double count; per-Q regularity is a separate obligation. -/
lemma sum_upperCount :
    (∑ Q : Grass V a, upperCount Q d) =
      gaussian (Module.finrank (ZMod 2) V) d * gaussian d a := by
  unfold upperCount
  rw [Finset.sum_comm]
  simp only [lowerCount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id, card_grass]

lemma flag_product (had : a ≤ d) :
    gaussian (Module.finrank (ZMod 2) V) a *
      gaussian (Module.finrank (ZMod 2) V - a) (d - a) =
    gaussian (Module.finrank (ZMod 2) V) d * gaussian d a := by
  have h := sum_upperCount (V := V) (a := a) (d := d)
  simpa only [upperCount_eq _ had, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id, card_grass] using h

/-- Internal per-Q probability, obtained from regularity and double counting. -/
lemma upperCount_ratio (Q : Grass V a) (had : a ≤ d)
    (ha : gaussian (Module.finrank (ZMod 2) V) a ≠ 0)
    (hd : gaussian (Module.finrank (ZMod 2) V) d ≠ 0) :
    (upperCount Q d : ℚ) / gaussian (Module.finrank (ZMod 2) V) d =
      (gaussian d a : ℚ) / gaussian (Module.finrank (ZMod 2) V) a := by
  have h : (gaussian (Module.finrank (ZMod 2) V) a : ℚ) *
      gaussian (Module.finrank (ZMod 2) V - a) (d - a) =
      (gaussian (Module.finrank (ZMod 2) V) d : ℚ) * gaussian d a := by
    exact_mod_cast flag_product (V := V) had
  rw [upperCount_eq Q had]
  apply (div_eq_div_iff (by exact_mod_cast hd) (by exact_mod_cast ha)).mpr
  nlinarith

def insideAdvice (W : Submodule (ZMod 2) V) (Q : Grass V a) (hQ : Q.val ≤ W) :
    Grass W a :=
  ⟨Q.val.comap W.subtype, by
    rw [(Submodule.comapSubtypeEquivOfLe hQ).finrank_eq, Q.property]⟩

/-- Actual flags inside W correspond to upper flags in W as a vector space. -/
def relativeUpperEquiv (W : Submodule (ZMod 2) V) (Q : Grass V a) (hQ : Q.val ≤ W) :
    {L : Grass V d // Q.val ≤ L.val ∧ L.val ≤ W} ≃
      {R : Grass W d // (insideAdvice W Q hQ).val ≤ R.val} where
  toFun L := ⟨insideAdvice W L.val L.property.2,
    Submodule.comap_mono L.property.1⟩
  invFun R := ⟨⟨R.val.val.map W.subtype, by
    rw [Submodule.finrank_map_subtype_eq, R.val.property]⟩, by
    constructor
    · intro x hx
      exact ⟨⟨x, hQ hx⟩, R.property hx, rfl⟩
    · exact W.map_subtype_le R.val.val⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Submodule.map_comap_subtype W L.val.val).trans
      (inf_eq_right.mpr L.property.2)
  right_inv R := by
    apply Subtype.ext
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective W.injective_subtype R.val.val

lemma card_relativeUpper (W : Submodule (ZMod 2) V) (Q : Grass V a)
    (hQ : Q.val ≤ W) (had : a ≤ d) :
    Nat.card {L : Grass V d // Q.val ≤ L.val ∧ L.val ≤ W} =
      gaussian (Module.finrank (ZMod 2) W - a) (d - a) := by
  rw [Nat.card_congr (relativeUpperEquiv W Q hQ)]
  exact card_upper (insideAdvice W Q hQ) had

/-- Actual uniform-L event probability, including zero denominators. -/
def containmentProbability (s : Draw J) (d : ℕ)
    (Q : GrassmannIncidence.Advice J a) : ℚ :=
  ∑ L : GrassmannIncidence.Advice J d,
    if Q.val ≤ L.val then GrassmannIncidence.kernel s L else 0

lemma containmentProbability_count (s : Draw J) (d : ℕ)
    (Q : GrassmannIncidence.Advice J a) :
    containmentProbability s d Q =
      (Nat.card {L : Grass (Vector J) d // Q.val ≤ L.val ∧ L.val ≤ retained s} : ℚ) /
        GrassmannIncidence.incidenceCount s d := by
  calc
    _ = ∑ L ∈ (Finset.univ.filter (fun L : Grass (Vector J) d =>
        Q.val ≤ L.val ∧ L.val ≤ retained s)),
        (GrassmannIncidence.incidenceCount s d : ℚ)⁻¹ := by
      rw [Finset.sum_filter]
      unfold containmentProbability GrassmannIncidence.kernel
      apply Finset.sum_congr rfl
      intro L _
      by_cases hQ : Q.val ≤ L.val <;> by_cases hL : L.val ≤ retained s <;>
        simp [hQ, hL]
    _ = _ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [div_eq_mul_inv, nsmul_eq_mul]

lemma containmentProbability_noncontainment (s : Draw J) (d : ℕ)
    (Q : GrassmannIncidence.Advice J a) (h : ¬ Q.val ≤ retained s) :
    containmentProbability s d Q = 0 := by
  apply Finset.sum_eq_zero
  intro L _
  by_cases hQL : Q.val ≤ L.val
  · have hLV : ¬ L.val ≤ retained s := fun hLV => h (hQL.trans hLV)
    simp [hQL, GrassmannIncidence.kernel, hLV]
  · simp [hQL]

lemma containmentProbability_formula (s : Draw J) (d : ℕ)
    (Q : GrassmannIncidence.Advice J a) (had : a ≤ d) (hdJ : d ≤ J) :
    containmentProbability s d Q =
      (gaussian d a : ℚ) * GrassmannIncidence.kernel s Q := by
  by_cases hQ : Q.val ≤ retained s
  · have ha : gaussian (Module.finrank (ZMod 2) (retained s)) a ≠ 0 := by
      rw [← incidenceCount_eq]
      exact Nat.ne_of_gt (GrassmannIncidence.incidenceCount_pos s (had.trans hdJ))
    have hd : gaussian (Module.finrank (ZMod 2) (retained s)) d ≠ 0 := by
      rw [← incidenceCount_eq]
      exact Nat.ne_of_gt (GrassmannIncidence.incidenceCount_pos s hdJ)
    rw [containmentProbability_count, card_relativeUpper (retained s) Q hQ had,
      incidenceCount_eq]
    have h := upperCount_ratio (insideAdvice (retained s) Q hQ) had ha hd
    rw [upperCount_eq _ had] at h
    simpa [GrassmannIncidence.kernel, hQ, incidenceCount_eq, div_eq_mul_inv] using h
  · rw [containmentProbability_noncontainment s d Q hQ]
    simp [GrassmannIncidence.kernel, hQ]

def eventMarginal (β : ℚ) (d : ℕ) (Q : GrassmannIncidence.Advice J a) : ℚ :=
  ∑ s : Draw J, GrassmannIncidence.prior β s * containmentProbability s d Q

/-- Null mass yields algebraic zero, not a normalized conditional law. -/
def eventPosterior (β : ℚ) (d : ℕ) (Q : GrassmannIncidence.Advice J a)
    (s : Draw J) : ℚ :=
  GrassmannIncidence.prior β s * containmentProbability s d Q / eventMarginal β d Q

lemma eventPosterior_null (β : ℚ) (d : ℕ) (Q : GrassmannIncidence.Advice J a)
    (h : eventMarginal β d Q = 0) (s : Draw J) : eventPosterior β d Q s = 0 := by
  simp [eventPosterior, h]

lemma eventMarginal_formula (β : ℚ) (d : ℕ) (Q : GrassmannIncidence.Advice J a)
    (had : a ≤ d) (hdJ : d ≤ J) :
    eventMarginal β d Q = (gaussian d a : ℚ) * GrassmannIncidence.adviceMarginal β Q := by
  unfold eventMarginal GrassmannIncidence.adviceMarginal PosteriorReweighting.marginal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [containmentProbability_formula _ _ _ had hdJ]
  ring

/-- Actual sampler identification; the positive event hypothesis justifies cancellation. -/
theorem eventPosterior_eq_conditional (β : ℚ) (d : ℕ)
    (Q : GrassmannIncidence.Advice J a) (had : a ≤ d) (hdJ : d ≤ J)
    (hpos : 0 < eventMarginal β d Q) (s : Draw J) :
    eventPosterior β d Q s = GrassmannIncidence.conditional β Q s := by
  have he := eventMarginal_formula β d Q had hdJ
  have hc : (gaussian d a : ℚ) ≠ 0 := by
    intro hc
    rw [he, hc, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hm : GrassmannIncidence.adviceMarginal β Q ≠ 0 := by
    intro hm
    rw [he, hm, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  unfold eventPosterior
  rw [containmentProbability_formula _ _ _ had hdJ, he]
  change _ = GrassmannIncidence.prior β s * GrassmannIncidence.kernel s Q /
    GrassmannIncidence.adviceMarginal β Q
  field_simp [hc, hm]

end
end PvNP.RealizableHardness.GrassmannFlagPosterior
