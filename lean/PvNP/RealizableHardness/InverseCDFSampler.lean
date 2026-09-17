import PvNP.RealizableHardness.FiniteSampling
import Mathlib.Data.Nat.Find

namespace PvNP.RealizableHardness.InverseCDFSampler
open scoped BigOperators
open FiniteSampling

lemma support_pos (p : ℕ → ℚ) (S : ℕ) (hn : cumulative p S = 1) : 0 < S := by
  by_contra h
  have : S = 0 := by omega
  simp [this] at hn

lemma cut_zero (p : ℕ → ℚ) (D : ℕ) : cut p D 0 = 0 := by simp [cut]
lemma cut_endpoint (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1) :
    cut p D S = D := by simp [cut, hn]
lemma cut_monotone (p : ℕ → ℚ) (D : ℕ) (hp : ∀ i, 0 ≤ p i) : Monotone (cut p D) :=
  monotone_nat_of_le_succ (cut_mono p D hp)

lemma crossing_exists (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1) (r : Fin D) :
    ∃ j, r.val < cut p D (j + 1) := by
  have hs := support_pos p S hn
  refine ⟨S - 1, ?_⟩
  rw [Nat.sub_add_cancel hs, cut_endpoint p D S hn]
  exact r.isLt

/-- Search for the first cumulative cut strictly above the seed. The proved endpoint bounds
this search by S, including repeated cuts from zero-mass atoms. -/
def sampler (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1) (r : Fin D) : Fin S :=
  ⟨Nat.find (crossing_exists p D S hn r), by
    have h := Nat.find_min' (crossing_exists p D S hn r)
      (show r.val < cut p D ((S - 1) + 1) by
        rw [Nat.sub_add_cancel (support_pos p S hn), cut_endpoint p D S hn]
        exact r.isLt)
    have := support_pos p S hn
    omega⟩

lemma sampler_interval (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1) (r : Fin D) :
    cut p D (sampler p D S hn r).val ≤ r.val ∧
      r.val < cut p D ((sampler p D S hn r).val + 1) := by
  constructor
  · by_cases hz : (sampler p D S hn r).val = 0
    · rw [hz, cut_zero]; omega
    · have hlt : (sampler p D S hn r).val - 1 < (sampler p D S hn r).val := by omega
      have h := Nat.find_min (crossing_exists p D S hn r) hlt
      have he : (sampler p D S hn r).val - 1 + 1 = (sampler p D S hn r).val := by omega
      rw [he] at h
      omega
  · exact Nat.find_spec (crossing_exists p D S hn r)

lemma sampler_eq_iff (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1)
    (hp : ∀ j, 0 ≤ p j) (r : Fin D) (i : Fin S) :
    sampler p D S hn r = i ↔ cut p D i.val ≤ r.val ∧ r.val < cut p D (i.val + 1) := by
  constructor
  · intro h; simpa [h] using sampler_interval p D S hn r
  · intro hi
    have hs := sampler_interval p D S hn r
    have hm := cut_monotone p D hp
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hc := hm (show (sampler p D S hn r).val + 1 ≤ i.val by omega)
      omega
    · have hc := hm (show i.val + 1 ≤ (sampler p D S hn r).val by omega)
      omega

/-- The fibre is an explicit interval translated to Fin of its length. -/
def fibreEquiv (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1)
    (hp : ∀ j, 0 ≤ p j) (i : Fin S) :
    {r : Fin D // sampler p D S hn r = i} ≃ Fin (cut p D (i.val + 1) - cut p D i.val) where
  toFun r := ⟨r.val.val - cut p D i.val, by
    have h := (sampler_eq_iff p D S hn hp r.val i).mp r.property
    omega⟩
  invFun k := ⟨⟨cut p D i.val + k.val, by
    have hm := cut_monotone p D hp
    have hc := hm (show i.val + 1 ≤ S by omega)
    rw [cut_endpoint p D S hn] at hc
    have hk := k.isLt
    omega⟩, by
      apply (sampler_eq_iff p D S hn hp _ i).mpr
      have hk := k.isLt
      constructor <;> dsimp <;> omega⟩
  left_inv r := by
    apply Subtype.ext
    apply Fin.ext
    have h := (sampler_eq_iff p D S hn hp r.val i).mp r.property
    dsimp
    omega
  right_inv k := by
    apply Fin.ext
    dsimp
    omega

theorem fibre_card (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1)
    (hp : ∀ j, 0 ≤ p j) (i : Fin S) :
    Fintype.card {r : Fin D // sampler p D S hn r = i} =
      cut p D (i.val + 1) - cut p D i.val := by
  simpa using Fintype.card_congr (fibreEquiv p D S hn hp i)

theorem fibre_probability (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1)
    (hp : ∀ j, 0 ≤ p j) (i : Fin S) :
    (Fintype.card {r : Fin D // sampler p D S hn r = i} : ℚ) / D = mass p D i.val := by
  rw [fibre_card p D S hn hp i, Nat.cast_sub (cut_mono p D hp i.val)]
  simp [mass, roundedCumulative, sub_div]

theorem sampler_event_law (p : ℕ → ℚ) (D S : ℕ) (hn : cumulative p S = 1)
    (hp : ∀ j, 0 ≤ p j) (event : ℕ → Bool) :
    average (fun r : Fin D => event (sampler p D S hn r).val) =
      eventMass (mass p D) S event := by
  unfold average
  rw [← Fintype.sum_fiberwise' (sampler p D S hn)
    (fun i : Fin S => if event i.val then (1 : ℚ) else 0)]
  simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
  rw [Finset.sum_div]
  unfold eventMass
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  cases he : event i.val
  · simp [he]
  · simp only [he, Bool.true_eq, ↓reduceIte, mul_one]
    exact fibre_probability p D S hn hp i

/-- Exactly b binary digits are mapped through their positional index and the cumulative sampler. -/
def bitSampler (p : ℕ → ℚ) (S b : ℕ) (hn : cumulative p S = 1)
    (bits : Fin b → Fin 2) : Fin S :=
  sampler p (2 ^ b) S hn (finFunctionFinEquiv bits)

theorem bitSampler_event_law (p : ℕ → ℚ) (S b : ℕ) (hn : cumulative p S = 1)
    (hp : ∀ j, 0 ≤ p j) (event : ℕ → Bool) :
    average (fun bits : Fin b → Fin 2 => event (bitSampler p S b hn bits).val) =
      eventMass (mass p (2 ^ b)) S event := by
  change average (fun bits : Fin b → Fin 2 =>
    (fun i : Fin S => event i.val) (listSampler b (sampler p (2 ^ b) S hn) bits)) = _
  rw [listSampler_exact b (sampler p (2 ^ b) S hn) (fun i : Fin S => event i.val)]
  exact sampler_event_law p (2 ^ b) S hn hp event

/-- Every event of the actual bounded-bit sampler is close to its original rational law. -/
theorem bitSampler_event_error (p : ℕ → ℚ) (S b : ℕ) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ j, 0 ≤ p j) (heps : 0 < eps)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ)) (event : ℕ → Bool) :
    |average (fun bits : Fin b → Fin 2 => event (bitSampler p S b hn bits).val) -
      eventMass p S event| ≤ eps / 8 := by
  rw [bitSampler_event_law p S b hn hp event]
  exact event_error_of_precision p S b eps hp heps hgrid event

end PvNP.RealizableHardness.InverseCDFSampler