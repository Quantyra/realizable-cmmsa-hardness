import Complexitylib.Classes.Promise.Defs
import Complexitylib.Classes.EventProb
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.P.Cobham.Internal

/-! Source draft: machine-facing seeded composition bridge. UNCOMPILED.
The probability contracts below are definitions, not a reduction construction.
The proved-source bridge constructs the executor's FP evidence from component
machines; full flat-uniform-seed composition is still a separate obligation. -/
namespace PvNP.RealizableHardness.RandomizedReduction
open Complexity

abbrev Bits := List Bool

/-- Coins have length determined only by input length. The length ruler is an
actual FP output, so its length cannot encode an arbitrary uncomputable rule. -/
structure SeededMap where
  run : Bits → Bits
  run_fp : run ∈ FP
  ruler : Bits → Bits
  ruler_fp : ruler ∈ FP
  coinCount : ℕ → ℕ
  ruler_length : ∀ x, (ruler x).length = coinCount x.length

def SeededMap.apply (R : SeededMap) (x seed : Bits) : Bits :=
  R.run (pair x seed)

/-- Every length, including zero and exceptional small inputs, is bounded. -/
theorem SeededMap.coinCount_poly (R : SeededMap) :
    ∃ p : Polynomial ℕ, ∀ n, R.coinCount n ≤ p.eval n := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP R.ruler_fp
  refine ⟨p, fun n => ?_⟩
  have h := hp (List.replicate n false)
  simpa only [R.ruler_length, List.length_replicate] using h

noncomputable def successProbability (R : SeededMap) (x : Bits)
    (target : Set Bits) : ℚ := by
  classical
  exact eventProb (Finset.univ.filter fun w : Fin (R.coinCount x.length) → Bool =>
    R.apply x (List.ofFn w) ∈ target)

/-- Distinct YES and NO guarantees; neither side silently becomes total.
This is only a semantic contract and supplies no instance of hardness. -/
def Preserves (R : SeededMap) (source target : PromiseProblem)
    (yesError noError : ℚ) : Prop :=
  (∀ x ∈ source.yesInstances,
    1 - yesError ≤ successProbability R x target.yesInstances) ∧
  (∀ x ∈ source.noInstances,
    1 - noError ≤ successProbability R x target.noInstances)

/-- The raw encoding is pair (pair input firstCoins) secondCoins.
Both pair projections are total on malformed encodings. -/
def firstOutput (f : Bits → Bits) (z : Bits) : Bits := f (pairFst z)

def secondCoins (f ruler : Bits → Bits) (z : Bits) : Bits :=
  (pairSnd z).take (ruler (firstOutput f z)).length

def execute (f g ruler : Bits → Bits) (z : Bits) : Bits :=
  g (pair (firstOutput f z) (secondCoins f ruler z))

@[simp] theorem execute_pair (f g ruler : Bits → Bits) (x r s : Bits) :
    execute f g ruler (pair (pair x r) s) =
      g (pair (f (pair x r)) (s.take (ruler (f (pair x r))).length)) := by
  simp [execute, firstOutput, secondCoins]

theorem firstOutput_fp {f : Bits → Bits} (hf : f ∈ FP) : firstOutput f ∈ FP :=
  mem_FP_comp pairFst_mem_FP hf

/-- Truncation is implemented by the library's actual take-length machine.
The ruler is evaluated on the actual random first output. -/
theorem secondCoins_fp {f ruler : Bits → Bits} (hf : f ∈ FP)
    (hr : ruler ∈ FP) : secondCoins f ruler ∈ FP := by
  exact Cobham.takeLenFn_mem_FP (mem_FP_comp (firstOutput_fp hf) hr) pairSnd_mem_FP

theorem execute_fp {f g ruler : Bits → Bits} (hf : f ∈ FP)
    (hg : g ∈ FP) (hr : ruler ∈ FP) : execute f g ruler ∈ FP := by
  exact mem_FP_comp (mem_FP_pair (firstOutput_fp hf) (secondCoins_fp hf hr)) hg

/-- An actual halting TM with an all-input natural-polynomial clock follows
from component machines, without assuming the composite belongs to FP. -/
theorem execute_machine {f g ruler : Bits → Bits} (hf : f ∈ FP)
    (hg : g ∈ FP) (hr : ruler ∈ FP) :
    ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.ComputesInTime (execute f g ruler) p.eval :=
  mem_FP_iff_computesInTime_polynomial.mp (execute_fp hf hg hr)

/-- Malformed inputs are still processed totally, using the codec's specified
partial-prefix first projection and empty second projection on parse failure. -/
theorem execute_malformed (f g ruler : Bits → Bits) (z : Bits)
    (hz : unpair? z = none) :
    execute f g ruler z = g (pair (f (pairFst z)) []) := by
  simp [execute, firstOutput, secondCoins, pairSnd, hz]

noncomputable def pairEnvelope (a : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 2 + a

/-- A fixed polynomial amount of second-stage padding suffices for every
first seed whose length is bounded by a. The bound is derived from the
component machines' output lengths, even on failed/out-of-promise outputs. -/
theorem second_coin_padding {f ruler : Bits → Bits} (hf : f ∈ FP)
    (hr : ruler ∈ FP) (a : Polynomial ℕ) :
    ∃ p q : Polynomial ℕ, ∀ x r : Bits, r.length ≤ a.eval x.length →
      (ruler (f (pair x r))).length ≤
        (q.comp (p.comp (pairEnvelope a))).eval x.length := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hf
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hr
  refine ⟨p, q, fun x r hlen => ?_⟩
  have hpair : (pair x r).length ≤ (pairEnvelope a).eval x.length := by
    simp only [pair_length, pairEnvelope, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  have hout := (hp (pair x r)).trans (polynomial_eval_mono_nat p hpair)
  have h := (hq (f (pair x r))).trans (polynomial_eval_mono_nat q hout)
  simpa only [Polynomial.eval_comp] using h

/-- With enough supplied bits the used prefix has exactly the required count. -/
theorem secondCoins_length (f ruler : Bits → Bits) (z : Bits)
    (h : (ruler (firstOutput f z)).length ≤ (pairSnd z).length) :
    (secondCoins f ruler z).length = (ruler (firstOutput f z)).length := by
  simp only [secondCoins, List.length_take, Nat.min_eq_left h]

end PvNP.RealizableHardness.RandomizedReduction
