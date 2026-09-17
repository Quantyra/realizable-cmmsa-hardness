import PvNP.RealizableHardness.InverseCDFSampler
import PvNP.RealizableHardness.FiniteConcentration

namespace PvNP.RealizableHardness.JointSamplingLaw
open scoped BigOperators
open FiniteSampling InverseCDFSampler

/-- Actual independent blocks of b binary digits, one block for each trial. -/
abbrev SeedArray (M b : Nat) := Fin M -> (Fin b -> Fin 2)

def sampleArray (p : Nat -> Rat) (S b M : Nat) (hn : cumulative p S = 1)
    (seeds : SeedArray M b) : Fin M -> Fin S :=
  fun i => bitSampler p S b hn (seeds i)

/-- A fibre of the coordinatewise map is the product of its coordinate fibres. -/
def arrayFibreEquiv {A B : Type*} (f : A -> B) (M : Nat) (x : Fin M -> B) :
    {seeds : Fin M -> A // (fun i => f (seeds i)) = x} ≃
      (forall i : Fin M, {a : A // f a = x i}) where
  toFun seeds i := ⟨seeds.val i, congrFun seeds.property i⟩
  invFun seeds := ⟨fun i => (seeds i).val, funext (fun i => (seeds i).property)⟩
  left_inv seeds := by rfl
  right_inv seeds := by rfl

theorem array_fibre_card {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A -> B) (M : Nat) (x : Fin M -> B) :
    Fintype.card {seeds : Fin M -> A // (fun i => f (seeds i)) = x} =
      ∏ i, Fintype.card {a : A // f a = x i} := by
  rw [Fintype.card_congr (arrayFibreEquiv f M x), Fintype.card_pi]

def bitFibreEquiv (p : Nat -> Rat) (S b : Nat) (hn : cumulative p S = 1) (i : Fin S) :
    {bits : Fin b -> Fin 2 // bitSampler p S b hn bits = i} ≃
      {r : Fin (2 ^ b) // sampler p (2 ^ b) S hn r = i} where
  toFun bits := ⟨finFunctionFinEquiv bits.val, bits.property⟩
  invFun r := ⟨finFunctionFinEquiv.symm r.val, by simpa [bitSampler] using r.property⟩
  left_inv bits := by apply Subtype.ext; simp
  right_inv r := by apply Subtype.ext; simp

theorem bit_fibre_probability (p : Nat -> Rat) (S b : Nat) (hn : cumulative p S = 1)
    (hp : forall j, 0 <= p j) (i : Fin S) :
    (Fintype.card {bits : Fin b -> Fin 2 // bitSampler p S b hn bits = i} : Rat) /
      Fintype.card (Fin b -> Fin 2) = mass p (2 ^ b) i.val := by
  rw [Fintype.card_congr (bitFibreEquiv p S b hn i)]
  simpa using fibre_probability p (2 ^ b) S hn hp i

theorem array_fibre_probability (p : Nat -> Rat) (S b M : Nat) (hn : cumulative p S = 1)
    (hp : forall j, 0 <= p j) (x : Fin M -> Fin S) :
    (Fintype.card {seeds : SeedArray M b // sampleArray p S b M hn seeds = x} : Rat) /
      Fintype.card (SeedArray M b) = trialMass (fun i : Fin S => mass p (2 ^ b) i.val) M x := by
  change (Fintype.card {seeds : Fin M -> (Fin b -> Fin 2) //
    (fun i => bitSampler p S b hn (seeds i)) = x} : Rat) / _ = _
  rw [array_fibre_card]
  simp only [Nat.cast_prod, trialMass, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  have hd : (∏ _i : Fin M, ((2 : Rat) ^ b)) = (2 ^ b) ^ M := by simp
  rw [← hd, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa using bit_fibre_probability p S b hn hp (x i)

/-- Uniform block seeds push forward exactly for arbitrary events, including nonrectangular ones. -/
theorem sampleArray_event_law (p : Nat -> Rat) (S b M : Nat) (hn : cumulative p S = 1)
    (hp : forall j, 0 <= p j) (event : (Fin M -> Fin S) -> Bool) :
    average (fun seeds : SeedArray M b => event (sampleArray p S b M hn seeds)) =
      ∑ x, if event x then trialMass (fun i : Fin S => mass p (2 ^ b) i.val) M x else 0 := by
  unfold average
  rw [← Fintype.sum_fiberwise' (sampleArray p S b M hn)
    (fun x => if event x then (1 : Rat) else 0)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x
  · simp [he]
  · simp only [he, Bool.true_eq, ↓reduceIte, mul_one]
    exact array_fibre_probability p S b M hn hp x

/-- Real-valued seed probability, permitting arbitrary mathematical events. -/
noncomputable def seedProbability (M b : Nat) (event : SeedArray M b -> Prop) : Real := by
  classical
  exact (∑ seeds, if event seeds then (1 : Real) else 0) / Fintype.card (SeedArray M b)

theorem sampleArray_probability (p : Nat -> Rat) (S b M : Nat) (hn : cumulative p S = 1)
    (hp : forall j, 0 <= p j) (event : (Fin M -> Fin S) -> Prop) :
    seedProbability M b (fun seeds => event (sampleArray p S b M hn seeds)) =
      FiniteConcentration.probability (fun i : Fin S => mass p (2 ^ b) i.val) M event := by
  classical
  have h := sampleArray_event_law p S b M hn hp (fun x => decide (event x))
  unfold average at h
  unfold seedProbability FiniteConcentration.probability
  have hr := congrArg (fun z : Rat => (z : Real)) h
  push_cast at hr
  simp only [apply_ite, Rat.cast_one, Rat.cast_zero] at hr
  simpa using hr

end PvNP.RealizableHardness.JointSamplingLaw
