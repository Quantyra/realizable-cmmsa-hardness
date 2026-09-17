import PvNP.RealizableHardness.JointSamplingLaw
import Mathlib.Logic.Equiv.Fin.Basic

namespace PvNP.RealizableHardness.SeedEncoding
open scoped BigOperators
open JointSamplingLaw

/-- Flat machine-facing Boolean coins. No positivity assumption is needed. -/
abbrev FlatSeed (n : Nat) := Fin n -> Bool

/-- Row-major flattening: address j + b*i holds block i, digit j. -/
def flatten (M b : Nat) (seeds : SeedArray M b) : FlatSeed (M * b) :=
  fun k => finTwoEquiv (seeds (finProdFinEquiv.symm k).1
    (finProdFinEquiv.symm k).2)

def unflatten (M b : Nat) (bits : FlatSeed (M * b)) : SeedArray M b :=
  fun i j => finTwoEquiv.symm (bits (finProdFinEquiv (i, j)))

@[simp] theorem unflatten_flatten (M b : Nat) (seeds : SeedArray M b) :
    unflatten M b (flatten M b seeds) = seeds := by
  funext i j
  simp [unflatten, flatten]

@[simp] theorem flatten_unflatten (M b : Nat) (bits : FlatSeed (M * b)) :
    flatten M b (unflatten M b bits) = bits := by
  funext k
  change finTwoEquiv (finTwoEquiv.symm
    (bits (finProdFinEquiv (finProdFinEquiv.symm k)))) = bits k
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def seedEquiv (M b : Nat) : Equiv (SeedArray M b) (FlatSeed (M * b)) where
  toFun := flatten M b
  invFun := unflatten M b
  left_inv := unflatten_flatten M b
  right_inv := flatten_unflatten M b

def sampleFlat (p : Nat -> Rat) (S b M : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (bits : FlatSeed (M * b)) :=
  sampleArray p S b M hn (unflatten M b bits)

/-- Split a longer seed into the used takePrefix and the ignored suffix. -/
def splitBits (n k : Nat) (bits : FlatSeed (n + k)) : FlatSeed n × FlatSeed k :=
  (fun i => bits (Fin.castAdd k i), fun j => bits (Fin.natAdd n j))

def joinBits (n k : Nat) (bits : FlatSeed n × FlatSeed k) : FlatSeed (n + k) :=
  fun i => Sum.elim bits.1 bits.2 (finSumFinEquiv.symm i)

@[simp] theorem split_join (n k : Nat) (bits : FlatSeed n × FlatSeed k) :
    splitBits n k (joinBits n k bits) = bits := by
  apply Prod.ext <;> funext i <;> simp [splitBits, joinBits]

@[simp] theorem join_split (n k : Nat) (bits : FlatSeed (n + k)) :
    joinBits n k (splitBits n k bits) = bits := by
  funext i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  cases s <;> simp [joinBits, splitBits]

def splitEquiv (n k : Nat) : Equiv (FlatSeed (n + k)) (FlatSeed n × FlatSeed k) where
  toFun := splitBits n k
  invFun := joinBits n k
  left_inv := join_split n k
  right_inv := split_join n k

def takePrefix (n k : Nat) (bits : FlatSeed (n + k)) : FlatSeed n :=
  (splitBits n k bits).1

/-- Explicit constant-size fibres; the inverse appends the supplied suffix. -/
def prefixFibreEquiv (n k : Nat) (x : FlatSeed n) :
    Equiv {bits : FlatSeed (n + k) // takePrefix n k bits = x} (FlatSeed k) where
  toFun bits := (splitBits n k bits.val).2
  invFun tail := (show {bits : FlatSeed (n + k) // takePrefix n k bits = x} from
    ⟨joinBits n k (x, tail), by simp [takePrefix]⟩)
  left_inv bits := by
    apply Subtype.ext
    have h : (x, (splitBits n k bits.val).2) = splitBits n k bits.val := by
      apply Prod.ext
      · exact bits.property.symm
      · rfl
    change joinBits n k (x, (splitBits n k bits.val).2) = bits.val
    rw [h, join_split]
  right_inv tail := by simp

attribute [local instance] Classical.propDecidable

/-- Cardinality definition, usable for arbitrary mathematical events. -/
noncomputable def uniformProbability {A : Type*} [Fintype A] (event : A -> Prop) : Real :=
  (Fintype.card {a : A // event a} : Real) / Fintype.card A

def eventEquiv {A B : Type*} (e : Equiv A B) (event : B -> Prop) :
    Equiv {a : A // event (e a)} {b : B // event b} where
  toFun a := ⟨e a.val, a.property⟩
  invFun b := ⟨e.symm b.val, by simpa using b.property⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

theorem event_card_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : Equiv A B) (event : B -> Prop) :
    Fintype.card {a : A // event (e a)} = Fintype.card {b : B // event b} :=
  Fintype.card_congr (eventEquiv e event)

theorem uniformProbability_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : Equiv A B) (event : B -> Prop) :
    uniformProbability (fun a => event (e a)) = uniformProbability event := by
  unfold uniformProbability
  rw [event_card_equiv e event, Fintype.card_congr e]

theorem uniformProbability_eq_sum {A : Type*} [Fintype A] (event : A -> Prop) :
    uniformProbability event =
      (∑ a, if event a then (1 : Real) else 0) / Fintype.card A := by
  simp [uniformProbability, Fintype.card_subtype, Finset.sum_boole]

theorem seedProbability_eq_uniform (M b : Nat) (event : SeedArray M b -> Prop) :
    seedProbability M b event = uniformProbability event := by
  rw [uniformProbability_eq_sum]
  rfl

theorem flat_event_card (M b : Nat) (event : SeedArray M b -> Prop) :
    Fintype.card {bits : FlatSeed (M * b) // event (unflatten M b bits)} =
      Fintype.card {seeds : SeedArray M b // event seeds} :=
  event_card_equiv (seedEquiv M b).symm event

theorem flat_probability (M b : Nat) (event : SeedArray M b -> Prop) :
    uniformProbability (fun bits : FlatSeed (M * b) => event (unflatten M b bits)) =
      seedProbability M b event := by
  rw [seedProbability_eq_uniform]
  exact uniformProbability_equiv (seedEquiv M b).symm event

theorem sampleFlat_probability (p : Nat -> Rat) (S b M : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (hp : forall j, 0 <= p j)
    (event : (Fin M -> Fin S) -> Prop) :
    uniformProbability (fun bits => event (sampleFlat p S b M hn bits)) =
      FiniteConcentration.probability
        (fun i : Fin S => FiniteSampling.mass p (2 ^ b) i.val) M event := by
  change uniformProbability (fun bits =>
    event (sampleArray p S b M hn (unflatten M b bits))) = _
  rw [flat_probability M b (fun seeds => event (sampleArray p S b M hn seeds))]
  exact sampleArray_probability p S b M hn hp event

theorem prefix_fibre_card (n k : Nat) (x : FlatSeed n) :
    Fintype.card {bits : FlatSeed (n + k) // takePrefix n k bits = x} = 2 ^ k := by
  rw [Fintype.card_congr (prefixFibreEquiv n k x)]
  simp [FlatSeed]

/-- Every event fibre is its takePrefix event times all suffixes, without independence assumptions. -/
def prefixEventEquiv (n k : Nat) (event : FlatSeed n -> Prop) :
    Equiv {bits : FlatSeed (n + k) // event (takePrefix n k bits)}
      ({x : FlatSeed n // event x} × FlatSeed k) where
  toFun bits := (⟨takePrefix n k bits.val, bits.property⟩, (splitBits n k bits.val).2)
  invFun pair := ⟨joinBits n k (pair.1.val, pair.2), by
    simpa [takePrefix] using pair.1.property⟩
  left_inv bits := by apply Subtype.ext; exact join_split n k bits.val
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      simp [takePrefix]
    · simp

theorem prefix_event_card (n k : Nat) (event : FlatSeed n -> Prop) :
    Fintype.card {bits : FlatSeed (n + k) // event (takePrefix n k bits)} =
      Fintype.card {bits : FlatSeed n // event bits} * 2 ^ k := by
  rw [Fintype.card_congr (prefixEventEquiv n k event), Fintype.card_prod]
  simp [FlatSeed]

theorem prefix_probability (n k : Nat) (event : FlatSeed n -> Prop) :
    uniformProbability (fun bits : FlatSeed (n + k) => event (takePrefix n k bits)) =
      uniformProbability event := by
  unfold uniformProbability
  rw [prefix_event_card]
  simp only [FlatSeed, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  have hk : (2 : Real) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_div_mul_right _ _ hk

theorem padded_sampleFlat_probability (p : Nat -> Rat) (S b M k : Nat)
    (hn : FiniteSampling.cumulative p S = 1) (hp : forall j, 0 <= p j)
    (event : (Fin M -> Fin S) -> Prop) :
    uniformProbability (fun bits : FlatSeed (M * b + k) =>
      event (sampleFlat p S b M hn (takePrefix (M * b) k bits))) =
      FiniteConcentration.probability
        (fun i : Fin S => FiniteSampling.mass p (2 ^ b) i.val) M event := by
  rw [prefix_probability (M * b) k (fun bits => event (sampleFlat p S b M hn bits))]
  exact sampleFlat_probability p S b M hn hp event

end PvNP.RealizableHardness.SeedEncoding
