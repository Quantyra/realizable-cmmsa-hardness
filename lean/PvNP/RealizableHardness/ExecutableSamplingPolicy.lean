import PvNP.RealizableHardness.ExecutablePipelineInput
import PvNP.RealizableHardness.ComputableSampleCount
import PvNP.RealizableHardness.SamplingGuarantee
import PvNP.RealizableHardness.SeedEncoding

/-! Source draft. Concrete manuscript sampling policy and encoded-length coin bound.
No parser/arithmetic FP or source-support construction theorem is asserted. -/
namespace PvNP.RealizableHardness.ExecutableSamplingPolicy
open CMMSACodec ExecutablePipelineInput
set_option autoImplicit false

def inverseCeil (eps : Rat) : Nat := ⌈1 / eps⌉₊

def selected (eps : Rat) (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters) : Input :=
  ⟨ws, t, q, SamplingGuarantee.precision t.rows.length eps,
    ComputableSampleCount.count ws.length (inverseCeil eps)⟩

theorem inverse_le (eps : Rat) : 1 / eps ≤ (inverseCeil eps : Rat) := Nat.le_ceil _

theorem inverse_pos (eps : Rat) (he : 0 < eps) : 0 < inverseCeil eps := by
  have h : (0 : Rat) < inverseCeil eps :=
    lt_of_lt_of_le (by positivity : (0 : Rat) < 1 / eps) (inverse_le eps)
  exact_mod_cast h

theorem self_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < (2 : Nat) ^ n := by positivity
    omega

theorem precision_upper (S : Nat) (eps : Rat) :
    SamplingGuarantee.precision S eps ≤ 8 * S * inverseCeil eps := by
  apply Nat.clog_le_of_le_pow
  apply le_trans (show ⌈8 * (S : Rat) / eps⌉₊ ≤ 8*S*inverseCeil eps from ?_)
    (self_le_two_pow _)
  apply Nat.ceil_le.mpr
  have h := mul_le_mul_of_nonneg_left (inverse_le eps)
    (by positivity : (0 : Rat) ≤ 8 * S)
  push_cast
  calc
    8 * (S : Rat) / eps = (8 * S) * (1 / eps) := by ring
    _ ≤ _ := h

theorem selected_trials_pos (eps : Rat) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (q : ExecutableRounding.InputParameters) :
    0 < (selected eps ws t q).trials := ComputableSampleCount.count_pos _ _

theorem selected_grid (eps : Rat) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (q : ExecutableRounding.InputParameters) :
    8 * (t.rows.length : Rat) / eps ≤
      ((2 ^ (selected eps ws t q).precision : Nat) : Rat) :=
  SamplingGuarantee.precision_bound _ _

theorem selected_threshold (eps : Rat) (he : 0 < eps) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (q : ExecutableRounding.InputParameters) :
    SamplingThreshold.learningThreshold ws.length (eps : Real) ≤
      ((selected eps ws t q).trials : Real) := by
  apply ComputableSampleCount.learningThreshold_le_count
  · exact_mod_cast he
  · exact_mod_cast inverse_le eps

theorem list_count_le_encode (ts : List Tree) : ts.length ≤ (Tree.encode (listTree ts)).length := by
  induction ts with
  | nil => simp [listTree, Tree.encode]
  | cons t ts ih =>
    simp only [listTree, Tree.encode, List.length_cons, List.length_append] at *
    omega

/-- The actual weight list consumes at least one encoded bit per variable. -/
theorem variables_le_input_length (x : Input) : x.weights.length ≤ (encodeInput x).length := by
  have h := list_count_le_encode (x.weights.map signedTree)
  simp only [List.length_map] at h
  simp only [encodeInput, inputTree, Tree.encode, List.length_cons, List.length_append]
  omega

/-- Stored source occurrences, including zero-probability rows, consume input bits. -/
theorem rows_le_input_length (x : Input) : x.source.rows.length ≤ (encodeInput x).length := by
  have h := list_count_le_encode (x.source.rows.map rowTree)
  simp only [List.length_map] at h
  simp only [encodeInput, inputTree, Tree.encode, List.length_cons, List.length_append]
  omega

/-- A quadratic length-only ruler for each fixed positive rational epsilon. -/
def coinRuler (eps : Rat) (n : Nat) : Nat :=
  (64 * (n+11) * inverseCeil eps ^ 2) * (8*n*inverseCeil eps)

theorem coinRuler_quadratic (eps : Rat) (n : Nat) :
    coinRuler eps n = 512 * inverseCeil eps ^ 3 * (n^2 + 11*n) := by
  unfold coinRuler
  ring

theorem selected_coins_le (eps : Rat) (he : 0 < eps) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (q : ExecutableRounding.InputParameters) :
    (selected eps ws t q).trials * (selected eps ws t q).precision ≤
      coinRuler eps (encodeInput (selected eps ws t q)).length := by
  let x := selected eps ws t q
  have hN := variables_le_input_length x
  have hS := rows_le_input_length x
  have hM := (ComputableSampleCount.count_upper ws.length (inverseCeil eps)
    (inverse_pos eps he)).le
  have hb := precision_upper t.rows.length eps
  have hMu : x.trials ≤ 64*((encodeInput x).length+11)*inverseCeil eps^2 := by
    exact hM.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hN 11)))
  have hbu : x.precision ≤ 8*(encodeInput x).length*inverseCeil eps := by
    exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hS))
  exact Nat.mul_le_mul hMu hbu

theorem selected_good_probability (eps : Rat) (he : 0 < eps) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (q : ExecutableRounding.InputParameters)
    (F : (Fin ws.length → Bool) → Nat → Bool) :
    (5 / 6 : Real) ≤ JointSamplingLaw.seedProbability
      (selected eps ws t q).trials (selected eps ws t q).precision
      (fun seeds => SamplingGuarantee.Good (FiniteSourceSampler.probability t)
        t.rows.length ws.length (selected eps ws t q).trials F eps
        (FiniteSourceSampler.selectArray t (selected eps ws t q).precision
          (selected eps ws t q).trials seeds)) := by
  exact SamplingGuarantee.good_probability_of_learningThreshold
    (FiniteSourceSampler.probability t) t.rows.length (selected eps ws t q).precision
    ws.length (selected eps ws t q).trials F eps
    (FiniteSourceSampler.cumulative_endpoint t) (FiniteSourceSampler.probability_nonneg t)
    he (selected_grid eps ws t q) (selected_threshold eps he ws t q)

theorem selected_run_valid {L : Nat} (eps : Rat) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (seeds : JointSamplingLaw.SeedArray
      (selected eps ws t (ExecutableRounding.inputOf p)).trials
      (selected eps ws t (ExecutableRounding.inputOf p)).precision)
    (hF : ∀ j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 ≤ L) :
    run L (Complexity.pair (encodeInput (selected eps ws t (ExecutableRounding.inputOf p)))
      (coinBits seeds)) = ExecutablePipeline.bits ws t
        (SamplingGuarantee.precision t.rows.length eps)
        (ComputableSampleCount.count ws.length (inverseCeil eps))
        (ExecutableRounding.inputOf p) seeds :=
  run_valid ws t _ _ p seeds (ComputableSampleCount.count_pos _ _) hF

/-- The parser's Boolean convention is exactly the accepted row-major seed equivalence. -/
theorem digitBool_eq_finTwoEquiv (d : Fin 2) : digitBool d = finTwoEquiv d := by
  fin_cases d <;> rfl

theorem coinBits_eq_flatten {M b : Nat} (seeds : JointSamplingLaw.SeedArray M b) :
    coinBits seeds = List.ofFn (SeedEncoding.flatten M b seeds) := by
  unfold coinBits SeedEncoding.flatten
  simp only [digitBool_eq_finTwoEquiv]

theorem padded_seed_probability (M b k : Nat) (event : JointSamplingLaw.SeedArray M b → Prop) :
    SeedEncoding.uniformProbability (fun bits : SeedEncoding.FlatSeed (M*b+k) =>
      event (SeedEncoding.unflatten M b (SeedEncoding.takePrefix (M*b) k bits))) =
      JointSamplingLaw.seedProbability M b event := by
  rw [SeedEncoding.prefix_probability (M*b) k
    (fun bits => event (SeedEncoding.unflatten M b bits))]
  exact SeedEncoding.flat_probability M b event

/-- Validate policy fields and the full length-only tape before executing the pipeline.
The parser and arithmetic used for these guards still require runtime proofs. -/
def paddedRunOption (L : Nat) (eps : Rat) (instanceBits coins : Bits) : Option Bits := do
  let x ← decodeInput instanceBits
  if x.precision = SamplingGuarantee.precision x.source.rows.length eps ∧
      x.trials = ComputableSampleCount.count x.weights.length (inverseCeil eps) ∧
      coins.length = coinRuler eps instanceBits.length ∧
      x.trials*x.precision ≤ coins.length then
    runOption L instanceBits (coins.take (x.trials*x.precision))
  else none

def paddedRun (L : Nat) (eps : Rat) (instanceBits coins : Bits) : Bits :=
  (paddedRunOption L eps instanceBits coins).getD []

theorem paddedRunOption_selected (L : Nat) (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (q : ExecutableRounding.InputParameters)
    (seeds : JointSamplingLaw.SeedArray (selected eps ws t q).trials
      (selected eps ws t q).precision) (tail : Bits)
    (htail : tail.length = coinRuler eps (encodeInput (selected eps ws t q)).length -
      (selected eps ws t q).trials*(selected eps ws t q).precision) :
    paddedRunOption L eps (encodeInput (selected eps ws t q)) (coinBits seeds ++ tail) =
      ExecutablePipeline.checkedBits L ws t (selected eps ws t q).precision
        (selected eps ws t q).trials q seeds := by
  have hc := selected_coins_le eps he ws t q
  have hlen : (coinBits seeds ++ tail).length =
      coinRuler eps (encodeInput (selected eps ws t q)).length := by
    rw [List.length_append, coinBits_length, htail]
    omega
  have htake : (coinBits seeds ++ tail).take
      ((selected eps ws t q).trials*(selected eps ws t q).precision) = coinBits seeds := by
    rw [← coinBits_length seeds]
    exact List.take_left
  simp only [paddedRunOption, decode_encodeInput]
  change (if
    (selected eps ws t q).precision = SamplingGuarantee.precision t.rows.length eps ∧
    (selected eps ws t q).trials = ComputableSampleCount.count ws.length (inverseCeil eps) ∧
    (coinBits seeds ++ tail).length = coinRuler eps (encodeInput (selected eps ws t q)).length ∧
    (selected eps ws t q).trials*(selected eps ws t q).precision ≤ (coinBits seeds ++ tail).length
    then runOption L (encodeInput (selected eps ws t q))
      ((coinBits seeds ++ tail).take ((selected eps ws t q).trials*(selected eps ws t q).precision))
    else none) = _
  rw [if_pos (by exact ⟨rfl, rfl, hlen, by rw [hlen]; exact hc⟩), htake]
  exact runOption_roundtrip L (selected eps ws t q) seeds

theorem ofFn_prefix_split (n k : Nat) (bits : SeedEncoding.FlatSeed (n+k)) :
    List.ofFn bits = List.ofFn (SeedEncoding.takePrefix n k bits) ++
      List.ofFn (fun j => bits (Fin.natAdd n j)) := by
  rw [List.ofFn_add]
  rfl

theorem coinBits_unflatten (M b : Nat) (bits : SeedEncoding.FlatSeed (M*b)) :
    coinBits (SeedEncoding.unflatten M b bits) = List.ofFn bits := by
  rw [coinBits_eq_flatten, SeedEncoding.flatten_unflatten]

/-- Exact Q-bit executor theorem, with Q written as c+(Q-c) using the proved cap. -/
theorem paddedRun_selected_valid {L : Nat} (eps : Rat) (he : 0 < eps) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (hF : ∀ j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 ≤ L)
    (bits : SeedEncoding.FlatSeed
      ((selected eps ws t (ExecutableRounding.inputOf p)).trials *
        (selected eps ws t (ExecutableRounding.inputOf p)).precision +
      (coinRuler eps (encodeInput (selected eps ws t (ExecutableRounding.inputOf p))).length -
        (selected eps ws t (ExecutableRounding.inputOf p)).trials *
          (selected eps ws t (ExecutableRounding.inputOf p)).precision))) :
    let x := selected eps ws t (ExecutableRounding.inputOf p)
    let k := coinRuler eps (encodeInput x).length - x.trials*x.precision
    let seeds := SeedEncoding.unflatten x.trials x.precision
      (SeedEncoding.takePrefix (x.trials*x.precision) k bits)
    paddedRun L eps (encodeInput x) (List.ofFn bits) =
      ExecutablePipeline.bits ws t x.precision x.trials (ExecutableRounding.inputOf p) seeds := by
  dsimp only
  rw [ofFn_prefix_split, ← coinBits_unflatten]
  unfold paddedRun
  rw [paddedRunOption_selected L eps he ws t (ExecutableRounding.inputOf p) _ _ (by simp)]
  rw [ExecutablePipeline.checkedBits_valid ws t _ _ p _
    (selected_trials_pos eps ws t (ExecutableRounding.inputOf p)) hF]
  rfl

theorem padded_length_eq_ruler (eps : Rat) (he : 0 < eps) (ws : List Rat)
    (t : FiniteSourceSampler.Table ws.length) (q : ExecutableRounding.InputParameters) :
    let x := selected eps ws t q
    x.trials*x.precision + (coinRuler eps (encodeInput x).length - x.trials*x.precision) =
      coinRuler eps (encodeInput x).length := by
  dsimp only
  have h := selected_coins_le eps he ws t q
  omega

/-- The actual padded executor agrees on every tape; its recovered source draws
simultaneously satisfy the concentration event with probability at least 5/6. -/
theorem padded_executor_good_probability {L : Nat} (eps : Rat) (he : 0 < eps)
    (ws : List Rat) (t : FiniteSourceSampler.Table ws.length)
    (p : FiniteRepairRoundingPipeline.Parameters ws.get)
    (hF : ∀ j : Fin t.rows.length, Formula.leaves (t.rows.get j).2+1 ≤ L)
    (F : (Fin ws.length → Bool) → Nat → Bool) :
    let x := selected eps ws t (ExecutableRounding.inputOf p)
    let k := coinRuler eps (encodeInput x).length - x.trials*x.precision
    (5 / 6 : Real) ≤ SeedEncoding.uniformProbability
      (fun bits : SeedEncoding.FlatSeed (x.trials*x.precision+k) =>
        let seeds := SeedEncoding.unflatten x.trials x.precision
          (SeedEncoding.takePrefix (x.trials*x.precision) k bits)
        paddedRun L eps (encodeInput x) (List.ofFn bits) =
          ExecutablePipeline.bits ws t x.precision x.trials (ExecutableRounding.inputOf p) seeds ∧
        SamplingGuarantee.Good (FiniteSourceSampler.probability t) t.rows.length
          ws.length x.trials F eps (FiniteSourceSampler.selectArray t x.precision x.trials seeds)) := by
  dsimp only
  simp only [paddedRun_selected_valid eps he ws t p hF, true_and]
  rw [padded_seed_probability
    (selected eps ws t (ExecutableRounding.inputOf p)).trials
    (selected eps ws t (ExecutableRounding.inputOf p)).precision _
    (fun seeds => SamplingGuarantee.Good (FiniteSourceSampler.probability t) t.rows.length
      ws.length (selected eps ws t (ExecutableRounding.inputOf p)).trials F eps
      (FiniteSourceSampler.selectArray t (selected eps ws t (ExecutableRounding.inputOf p)).precision
        (selected eps ws t (ExecutableRounding.inputOf p)).trials seeds))]
  exact selected_good_probability eps he ws t (ExecutableRounding.inputOf p) F

end PvNP.RealizableHardness.ExecutableSamplingPolicy
