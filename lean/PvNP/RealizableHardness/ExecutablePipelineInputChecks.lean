import PvNP.RealizableHardness.ExecutablePipelineInput
/-! Uncompiled parser checks. No observed evaluation or kernel acceptance claimed. -/
open PvNP.RealizableHardness ExecutablePipelineInput

#print axioms read_ratTree_abs
#print axioms read_signedTree
#print axioms read_rowTree
#print axioms read_parameterTree
#print axioms read_inputTree
#print axioms decode_encodeInput
#print axioms decodeInput_bad_fields
#print axioms decodeInput_trailing
#print axioms decodeInput_empty
#print axioms digit_roundtrip
#print axioms coinBits_length
#print axioms seedsOf_coinBits
#print axioms runOption_roundtrip
#print axioms runOption_wrong_coins
#print axioms runOption_bad_input
#print axioms run_pair
#print axioms run_valid
#print axioms readInput_empty_rows
#print axioms readSigned_zero_denominator
#print axioms readRow_bad_variable
#print axioms coinBits_zero_trials
#print axioms coinBits_zero_precision

example : decodeInput [] = none := decodeInput_empty
example : readSigned (signedTree (-3/7)) = some (-3/7) := read_signedTree _
example : readSigned (signedTree (0 : Rat)) = some 0 := read_signedTree _
example (n : Nat) : readSigned (.node .leaf (.node (CMMSAEncoding.natTree n)
    (CMMSAEncoding.natTree 0))) = none := readSigned_zero_denominator false n
example (q : Rat) : readRow 1 (.node (signedTree q)
    (.node .leaf (CMMSAEncoding.natTree 1))) = none := readRow_bad_variable 1 1 q le_rfl
example (x : Input) : decodeInput (encodeInput x) = some x := decode_encodeInput x
example (b : Nat) (seeds : JointSamplingLaw.SeedArray 0 b) : coinBits seeds = [] :=
  coinBits_zero_trials b seeds
example (M : Nat) (seeds : JointSamplingLaw.SeedArray M 0) : coinBits seeds = [] :=
  coinBits_zero_precision M seeds
example (L : Nat) (x : Input) (coins : CMMSACodec.Bits)
    (h : coins.length ≠ x.trials*x.precision) :
    runOption L (encodeInput x) coins = none := runOption_wrong_coins L x coins h
example (L : Nat) (coins : CMMSACodec.Bits) : runOption L [] coins = none :=
  runOption_bad_input L [] coins decodeInput_empty
