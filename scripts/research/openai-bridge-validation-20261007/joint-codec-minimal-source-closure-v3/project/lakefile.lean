import Lake
open Lake DSL
package jointCodec
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib Complexitylib where
  roots := #[`Complexitylib.SAT.Encoding, `Complexitylib.SAT.ThreeSAT, `Complexitylib.Classes.P.Cobham, `Complexitylib.Classes.P.Cobham.Internal.Algebra, `Complexitylib.Classes.P.Cobham.Internal.Reverse]
lean_lib OAI where
  roots := #[`OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas]
lean_lib JointCodec where
  roots := #[`LocalThreeSATBinaryCodec, `LocalThreeSATBinaryCodecSemantics, `LocalThreeSATBinaryCodecRuntime, `LocalThreeSATBinaryCodecUpstream]
