import Lake
open Lake DSL
package jointCodecProbe where
  srcDir := "sources"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI
lean_lib Complexitylib
lean_lib PvNP
lean_lib LocalThreeSATBinaryCodec
lean_lib LocalThreeSATBinaryCodecSemantics
lean_lib LocalThreeSATBinaryCodecRuntime
lean_lib ImportProbe
