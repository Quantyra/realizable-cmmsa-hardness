import PvNP.RealizableHardness.ActualMZFixedUSourceDecoderContract

/-! Axiom audit for the visibly external fixed-U MZ source-law interface.
The projection is a field of an assumed structure, not a proved decoder. -/

open PvNP.RealizableHardness.ActualMZFixedUSourceDecoderContract

#check ExternalMZFixedUSourceDecoder.decode
#check selectedDomainTable_sourceLegal
#print axioms ExternalMZFixedUSourceDecoder.decode
#print axioms selectedDomainTable_sourceLegal
