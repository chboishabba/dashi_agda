module DASHI.ComputerScience.RSA260BidiGF2FactorMaskDecoderValidationExact where

import DASHI.ComputerScience.RSA260BidiGF2FactorMaskDecoderExact as Decoder

sampleExpansion :
  Decoder.expandMask8 Decoder.sampleBasis Decoder.sampleMask
  ≡ Decoder.sampleExpectedRow
sampleExpansion = Decoder.sampleExpansionExact

boundary : Decoder.GF2FactorMaskDecoderBoundary
boundary = Decoder.canonicalGF2FactorMaskDecoderBoundary

firstResidual : Decoder.GF2FactorMaskDecoderResidual
firstResidual = Decoder.firstGF2FactorMaskDecoderResidual
