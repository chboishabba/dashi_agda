module DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecValidationExact where

import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec

boundary : Codec.CoefficientHybridReplayCodecBoundary
boundary = Codec.canonicalCoefficientHybridReplayCodecBoundary

roundTrip :
  (generator : Codec.SyntheticGenerator) →
  Codec.decodeHybrid (Codec.encodeHybrid generator) ≡ generator
roundTrip = Codec.hybridRoundTripExact

firstResidual : Codec.CoefficientHybridReplayCodecResidual
firstResidual = Codec.firstCoefficientHybridReplayCodecResidual
