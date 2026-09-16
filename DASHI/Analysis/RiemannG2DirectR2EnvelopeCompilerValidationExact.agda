module DASHI.Analysis.RiemannG2DirectR2EnvelopeCompilerValidationExact where

import DASHI.Analysis.RiemannG2DirectR2EnvelopeCompilerExact as O

compilerTargetsActualClusterResponse :
  O.DirectR2EnvelopeCompilerBoundary.envelopeTargetsActualClusterResponse
    O.canonicalDirectR2EnvelopeCompilerBoundary ≡ true
compilerTargetsActualClusterResponse = refl

noIntermediateClusterMargin :
  O.DirectR2EnvelopeCompilerBoundary.intermediateQuantitativeClusterMarginReintroduced
    O.canonicalDirectR2EnvelopeCompilerBoundary ≡ false
noIntermediateClusterMargin = refl

rateProducerStillOpen :
  O.DirectR2EnvelopeCompilerBoundary.inverseSquareRateProducerInhabitedHere
    O.canonicalDirectR2EnvelopeCompilerBoundary ≡ false
rateProducerStillOpen = refl
