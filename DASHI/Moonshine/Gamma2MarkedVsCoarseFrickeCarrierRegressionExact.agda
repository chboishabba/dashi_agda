module DASHI.Moonshine.Gamma2MarkedVsCoarseFrickeCarrierRegressionExact where

------------------------------------------------------------------------
-- Theorem-bearing regression for the marked/coarse carrier boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact as P11
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine

markedPairCountReallyOne :
  Orbit.pairedOrbitCount P11.p11MarkedFrobeniusSpectrum ≡ 1
markedPairCountReallyOne = P11.p11MarkedPairCountIsOne

markedPairReallyCollapsesUnderForgetLevel :
  Fine.projectFine5 Fine.a0 ≡ Fine.projectFine5 Fine.a1
markedPairReallyCollapsesUnderForgetLevel = P11.a0a1SameCoarseClass

coarseCarrierReallyFullyFixed :
  Orbit.fullyFixed (Spectrum.supersingularOrbitSpectrum Matrix.prime11) ≡ true
coarseCarrierReallyFullyFixed = P11.coarseP11FullyFixed
