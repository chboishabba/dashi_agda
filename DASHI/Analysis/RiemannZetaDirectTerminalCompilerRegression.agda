module DASHI.Analysis.RiemannZetaDirectTerminalCompilerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannZetaDirectTerminalCompilerExact as T
import DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact as Certified
import DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact as CertifiedOff
import DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact as DirectCore

private
  boundary = T.canonicalDirectTerminalCompilerBoundary
  upperBoundary = Certified.canonicalCertifiedFiniteNearUpperRouteBoundary
  upperOffBoundary = CertifiedOff.canonicalCertifiedFiniteNearUpperOffBoundary
  factorBoundary = DirectCore.canonicalDirectInputsToAnalyticCoresBoundary

analyticCoreRoutePreferred :
  T.DirectTerminalCompilerBoundary.analyticCoreRoutePreferredOverDeterminantPackaging boundary ≡ true
analyticCoreRoutePreferred = refl

lowCoverageNotManufactured :
  T.DirectTerminalCompilerBoundary.prizeFacingCompilerManufacturesLowCoverage boundary ≡ false
lowCoverageNotManufactured = refl

packetInhabitanceNotClaimed :
  T.DirectTerminalCompilerBoundary.packetInhabitanceClaimedHere boundary ≡ false
packetInhabitanceNotClaimed = refl

rhNotDerivedWithoutPacket :
  T.DirectTerminalCompilerBoundary.rhDerivedWithoutPacket boundary ≡ false
rhNotDerivedWithoutPacket = refl

secondAnalyticNearUpperPruned :
  Certified.CertifiedFiniteNearUpperRouteBoundary.secondAnalyticFiniteSumUpperReceiptRequired
    upperBoundary ≡ false
secondAnalyticNearUpperPruned = refl

orderedUpperCompilesSelectedPayment :
  Certified.CertifiedFiniteNearUpperRouteBoundary.orderedUpperCertificateCompilesMinimalSelectedPayment
    upperBoundary ≡ true
orderedUpperCompilesSelectedPayment = refl

orderedUpperCompilesFinalOffPayment :
  CertifiedOff.CertifiedFiniteNearUpperOffBoundary.certifiedUpperEndpointCompilesTerminalOffPayment
    upperOffBoundary ≡ true
orderedUpperCompilesFinalOffPayment = refl

directOffFactorsThroughCore :
  DirectCore.DirectInputsToAnalyticCoresBoundary.directOffPaymentDefinitionallyFactorsThroughCore
    factorBoundary ≡ true
directOffFactorsThroughCore = refl

directGammaFactorsThroughCore :
  DirectCore.DirectInputsToAnalyticCoresBoundary.directGammaPaymentDefinitionallyFactorsThroughCore
    factorBoundary ≡ true
directGammaFactorsThroughCore = refl

certifiedUpperCompilesOffCore :
  DirectCore.DirectInputsToAnalyticCoresBoundary.certifiedFiniteUpperRouteCompilesOffAnalyticCore
    factorBoundary ≡ true
certifiedUpperCompilesOffCore = refl

rhStillOpenAfterCompression :
  DirectCore.DirectInputsToAnalyticCoresBoundary.rhDerived factorBoundary ≡ false
rhStillOpenAfterCompression = refl
