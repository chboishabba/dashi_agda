module DASHI.Analysis.RiemannG2CurrentGenericHighFrontierRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact as DirectFrontier
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as GenericHigh
import DASHI.Analysis.RiemannG2UniformCertifiedNearUpperHighProducerExact as CertifiedHigh
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannG2ClayTerminalGenericHighCoordinateExact as Clay

------------------------------------------------------------------------
-- INTROSPECTIVE REFINEMENT OF THE CURRENT FRONTIER
--
-- Keep the existing direct frontier as the producer-facing acquisition map.
-- The new observation is downstream: the high/low and Clay consumers do not
-- need to know whether the high contradiction was produced by literal phase,
-- a proof-carrying certified upper, or another exact same-object producer.
------------------------------------------------------------------------

terminalHighConsumerIsImplementationNeutral :
  GenericHigh.UniformHighContradictionBoundary.terminalHighConsumerNeedsLiteralPhaseImplementation
    GenericHigh.canonicalUniformHighContradictionBoundary ≡ false
terminalHighConsumerIsImplementationNeutral = refl

literalPhaseCompilesGenericHighConsumer :
  GenericHigh.UniformHighContradictionBoundary.literalPhaseProducerCompilesGenericHighContradiction
    GenericHigh.canonicalUniformHighContradictionBoundary ≡ true
literalPhaseCompilesGenericHighConsumer = refl

certifiedUpperCompilesGenericHighConsumer :
  CertifiedHigh.UniformCertifiedNearUpperHighBoundary.certifiedRouteCompilesGenericHighContradiction
    CertifiedHigh.canonicalUniformCertifiedNearUpperHighBoundary ≡ true
certifiedUpperCompilesGenericHighConsumer = refl

certifiedRouteKeepsBalanceDownstream :
  CertifiedHigh.UniformCertifiedNearUpperHighBoundary.finalBalanceAvailableToCertifiedMargin
    CertifiedHigh.canonicalUniformCertifiedNearUpperHighBoundary ≡ false
certifiedRouteKeepsBalanceDownstream = refl

negativeRHCompilerIsHighStrategyNeutral :
  Negative.ConstructiveNegativeRHBoundary.terminalNegativeRHCompilerRequiresLiteralPhaseImplementation
    Negative.canonicalConstructiveNegativeRHBoundary ≡ false
negativeRHCompilerIsHighStrategyNeutral = refl

oneCoordinatePackageCompilesLowAndStability :
  Coordinate.AnalyticCoordinateTerminalRefinementBoundary.oneSameCarrierHalfCharacterisationCompilesCriticalRefinement
    Coordinate.canonicalAnalyticCoordinateTerminalRefinementBoundary ≡ true
oneCoordinatePackageCompilesLowAndStability = refl

genericClayWrapperNeedsNoLiteralImplementation :
  Clay.GenericHighCoordinateClayBoundary.terminalClayWrapperRequiresLiteralPhaseImplementation
    Clay.canonicalGenericHighCoordinateClayBoundary ≡ false
genericClayWrapperNeedsNoLiteralImplementation = refl

genericClayWrapperNeedsNoCertifiedImplementation :
  Clay.GenericHighCoordinateClayBoundary.terminalClayWrapperRequiresCertifiedUpperImplementation
    Clay.canonicalGenericHighCoordinateClayBoundary ≡ false
genericClayWrapperNeedsNoCertifiedImplementation = refl

genericClayWrapperCompilesRHConditionally :
  Clay.GenericHighCoordinateClayBoundary.theseInputsCompileRiemannHypothesisFor
    Clay.canonicalGenericHighCoordinateClayBoundary ≡ true
genericClayWrapperCompilesRHConditionally = refl

record CurrentGenericHighFrontierRefinementBoundary : Set where
  constructor current-generic-high-frontier-refinement-boundary
  field
    directFrontierRemainsProducerAcquisitionMap : Bool
    directFrontierRemainsProducerAcquisitionMapIsTrue :
      directFrontierRemainsProducerAcquisitionMap ≡ true

    terminalHighConsumerIsProducerAgnostic : Bool
    terminalHighConsumerIsProducerAgnosticIsTrue :
      terminalHighConsumerIsProducerAgnostic ≡ true

    literalPhaseAndCertifiedUpperShareTerminalSpine : Bool
    literalPhaseAndCertifiedUpperShareTerminalSpineIsTrue :
      literalPhaseAndCertifiedUpperShareTerminalSpine ≡ true

    oneSharedCoordinateRefinementFeedsLowAndStability : Bool
    oneSharedCoordinateRefinementFeedsLowAndStabilityIsTrue :
      oneSharedCoordinateRefinementFeedsLowAndStability ≡ true

    representationEqualityStillFirstDirectNonanalyticWall : Bool
    representationEqualityStillFirstDirectNonanalyticWallIsTrue :
      representationEqualityStillFirstDirectNonanalyticWall ≡ true

    strictClusterResponseMarginStillFirstHighAnalyticWall : Bool
    strictClusterResponseMarginStillFirstHighAnalyticWallIsTrue :
      strictClusterResponseMarginStillFirstHighAnalyticWall ≡ true

    exactHeadAgdaKernelValidationOwned : Bool
    exactHeadAgdaKernelValidationOwnedIsFalse :
      exactHeadAgdaKernelValidationOwned ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCurrentGenericHighFrontierRefinementBoundary :
  CurrentGenericHighFrontierRefinementBoundary
canonicalCurrentGenericHighFrontierRefinementBoundary =
  current-generic-high-frontier-refinement-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Keep RiemannG2CurrentDirectOneLeafFrontierExact as the acquisition map: first realize nearResponseAt(J)=literal finite near sum, then prove either the direct literal strict ClusterResponse theorem or a certified upper plus strict certified envelope. Downstream, compile either producer into one implementation-neutral uniform high contradiction. One shared analytic-coordinate refinement supplies the low verified-region transport and critical-line stability. No second Clay architecture is introduced; exact-head Agda validation and RH remain unowned."
