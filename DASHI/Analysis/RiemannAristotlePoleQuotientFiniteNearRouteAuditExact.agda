module DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearRouteAuditExact where

------------------------------------------------------------------------
-- RH FINITE-NEAR ROUTE AUDIT
--
-- The live zero-side theorem is the literal finite reflection-paired
-- target-centred pole-quotient sum.  Two route classes are structurally
-- admissible:
--
--   A. estimate that finite signed exponential/cosine sum directly;
--   B. derive a literal target-centred explicit-formula transform for exactly
--      that carrier and estimate the transformed side.
--
-- The repository's older G3 explicit-formula bridge is useful source material,
-- but it transports a Hermitian matrix object Gz to Gp.  No theorem currently
-- identifies that matrix/Frobenius carrier with the final pole-quotient
-- nearOffFinset signed response.  It is therefore a donor, not a producer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Near
import DASHI.Analysis.RiemannG3SourceTransportExact as G3
import DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact as Poisson

------------------------------------------------------------------------
-- Literal explicit-formula bridge required by route B.
------------------------------------------------------------------------

record LiteralPoleNearExplicitFormulaBridge : Set₁ where
  constructor literal-pole-near-explicit-formula-bridge
  field
    ZeroSide PrimeSide : Set
    poleNearSignedZeroSide : ZeroSide
    transformedPrimeSide : PrimeSide
    TransformCorrespondence : ZeroSide → PrimeSide → Set

    preservesFinalPoleTaper : Set
    preservesTargetCenteredGap : Set
    preservesReflectionPairedSign : Set
    preservesNearIndexCutoff : Set

    correspondence :
      TransformCorrespondence poleNearSignedZeroSide transformedPrimeSide

    bridgeReference : String

open LiteralPoleNearExplicitFormulaBridge public

------------------------------------------------------------------------
-- The older Hermitian G3 bridge has source authority for its own matrix route,
-- but no coercion is provided here to the pole-near carrier.
------------------------------------------------------------------------

record HermitianExplicitFormulaDonor : Set₁ where
  constructor hermitian-explicit-formula-donor
  field
    GzEqualsGpSourceOwned : Set
    donorReference : String
    literalPoleNearCarrierBridge : Set
    literalPoleNearCarrierBridgeReference : String

open HermitianExplicitFormulaDonor public

------------------------------------------------------------------------
-- Current route state.
------------------------------------------------------------------------

data FiniteNearRouteState : Set where
  routeOpenDirect
  routeBlockedOnCarrierBridge
  routeRejectedInformationLoss
  routeClosed
  : FiniteNearRouteState

currentRouteState : Near.FiniteNearRoute → FiniteNearRouteState
currentRouteState Near.directFiniteExponentialSum = routeOpenDirect
currentRouteState Near.targetCenteredExplicitFormula = routeBlockedOnCarrierBridge
currentRouteState Near.localZeroCountOnly = routeRejectedInformationLoss
currentRouteState Near.reflectionOnly = routeRejectedInformationLoss
currentRouteState Near.absoluteEnvelopeMajorant = routeRejectedInformationLoss
currentRouteState Near.montgomeryVaughanDirect = routeRejectedInformationLoss
currentRouteState Near.unbridgedHermitianPoisson = routeRejectedInformationLoss
currentRouteState Near.unbridgedPairKernelFrobenius = routeRejectedInformationLoss
currentRouteState Near.namedHardyDonorOnly = routeRejectedInformationLoss

------------------------------------------------------------------------
-- BIDI route experiments.
------------------------------------------------------------------------

data FiniteNearResearchExperiment : Set where
  directlyEvaluatePoleNearSum
  constructLiteralPoleNearExplicitFormulaBridge
  reuseHermitianG3WithoutBridge
  complexifyPoissonWithoutPoleCarrierMap
  : FiniteNearResearchExperiment

data FeedsFiniteNearProducer : FiniteNearResearchExperiment → Set where
  directRouteFeeds : FeedsFiniteNearProducer directlyEvaluatePoleNearSum
  explicitFormulaBridgeFeeds :
    FeedsFiniteNearProducer constructLiteralPoleNearExplicitFormulaBridge

reuseHermitianG3WithoutBridgeDoesNotFeed :
  FeedsFiniteNearProducer reuseHermitianG3WithoutBridge → ⊥
reuseHermitianG3WithoutBridgeDoesNotFeed ()

complexifyPoissonWithoutPoleCarrierMapDoesNotFeed :
  FeedsFiniteNearProducer complexifyPoissonWithoutPoleCarrierMap → ⊥
complexifyPoissonWithoutPoleCarrierMapDoesNotFeed ()

------------------------------------------------------------------------
-- Source-boundary evidence.
------------------------------------------------------------------------

complexPoissonContinuationStillOpenInThatLane :
  Poisson.analyticComplexPoissonContinuationProvedHere
    Poisson.complexPoissonFiniteRetentionBoundary ≡ false
complexPoissonContinuationStillOpenInThatLane = refl

------------------------------------------------------------------------
-- Boundary/status.
------------------------------------------------------------------------

record FiniteNearRouteAuditBoundary : Set where
  constructor finite-near-route-audit-boundary
  field
    directFiniteSignedRouteFeedsCurrentRHProducer : Bool
    directFiniteSignedRouteFeedsCurrentRHProducerIsTrue :
      directFiniteSignedRouteFeedsCurrentRHProducer ≡ true

    literalTargetCenteredExplicitFormulaWouldFeedCurrentRHProducer : Bool
    literalTargetCenteredExplicitFormulaWouldFeedCurrentRHProducerIsTrue :
      literalTargetCenteredExplicitFormulaWouldFeedCurrentRHProducer ≡ true

    existingHermitianG3ExplicitFormulaIsDefinitionallyPoleNearBridge : Bool
    existingHermitianG3ExplicitFormulaIsDefinitionallyPoleNearBridgeIsFalse :
      existingHermitianG3ExplicitFormulaIsDefinitionallyPoleNearBridge ≡ false

    existingComplexPoissonLaneAlreadyClosesPoleNearBridge : Bool
    existingComplexPoissonLaneAlreadyClosesPoleNearBridgeIsFalse :
      existingComplexPoissonLaneAlreadyClosesPoleNearBridge ≡ false

    directFiniteRouteClosed : Bool
    directFiniteRouteClosedIsFalse : directFiniteRouteClosed ≡ false

    literalPoleNearExplicitFormulaBridgeClosed : Bool
    literalPoleNearExplicitFormulaBridgeClosedIsFalse :
      literalPoleNearExplicitFormulaBridgeClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFiniteNearRouteAuditBoundary : FiniteNearRouteAuditBoundary
canonicalFiniteNearRouteAuditBoundary =
  finite-near-route-audit-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The source-native live alternatives are: directly evaluate the finite pole-near signed cosine sum, or first construct a literal target-centred explicit-formula bridge for that exact carrier. Existing Hermitian Gz=Gp / complex-Poisson machinery is not silently promoted because its carrier differs. No theorem-difficulty ordering between the two live alternatives is asserted."
