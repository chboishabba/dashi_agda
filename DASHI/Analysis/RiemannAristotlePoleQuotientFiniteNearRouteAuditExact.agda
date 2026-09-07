module DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearRouteAuditExact where

------------------------------------------------------------------------
-- RH FINITE-NEAR ROUTE AUDIT
--
-- The live zero-side theorem is the literal finite reflection-paired
-- target-centred pole-quotient sum. Two route classes remain structurally
-- admissible:
--
--   A. estimate that finite signed exponential/cosine sum directly;
--   B. recover the literal selected target-window explicit-formula producer,
--      supply lawful near extraction, then estimate the transformed side.
--
-- Later target-window owners materially compress route B: PoleNearTargetWindow
-- already carries the exact spectral cluster + finite-near + far equality, and
-- RiemannG2PoleNearTargetWindowSpectralIdentificationCompilerExact compiles that
-- equality into the modulation/HW view once same-selected-test identity is paid.
-- Therefore a second spectral decomposition theorem is NOT a live prerequisite.
--
-- But the literal PoleNearTargetWindow / PoleNearTargetModulation producers are
-- themselves still uninhabited in the current repo graph, and generic
-- WeilTestSpace has no subtraction/cancellation operation from which near
-- extraction follows automatically. Thus route B currently has strictly more
-- producer prerequisites before reaching the same finite-near evaluation leaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Near
import DASHI.Analysis.RiemannG3SourceTransportExact as G3
import DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact as Poisson
import DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact as Target
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2PoleNearTargetWindowSpectralIdentificationCompilerExact as Spectral

------------------------------------------------------------------------
-- Historical generic bridge language retained for compatibility.
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
-- Later-owner reconciliation.
------------------------------------------------------------------------

targetModulationConstructionStillOpen :
  Target.PoleNearTargetModulationBoundary.targetWindowConstructionClosed
    Target.canonicalPoleNearTargetModulationBoundary ≡ false
targetModulationConstructionStillOpen = refl

literalTargetWindowStillOpen :
  Spectral.PoleNearTargetWindowSpectralIdentificationBoundary.literalTargetWindowRecoveredHere
    Spectral.canonicalPoleNearTargetWindowSpectralIdentificationBoundary ≡ false
literalTargetWindowStillOpen = refl

secondSpectralDecompositionReproofPruned :
  Spectral.PoleNearTargetWindowSpectralIdentificationBoundary.secondSpectralDecompositionTheoremRequired
    Spectral.canonicalPoleNearTargetWindowSpectralIdentificationBoundary ≡ false
secondSpectralDecompositionReproofPruned = refl

lawfulNearExtractionStillRequired :
  Window.PoleNearExplicitFormulaBoundary.lawfulNearExtractionRequired
    Window.canonicalPoleNearExplicitFormulaBoundary ≡ true
lawfulNearExtractionStillRequired = refl

explicitFormulaRouteStillOpen :
  Window.PoleNearExplicitFormulaBoundary.explicitFormulaRouteClosed
    Window.canonicalPoleNearExplicitFormulaBoundary ≡ false
explicitFormulaRouteStillOpen = refl

------------------------------------------------------------------------
-- Source-boundary evidence.
------------------------------------------------------------------------

complexPoissonContinuationStillOpenInThatLane :
  Poisson.analyticComplexPoissonContinuationProvedHere
    Poisson.complexPoissonFiniteRetentionBoundary ≡ false
complexPoissonContinuationStillOpenInThatLane = refl

------------------------------------------------------------------------
-- Non-record precedence pins keep the historical compatibility record stable.
------------------------------------------------------------------------

directRouteHasFewerUninhabitedProducerPrerequisites : Bool
directRouteHasFewerUninhabitedProducerPrerequisites = true

directRouteHasFewerUninhabitedProducerPrerequisitesIsTrue :
  directRouteHasFewerUninhabitedProducerPrerequisites ≡ true
directRouteHasFewerUninhabitedProducerPrerequisitesIsTrue = refl

directRouteIsCurrentHighestAlphaZeroSideRoute : Bool
directRouteIsCurrentHighestAlphaZeroSideRoute = true

directRouteIsCurrentHighestAlphaZeroSideRouteIsTrue :
  directRouteIsCurrentHighestAlphaZeroSideRoute ≡ true
directRouteIsCurrentHighestAlphaZeroSideRouteIsTrue = refl

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
    "Both route classes remain logically admissible, but the later target-window owners remove the old ambiguity about scheduling. Route B no longer needs a second spectral cluster+near+far theorem, yet it still requires an uninhabited literal PoleNearTargetModulation/PoleNearTargetWindow producer, same-selected-test identity, and lawful extraction before it can evaluate the same finite near term. Route A directly attacks that finite signed cosine value and therefore has fewer uninhabited prerequisites. Under the current closed-world repo graph, direct finite evaluation is the highest-alpha zero-side route. Existing Hermitian G3 / complex-Poisson donors remain carrier-incompatible without an explicit bridge. RH is not derived."
