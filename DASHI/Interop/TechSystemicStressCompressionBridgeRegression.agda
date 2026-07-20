module DASHI.Interop.TechSystemicStressCompressionBridgeRegression where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Promotion.TechSystemicStressScenarioBoundary as Tech
import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Compression
import DASHI.Interop.TechSystemicStressCompressionBridge as Bridge

------------------------------------------------------------------------
-- Shared-carrier and partial-phase witnesses.
------------------------------------------------------------------------

negativeScenarioTritAgrees :
  Bridge.scenarioTrit Tech.Trit.sspNegOne ≡ neg
negativeScenarioTritAgrees = refl

unresolvedPhaseDoesNotInventMechanism :
  Bridge.alignScenarioPhase Tech.unresolvedPhase
    ≡ Bridge.unresolvedHasNoMechanismPhase
unresolvedPhaseDoesNotInventMechanism = refl

activePhaseAlignment :
  Bridge.alignScenarioPhase Tech.activeDysfunctionPhase
    ≡ Bridge.alignedActivePhase
activePhaseAlignment = refl

------------------------------------------------------------------------
-- Scenario/news attribution alone remains unsupported.
------------------------------------------------------------------------

greeceFixtureUnsupported :
  Compression.promotionLevel
    (Bridge.scenarioOnlySystemicReceipt
      Tech.canonicalGreeceStyleAttributionCandidate)
    ≡ Compression.unsupportedLevel
greeceFixtureUnsupported = refl

aiFixtureUnsupported :
  Compression.promotionLevel
    (Bridge.scenarioOnlySystemicReceipt
      Tech.canonicalAIStressAttributionCandidate)
    ≡ Compression.unsupportedLevel
aiFixtureUnsupported = refl

------------------------------------------------------------------------
-- Independent mechanism fixtures.
------------------------------------------------------------------------

fracturedResiduals : Compression.ResidualDepthProfile
fracturedResiduals = Compression.residualProfile pos pos pos pos pos pos

activeObservation : Crisis.CrisisObservation
activeObservation = Crisis.observation pos pos pos pos pos neg neg

activeChain : Compression.TransmissionChain
activeChain = Compression.transmission pos pos pos pos pos pos zer

closedModelReceipt : Compression.ModelSelectionReceipt
closedModelReceipt =
  Compression.modelReceipt true true true true true true true

validatedSystemicReceipt : Compression.SystemicSignalReceipt
validatedSystemicReceipt =
  Compression.systemicReceipt
    activeObservation
    fracturedResiduals
    activeChain
    closedModelReceipt
    true
    true
    true

joinedValidatedReceipt : Bridge.TechCrisisCompressionReceipt
joinedValidatedReceipt =
  Bridge.techCrisisCompressionReceipt
    Tech.canonicalTechSystemicStressMachine
    validatedSystemicReceipt
    true
    true
    true
    true
    true
    true
    true
    true

validatedReceiptPromotesOnlyAfterIndependentMechanism :
  Bridge.joinedPromotionLevel joinedValidatedReceipt
    ≡ Compression.validatedModelLevel
validatedReceiptPromotesOnlyAfterIndependentMechanism = refl

validatedReceiptHasFracture :
  Bridge.joinedCompressionRegime joinedValidatedReceipt
    ≡ Compression.fractureRegime
validatedReceiptHasFracture = refl

validatedReceiptCrossLayerStatus :
  Bridge.joinedStatus joinedValidatedReceipt
    ≡ Bridge.validatedMechanismStatus
validatedReceiptCrossLayerStatus = refl

validatedGateCloses :
  Bridge.validatedCrossLayerGate joinedValidatedReceipt ≡ true
validatedGateCloses = refl

------------------------------------------------------------------------
-- Posture and peak boundaries.
------------------------------------------------------------------------

defensivePreservationRelation :
  Bridge.relatePostures
    Tech.defensivePosture
    Crisis.preserveLiquidityPosture
    ≡ Bridge.coherentDefensivePreservation
defensivePreservationRelation = refl

adverseIsNotAutomaticallyDirectional :
  Tech.arbitrarySignInversionAllowed Tech.canonicalDefensiveBoundary ≡ false
adverseIsNotAutomaticallyDirectional = refl

peakDoesNotBecomePriceBottom :
  Bridge.finalPriceBottomClaimed Bridge.canonicalMechanicalPeakBridge ≡ false
peakDoesNotBecomePriceBottom = refl
