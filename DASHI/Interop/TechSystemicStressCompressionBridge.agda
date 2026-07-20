module DASHI.Interop.TechSystemicStressCompressionBridge where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Promotion.TechSystemicStressScenarioBoundary as Tech
import DASHI.Economics.SystemicCrisisSignalKernel as Crisis
import DASHI.Economics.SystemicCrisisCompressionBridge as Compression

------------------------------------------------------------------------
-- Cross-pollination bridge.
--
-- TechSystemicStressScenarioBoundary supplies the observation vocabulary,
-- BAD-window geometry, scenario attribution, capital posture, and execution
-- boundary.  SystemicCrisisSignalKernel and SystemicCrisisCompressionBridge
-- supply the mechanism-first plumbing classifier, quotient-residual fracture,
-- transmission chain, MDL gate, and promotion ladder.
--
-- This module joins those surfaces without identifying any of them:
--
--   scenario attribution != observed transmission mechanism
--   adverse signed regime != negative price direction
--   BAD/news alignment != causal or predictive evidence
--   compression fracture != sovereign crisis
--   mechanical abatement != final price bottom
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Shared trit seam.
------------------------------------------------------------------------

scenarioTrit : SSP.SSPTrit → Trit
scenarioTrit = SSP.toTrit

scenarioTrit-neg : scenarioTrit SSP.sspNegOne ≡ neg
scenarioTrit-neg = refl

scenarioTrit-zero : scenarioTrit SSP.sspZero ≡ zer
scenarioTrit-zero = refl

scenarioTrit-pos : scenarioTrit SSP.sspPosOne ≡ pos
scenarioTrit-pos = refl

------------------------------------------------------------------------
-- Phase alignment is partial on purpose.
--
-- The scenario layer has an explicit unresolved phase.  The mechanism kernel
-- has no corresponding positive mechanism claim, so unresolved does not get
-- silently coerced to normal, proximity, or active crisis.
------------------------------------------------------------------------

data CrisisPhaseAlignment : Set where
  alignedNormalPhase : CrisisPhaseAlignment
  alignedFragilityPhase : CrisisPhaseAlignment
  alignedProximityPhase : CrisisPhaseAlignment
  alignedActivePhase : CrisisPhaseAlignment
  alignedAbatingPhase : CrisisPhaseAlignment
  unresolvedHasNoMechanismPhase : CrisisPhaseAlignment

alignScenarioPhase : Tech.StressPhase → CrisisPhaseAlignment
alignScenarioPhase Tech.latentFragilityPhase = alignedFragilityPhase
alignScenarioPhase Tech.triggerProximityPhase = alignedProximityPhase
alignScenarioPhase Tech.activeDysfunctionPhase = alignedActivePhase
alignScenarioPhase Tech.stabilizationPhase = alignedAbatingPhase
alignScenarioPhase Tech.unresolvedPhase = unresolvedHasNoMechanismPhase

------------------------------------------------------------------------
-- Posture relation.
--
-- Capital posture and crisis posture remain distinct types.  The relation is
-- advisory/governance metadata, not an executable portfolio instruction.
------------------------------------------------------------------------

data PostureRelation : Set where
  coherentDefensivePreservation : PostureRelation
  coherentDefensiveReduction : PostureRelation
  coherentObservationMonitoring : PostureRelation
  coherentOpportunityReengagement : PostureRelation
  postureCombinationNeedsReview : PostureRelation

relatePostures : Tech.CapitalPosture → Crisis.CrisisPosture → PostureRelation
relatePostures Tech.defensivePosture Crisis.preserveLiquidityPosture =
  coherentDefensivePreservation
relatePostures Tech.defensivePosture Crisis.reduceRiskPosture =
  coherentDefensiveReduction
relatePostures Tech.observationalPosture Crisis.monitorPosture =
  coherentObservationMonitoring
relatePostures Tech.opportunityPosture Crisis.reengageCautiouslyPosture =
  coherentOpportunityReengagement
relatePostures _ _ = postureCombinationNeedsReview

------------------------------------------------------------------------
-- Scenario-only evidence is deliberately unable to promote plumbing.
------------------------------------------------------------------------

scenarioOnlyObservation : Crisis.CrisisObservation
scenarioOnlyObservation = Crisis.observation neg neg neg neg neg neg neg

scenarioOnlyResiduals : Compression.ResidualDepthProfile
scenarioOnlyResiduals = Compression.residualProfile zer zer zer zer zer zer

scenarioOnlyModelReceipt : Compression.ModelSelectionReceipt
scenarioOnlyModelReceipt =
  Compression.modelReceipt false false false false false false false

scenarioOnlySystemicReceipt :
  Tech.ScenarioAttributionCandidate → Compression.SystemicSignalReceipt
scenarioOnlySystemicReceipt candidate =
  Compression.systemicReceipt
    scenarioOnlyObservation
    scenarioOnlyResiduals
    (Compression.triggerOnlyChain
      (scenarioTrit
        (Tech.signedPeakRegime (Tech.adverseWindow candidate))))
    scenarioOnlyModelReceipt
    true
    true
    true

scenarioAttributionCannotPromoteMechanism :
  (candidate : Tech.ScenarioAttributionCandidate) →
  Compression.promotionLevel (scenarioOnlySystemicReceipt candidate)
    ≡ Compression.unsupportedLevel
scenarioAttributionCannotPromoteMechanism candidate = refl

canonicalGreeceAlignmentCannotPromoteMechanism :
  Compression.promotionLevel
    (scenarioOnlySystemicReceipt Tech.canonicalGreeceStyleAttributionCandidate)
    ≡ Compression.unsupportedLevel
canonicalGreeceAlignmentCannotPromoteMechanism = refl

canonicalAIAttributionCannotPromoteMechanism :
  Compression.promotionLevel
    (scenarioOnlySystemicReceipt Tech.canonicalAIStressAttributionCandidate)
    ≡ Compression.unsupportedLevel
canonicalAIAttributionCannotPromoteMechanism = refl

------------------------------------------------------------------------
-- Combined status.
--
-- Scenario attribution answers "where is stress concentrated?".
-- Compression regime answers "is the selected quotient/model failing?".
-- Promotion level answers "how much of the transmission mechanism has actually
-- been receipted and validated?".  None substitutes for another.
------------------------------------------------------------------------

data CrossLayerStatus : Set where
  attributionOnlyStatus : CrossLayerStatus
  structuralWatchStatus : CrossLayerStatus
  compressionFractureStatus : CrossLayerStatus
  observedMechanismStatus : CrossLayerStatus
  validatedMechanismStatus : CrossLayerStatus
  mechanicalAbatementStatus : CrossLayerStatus

crossLayerStatus :
  Tech.StressPhase →
  Compression.CompressionRegime →
  Compression.PromotionLevel →
  CrossLayerStatus
crossLayerStatus Tech.stabilizationPhase _ _ = mechanicalAbatementStatus
crossLayerStatus _ _ Compression.validatedModelLevel = validatedMechanismStatus
crossLayerStatus _ _ Compression.observedMechanismLevel = observedMechanismStatus
crossLayerStatus _ Compression.fractureRegime _ = compressionFractureStatus
crossLayerStatus Tech.latentFragilityPhase Compression.watchRegime _ =
  structuralWatchStatus
crossLayerStatus Tech.triggerProximityPhase Compression.watchRegime _ =
  structuralWatchStatus
crossLayerStatus _ _ _ = attributionOnlyStatus

------------------------------------------------------------------------
-- Joined receipt.
--
-- The receipt binds the candidate scenario machine to an independently formed
-- mechanism/MDL receipt.  It does not manufacture either side from the other.
------------------------------------------------------------------------

record TechCrisisCompressionReceipt : Set where
  constructor techCrisisCompressionReceipt
  field
    scenarioMachine : Tech.TechSystemicStressMachine
    systemicReceipt : Compression.SystemicSignalReceipt
    scenarioSourceBound : Bool
    mechanismSourceBound : Bool
    clockAndWindowAligned : Bool
    noLookaheadLeakage : Bool
    sideInformationCounted : Bool
    scenarioAttributionIndependentOfOutcome : Bool
    scenarioDoesNotStandInForTransmission : Bool
    signedRegimeDoesNotStandInForPriceDirection : Bool

open TechCrisisCompressionReceipt public

joinedCompressionRegime :
  TechCrisisCompressionReceipt → Compression.CompressionRegime
joinedCompressionRegime r =
  Compression.compressionRegime
    (Compression.residuals (systemicReceipt r))

joinedPromotionLevel :
  TechCrisisCompressionReceipt → Compression.PromotionLevel
joinedPromotionLevel r = Compression.promotionLevel (systemicReceipt r)

joinedStatus : TechCrisisCompressionReceipt → CrossLayerStatus
joinedStatus r =
  crossLayerStatus
    (Tech.phase (Tech.phaseAssessment (scenarioMachine r)))
    (joinedCompressionRegime r)
    (joinedPromotionLevel r)

------------------------------------------------------------------------
-- Hard conjunction for a validated tech/systemic mechanism claim.
--
-- This is intentionally stronger than a BAD day, news match, technology
-- concentration observation, compression fracture, or active crisis phase
-- alone.  It requires cross-layer source binding and a validated mechanism.
------------------------------------------------------------------------

infixr 6 _and_

_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

validatedCrossLayerGate : TechCrisisCompressionReceipt → Bool
validatedCrossLayerGate r =
  scenarioSourceBound r
  and mechanismSourceBound r
  and clockAndWindowAligned r
  and noLookaheadLeakage r
  and sideInformationCounted r
  and scenarioAttributionIndependentOfOutcome r
  and scenarioDoesNotStandInForTransmission r
  and signedRegimeDoesNotStandInForPriceDirection r
  and Compression.mdlGateClosed
        (Compression.modelSelection (systemicReceipt r))
  and Compression.mechanismEvidence (systemicReceipt r)

------------------------------------------------------------------------
-- Peak semantics remain mechanical.
------------------------------------------------------------------------

record MechanicalPeakBridge : Set where
  constructor mechanicalPeakBridge
  field
    scenarioPhase : Tech.StressPhase
    mechanismReceipt : Compression.SystemicSignalReceipt
    scenarioReportsStabilization : Bool
    mechanismReportsAbatement : Bool
    finalPriceBottomClaimed : Bool
    finalPriceBottomClaimedIsFalse : finalPriceBottomClaimed ≡ false

open MechanicalPeakBridge public

canonicalMechanicalPeakBridge : MechanicalPeakBridge
canonicalMechanicalPeakBridge =
  mechanicalPeakBridge
    Tech.stabilizationPhase
    (scenarioOnlySystemicReceipt Tech.canonicalAIStressAttributionCandidate)
    true
    false
    false
    refl

mechanicalPeakNeverSuppliesPriceBottom :
  (p : MechanicalPeakBridge) → finalPriceBottomClaimed p ≡ false
mechanicalPeakNeverSuppliesPriceBottom p = finalPriceBottomClaimedIsFalse p

techSystemicStressCompressionBridgeSummary : String
techSystemicStressCompressionBridgeSummary =
  "Tech/AI and Greece-style scenario attribution is joined to the mechanism-first crisis and quotient-MDL kernels through a shared trit seam, partial phase alignment, independent receipts, and a hard cross-layer gate; BAD windows, news matches, compression fracture, and expectation cycles cannot independently promote a systemic or sovereign mechanism claim."
