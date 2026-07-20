module DASHI.Economics.SystemicCrisisCompressionBridge where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.MinimalKernelAlgebra as Minimal
import DASHI.Cognition.QuotientResidualDynamics as QuotientResidual
import DASHI.Economics.SystemicCrisisSignalKernel as Crisis

------------------------------------------------------------------------
-- Compression-stability bridge for mechanism-first crisis detection.
--
-- Existing DASHI content supplies the general signed-ternary carrier,
-- support/sign factorisation, symmetry actions, quotient compatibility,
-- quotient-residual theorem surface, and optional MDL/action descent laws.
-- This module does not duplicate those constructions.  It instantiates their
-- observable boundary for financial plumbing and keeps price narratives,
-- expectation cycles, and deterministic timelines outside the classifier.
------------------------------------------------------------------------

infixr 6 _∧_
infixr 5 _∨_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

isPositive : Trit → Bool
isPositive neg = false
isPositive zer = false
isPositive pos = true

isNegative : Trit → Bool
isNegative neg = true
isNegative zer = false
isNegative pos = false

------------------------------------------------------------------------
-- Residual-depth observations.
--
-- shallowActivation records ordinary local surprise.  Deep activation records
-- failure at successively coarser triadic scales.  Side-information growth and
-- quotient failure state that the currently selected chart/model is ceasing to
-- compress the observations.  These are diagnostics; monotonicity is supplied
-- only by a separate MDL/action receipt, in line with MinimalKernelAlgebra.
------------------------------------------------------------------------

record ResidualDepthProfile : Set where
  constructor residualProfile
  field
    shallowActivation      : Trit
    middleActivation       : Trit
    deepActivation         : Trit
    sideInformationGrowth  : Trit
    quotientFailure        : Trit
    modelMismatch          : Trit

open ResidualDepthProfile public

data CompressionRegime : Set where
  compressiveRegime : CompressionRegime
  watchRegime       : CompressionRegime
  fractureRegime    : CompressionRegime

compressionFracture : ResidualDepthProfile → Bool
compressionFracture r =
  isPositive (deepActivation r)
  ∧ isPositive (sideInformationGrowth r)
  ∧ isPositive (quotientFailure r)

compressionWatch : ResidualDepthProfile → Bool
compressionWatch r =
  isPositive (middleActivation r)
  ∨ isPositive (modelMismatch r)
  ∨ isPositive (sideInformationGrowth r)

compressionRegime : ResidualDepthProfile → CompressionRegime
compressionRegime r with compressionFracture r
... | true  = fractureRegime
... | false with compressionWatch r
...   | true  = watchRegime
...   | false = compressiveRegime

------------------------------------------------------------------------
-- Explicit transmission chain.
--
-- The chain separates a trigger asset from the balance-sheet, margin,
-- liquidation, market-function, and sovereign-funding links.  A trigger is
-- neither necessary nor sufficient evidence for the downstream links.
------------------------------------------------------------------------

record TransmissionChain : Set where
  constructor transmission
  field
    triggerAssetShock       : Trit
    balanceSheetLoss        : Trit
    marginTightening        : Trit
    synchronousDeleveraging : Trit
    treasuryLiquidation     : Trit
    marketFunctionFailure   : Trit
    sovereignFundingStress  : Trit

open TransmissionChain public

cascadeActive : TransmissionChain → Bool
cascadeActive c =
  isPositive (balanceSheetLoss c)
  ∧ isPositive (marginTightening c)
  ∧ isPositive (synchronousDeleveraging c)
  ∧ isPositive (treasuryLiquidation c)
  ∧ isPositive (marketFunctionFailure c)

sovereignTransmissionObserved : TransmissionChain → Bool
sovereignTransmissionObserved c =
  cascadeActive c
  ∧ isPositive (sovereignFundingStress c)

triggerOnlyChain : Trit → TransmissionChain
triggerOnlyChain trigger = transmission trigger zer zer zer zer zer zer

triggerAloneDoesNotActivateCascade :
  (trigger : Trit) → cascadeActive (triggerOnlyChain trigger) ≡ false
triggerAloneDoesNotActivateCascade trigger = refl

------------------------------------------------------------------------
-- Evidence and MDL promotion gates.
------------------------------------------------------------------------

record ModelSelectionReceipt : Set where
  constructor modelReceipt
  field
    sourceBound                   : Bool
    deterministicDecodeAvailable : Bool
    trainTestSeparated            : Bool
    outOfSampleValidated          : Bool
    sideInformationCounted        : Bool
    mdlImproves                   : Bool
    competingModelsCompared       : Bool

open ModelSelectionReceipt public

mdlGateClosed : ModelSelectionReceipt → Bool
mdlGateClosed r =
  sourceBound r
  ∧ deterministicDecodeAvailable r
  ∧ trainTestSeparated r
  ∧ outOfSampleValidated r
  ∧ sideInformationCounted r
  ∧ mdlImproves r
  ∧ competingModelsCompared r

record SystemicSignalReceipt : Set where
  constructor systemicReceipt
  field
    observation             : Crisis.CrisisObservation
    residuals               : ResidualDepthProfile
    transmissionChain       : TransmissionChain
    modelSelection          : ModelSelectionReceipt
    noLookaheadLeakage      : Bool
    noNarrativePromotion    : Bool
    noDeterministicTimeline : Bool

open SystemicSignalReceipt public

data PromotionLevel : Set where
  unsupportedLevel      : PromotionLevel
  diagnosticLevel       : PromotionLevel
  observedMechanismLevel : PromotionLevel
  validatedModelLevel   : PromotionLevel

mechanismEvidence : SystemicSignalReceipt → Bool
mechanismEvidence r =
  Crisis.marketFunctionBreak (observation r)
  ∧ cascadeActive (transmissionChain r)
  ∧ noLookaheadLeakage r
  ∧ noNarrativePromotion r
  ∧ noDeterministicTimeline r

promotionLevel : SystemicSignalReceipt → PromotionLevel
promotionLevel r with mechanismEvidence r
... | false with Crisis.latentFragility (observation r)
...   | true  = diagnosticLevel
...   | false = unsupportedLevel
... | true with mdlGateClosed (modelSelection r)
...   | true  = validatedModelLevel
...   | false = observedMechanismLevel

------------------------------------------------------------------------
-- Expectation/adoption frameworks remain a separate observation layer.
------------------------------------------------------------------------

data ExpectationCycle : Set where
  innovationTrigger     : ExpectationCycle
  inflatedExpectations  : ExpectationCycle
  disillusionment       : ExpectationCycle
  enlightenment         : ExpectationCycle
  productivityPlateau   : ExpectationCycle

record TechnologyExpectationObservation : Set where
  constructor technologyExpectation
  field
    cycle           : ExpectationCycle
    adoptionStress  : Trit
    valuationStress : Trit

expectationOnlyReceipt :
  TechnologyExpectationObservation → ModelSelectionReceipt → SystemicSignalReceipt
expectationOnlyReceipt e m =
  systemicReceipt
    (Crisis.observation neg neg neg neg neg neg neg)
    (residualProfile zer zer zer zer zer zer)
    (triggerOnlyChain (TechnologyExpectationObservation.valuationStress e))
    m true true true

expectationCycleCannotPromotePlumbing :
  (e : TechnologyExpectationObservation) (m : ModelSelectionReceipt) →
  promotionLevel (expectationOnlyReceipt e m) ≡ unsupportedLevel
expectationCycleCannotPromotePlumbing e m = refl

------------------------------------------------------------------------
-- Online synthesis: combine the hysteretic plumbing phase with model fracture.
------------------------------------------------------------------------

data MonitoringPosture : Set where
  ordinaryMonitoring   : MonitoringPosture
  modelReview          : MonitoringPosture
  proximityAlert       : MonitoringPosture
  activeDysfunction    : MonitoringPosture
  mechanicalAbatement  : MonitoringPosture

monitoringPosture : Crisis.CrisisPhase → CompressionRegime → MonitoringPosture
monitoringPosture Crisis.activePhase _ = activeDysfunction
monitoringPosture Crisis.abatingPhase _ = mechanicalAbatement
monitoringPosture Crisis.proximityPhase _ = proximityAlert
monitoringPosture Crisis.fragilityPhase fractureRegime = proximityAlert
monitoringPosture Crisis.fragilityPhase _ = modelReview
monitoringPosture Crisis.normalPhase fractureRegime = modelReview
monitoringPosture Crisis.normalPhase watchRegime = modelReview
monitoringPosture Crisis.normalPhase compressiveRegime = ordinaryMonitoring

------------------------------------------------------------------------
-- Peak means mechanical abatement, not a guaranteed price bottom.
------------------------------------------------------------------------

peakMechanicsObserved : SystemicSignalReceipt → Bool
peakMechanicsObserved r =
  Crisis.mechanicalRecovery (observation r)
  ∧ isNegative (deepActivation (residuals r))
  ∧ isNegative (sideInformationGrowth (residuals r))
  ∧ isNegative (quotientFailure (residuals r))

priceBottomClaimed : SystemicSignalReceipt → Bool
priceBottomClaimed _ = false

peakDoesNotClaimPriceBottom :
  (r : SystemicSignalReceipt) → priceBottomClaimed r ≡ false
peakDoesNotClaimPriceBottom r = refl
