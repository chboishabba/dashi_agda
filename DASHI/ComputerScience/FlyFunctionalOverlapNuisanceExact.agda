module DASHI.ComputerScience.FlyFunctionalOverlapNuisanceExact where

-- Thin extension of the Fly NDim owner.
--
-- The soft VFB JRC2018 carrier is intentionally overlapping: one selected ROI
-- may contribute to multiple painted domains.  That representation itself can
-- induce functional covariance because two domain traces may reuse some of the
-- same ROI signals.  This nuisance belongs to the functional/provenance side;
-- it is not a MaleCNS connectome fibre.
--
-- Runtime consumer:
--   K[r,s] = cosine(ROI-membership-row r, ROI-membership-row s)
--   Cfunc   = alpha + beta K + Cresidual
-- where alpha/beta are fit on training pairs only inside each split.  Structural
-- NDim fibres are then evaluated against Cresidual.

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact


data FunctionalNuisanceCoordinate : Set where
  globalCorrelationLevel : FunctionalNuisanceCoordinate
  paintedDomainOverlapGeometry : FunctionalNuisanceCoordinate

record OverlapControlledConsumerBoundary : Set where
  constructor overlap-controlled-consumer-boundary
  field
    atlasOverlapKeptSeparateFromConnectomeFibres : Bool
    nuisanceFitUsesHeldOutPairs : Bool
    nuisanceFitRepeatedInsideEveryRegionHoldoutFold : Bool
    labelNullPermutesFunctionalTargetAndOverlapGeometryTogether : Bool
    strengthNullScramblesFunctionalOverlapGeometry : Bool
    rawSoftPredictionAutomaticallyImpliesWiringSpecificSignal : Bool
    controlledTargetStillRequiresRefittedNulls : Bool
open OverlapControlledConsumerBoundary public

canonicalOverlapControlledConsumerBoundary : OverlapControlledConsumerBoundary
canonicalOverlapControlledConsumerBoundary =
  overlap-controlled-consumer-boundary
    true
    false
    true
    true
    false
    false
    true

-- Non-promotion firewalls.
data AtlasOverlapSimilarityIsConnectomeFibre : Set where
data RawSoftLowResidualImpliesWiringSpecificSignal : Set where
data NuisanceFitMayUseHeldOutPairs : Set where
data LabelNullMayPermuteTargetWithoutOverlapGeometry : Set where

atlasOverlapDoesNotCreateConnectomeFibre :
  AtlasOverlapSimilarityIsConnectomeFibre → ⊥
atlasOverlapDoesNotCreateConnectomeFibre ()

rawSoftLowResidualDoesNotCreateWiringSpecificSignal :
  RawSoftLowResidualImpliesWiringSpecificSignal → ⊥
rawSoftLowResidualDoesNotCreateWiringSpecificSignal ()

nuisanceFitCannotUseHeldOutPairs :
  NuisanceFitMayUseHeldOutPairs → ⊥
nuisanceFitCannotUseHeldOutPairs ()

labelNullMustCarryOverlapGeometry :
  LabelNullMayPermuteTargetWithoutOverlapGeometry → ⊥
labelNullMustCarryOverlapGeometry ()

record CurrentSoftCarrierInterpretation : Set where
  constructor current-soft-carrier-interpretation
  field
    expandedCarrierRetainsMoreFunctionalDomains : Bool
    rawSoftNDimPredictionImprovesOnPathBaseline : Bool
    rawSoftLabelPermutationNullRejected : Bool
    rawSoftStrengthPreservingWiringNullRejected : Bool
    overlapControlledConsumerStillRequired : Bool
    independentTrialOrAnimalReplicationStillRequired : Bool
open CurrentSoftCarrierInterpretation public

-- Current execution state after the 26-common-region soft-carrier run:
-- predictive residual remains low, but both raw-soft nulls fail to separate.
currentSoftCarrierInterpretation : CurrentSoftCarrierInterpretation
currentSoftCarrierInterpretation =
  current-soft-carrier-interpretation
    true
    true
    false
    false
    true
    true
