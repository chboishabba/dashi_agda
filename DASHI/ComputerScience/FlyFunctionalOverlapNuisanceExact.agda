module DASHI.ComputerScience.FlyFunctionalOverlapNuisanceExact where

-- Thin extension of the Fly NDim owner.
--
-- Two functional-side nuisances are now kept separate from MaleCNS structure.
--
-- (1) The soft VFB JRC2018 carrier is intentionally overlapping: one selected
-- ROI may contribute to multiple painted domains.  That representation itself
-- can induce covariance because two domain traces may reuse the same ROI signal.
--
-- (2) The Gauthey selected ROIs were chosen for high correlation with the
-- published audio stimulus regressor.  Shared exogenous stimulus drive can
-- therefore create region-region covariance even after atlas-overlap geometry
-- is controlled.
--
-- Runtime consumers:
--   x_r(t) = a_r + b_r s(t) + epsilon_r(t)
--   K[r,s] = cosine(ROI-membership-row r, ROI-membership-row s)
--   Ceps    = alpha + beta K + Cresidual
--
-- The stimulus regression is region-local over time and uses no connectome
-- structure or pair outcome.  The overlap alpha/beta fit is repeated on training
-- pairs only inside each split.  Structural NDim fibres are evaluated only after
-- these nuisance coordinates are separated.

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact


data FunctionalNuisanceCoordinate : Set where
  globalCorrelationLevel : FunctionalNuisanceCoordinate
  publishedAudioStimulusDrive : FunctionalNuisanceCoordinate
  paintedDomainOverlapGeometry : FunctionalNuisanceCoordinate

record FunctionalNuisanceConsumerBoundary : Set where
  constructor functional-nuisance-consumer-boundary
  field
    stimulusDriveKeptSeparateFromConnectomeFibres : Bool
    stimulusResidualizationUsesRegionPairOutcomes : Bool
    stimulusResidualizationUsesConnectomeStructure : Bool
    atlasOverlapKeptSeparateFromConnectomeFibres : Bool
    overlapNuisanceFitUsesHeldOutPairs : Bool
    overlapNuisanceFitRepeatedInsideEveryRegionHoldoutFold : Bool
    labelNullPermutesFunctionalTargetAndOverlapGeometryTogether : Bool
    strengthNullScramblesFunctionalOverlapGeometry : Bool
    rawSoftPredictionAutomaticallyImpliesWiringSpecificSignal : Bool
    overlapControlledPredictionAutomaticallyImpliesWiringSpecificSignal : Bool
    stimulusAndOverlapControlledTargetStillRequiresRefittedNulls : Bool
open FunctionalNuisanceConsumerBoundary public

canonicalFunctionalNuisanceConsumerBoundary : FunctionalNuisanceConsumerBoundary
canonicalFunctionalNuisanceConsumerBoundary =
  functional-nuisance-consumer-boundary
    true
    false
    false
    true
    false
    true
    true
    false
    false
    false
    true

-- Non-promotion firewalls.
data StimulusDriveIsConnectomeFibre : Set where
data AtlasOverlapSimilarityIsConnectomeFibre : Set where
data RawSoftLowResidualImpliesWiringSpecificSignal : Set where
data OverlapControlledLowResidualImpliesWiringSpecificSignal : Set where
data StimulusResidualizationProvesStimulusIsNotBiological : Set where
data NuisanceFitMayUseHeldOutPairs : Set where
data LabelNullMayPermuteTargetWithoutOverlapGeometry : Set where

stimulusDriveDoesNotCreateConnectomeFibre :
  StimulusDriveIsConnectomeFibre → ⊥
stimulusDriveDoesNotCreateConnectomeFibre ()

atlasOverlapDoesNotCreateConnectomeFibre :
  AtlasOverlapSimilarityIsConnectomeFibre → ⊥
atlasOverlapDoesNotCreateConnectomeFibre ()

rawSoftLowResidualDoesNotCreateWiringSpecificSignal :
  RawSoftLowResidualImpliesWiringSpecificSignal → ⊥
rawSoftLowResidualDoesNotCreateWiringSpecificSignal ()

overlapControlledLowResidualDoesNotCreateWiringSpecificSignal :
  OverlapControlledLowResidualImpliesWiringSpecificSignal → ⊥
overlapControlledLowResidualDoesNotCreateWiringSpecificSignal ()

stimulusResidualizationDoesNotEraseBiologicalStatus :
  StimulusResidualizationProvesStimulusIsNotBiological → ⊥
stimulusResidualizationDoesNotEraseBiologicalStatus ()

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
    overlapControlledPredictionRemainsLowResidual : Bool
    overlapControlledStrengthNullSeparationImproves : Bool
    overlapControlledStrengthNullRejected : Bool
    overlapControlledLabelNullRejected : Bool
    publishedStimulusControlStillRequired : Bool
    pairSpecificWiringMechanismEstablished : Bool
    independentTrialOrAnimalReplicationStillRequired : Bool
open CurrentSoftCarrierInterpretation public

-- Current execution state after the 26-common-region overlap-controlled run:
--   raw-soft LORO residual                 ~ 0.1485
--   overlap-controlled LORO residual       ~ 0.1360
--   overlap-controlled strength-null p     ~ 0.1881
--   overlap-controlled label-null p        ~ 0.7030
-- Atlas-overlap removal improves both held-out error and strength-null
-- separation, but neither refitted null is rejected.  The next unpaid nuisance
-- is the published exogenous audio drive used to select the ROI population.
currentSoftCarrierInterpretation : CurrentSoftCarrierInterpretation
currentSoftCarrierInterpretation =
  current-soft-carrier-interpretation
    true
    true
    false
    false
    true
    true
    false
    false
    true
    false
    true
