module DASHI.Environment.HolzerPondCascadeTreatmentExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.HolzerKrameterhofSourceAttributionExact as HolzerSources
import DASHI.Environment.HolzerKrameterhofIntegratedLandscapeBridgeExact as Holzer
import DASHI.Environment.HolzerKrameterhofAdjacentSOTASourceRegistryExact as SOTA
import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- KRAMETERHOF POND-CASCADE TREATMENT EXPERIMENT
--
-- Attribution order:
-- practitioner report -> candidate mechanism -> adjacent external evidence
-- -> DASHI experiment reconstruction -> measured site transition
-- -> causal estimate -> recommendation.
--
-- No arrow is automatic.  In particular, constructed-wetland literature is
-- adjacent mechanism/design evidence; it is not a direct Krameterhof result.
------------------------------------------------------------------------

data CascadeStageKind : Set where
  productivePond
  plantedRestPond
  openRockChannel
  sedimentationOrSettlingZone
  downstreamProductivePond : CascadeStageKind

data WaterQualityCoordinate : Set where
  dissolvedOxygen
  carbonDioxide
  totalAmmoniacalNitrogen
  nitrite
  nitrate
  temperature
  pH
  conductivity
  suspendedSolids
  turbidity
  flowRate : WaterQualityCoordinate

data ClaimStatus : Set where
  practitionerReported
  mechanismHypothesis
  adjacentLiteratureSupported
  siteMeasured
  causallyEstimated
  replicatedOrHeldOut : ClaimStatus

record CascadeStageIdentity : Set where
  constructor cascade-stage-identity
  field
    stageId : String
    stageKind : CascadeStageKind
    siteBoundaryReference : String
    inletReference : String
    outletReference : String
    hydraulicGeometryReference : String
    residenceTimeReference : String
    vegetationOrMediaReference : String
    sourcePractice : Holzer.SituatedKrameterhofPractice
    practitionerSource : HolzerSources.KrameterhofSource

open CascadeStageIdentity public

record StageMeasurement (stage : CascadeStageIdentity) : Set where
  constructor stage-measurement
  field
    coordinate : WaterQualityCoordinate
    upstreamValueReference : String
    downstreamValueReference : String
    unitReference : String
    methodReference : String
    calibrationReference : String
    uncertaintyReference : String
    sampleTimeReference : String
    commonWaterIdentityReference : String
    measuredAtDeclaredStageBoundary : Bool

open StageMeasurement public

record StageTreatmentEvidence (stage : CascadeStageIdentity) : Set where
  constructor stage-treatment-evidence
  field
    measurements : List (StageMeasurement stage)
    waterBalance : Conservation.WaterBalance
    treatmentRoles : List Aquatic.TreatmentRole
    hydraulicRoles : List Aquatic.HydraulicRole
    microbialCommunityReference : String
    vegetationStateReference : String
    solidsInventoryReference : String
    weatherReference : String
    sourceDataProvenanceReference : String
    status : ClaimStatus

open StageTreatmentEvidence public

------------------------------------------------------------------------
-- Adjacent evidence admission.
------------------------------------------------------------------------

record AdjacentMechanismAdmission
    (stage : CascadeStageIdentity) : Set where
  constructor adjacent-mechanism-admission
  field
    source : SOTA.AdjacentSOTASource
    sharedMechanismReference : String
    hydraulicSimilarityReference : String
    vegetationMediaSimilarityReference : String
    waterChemistrySimilarityReference : String
    loadingSimilarityReference : String
    residenceTimeSimilarityReference : String
    scaleSimilarityReference : String
    relationIsAdjacentNotDirect : Bool
    claimOwner : Attribution.ClaimOwner
    ownerIsExternalSource : claimOwner ≡ Attribution.externalSourceOwner

open AdjacentMechanismAdmission public

------------------------------------------------------------------------
-- Transition chain.
------------------------------------------------------------------------

record CascadeTransition : Set where
  constructor cascade-transition
  field
    fromStage : CascadeStageIdentity
    toStage : CascadeStageIdentity
    sameWaterOrDeclaredMixingReference : String
    transferredFlowReference : String
    travelTimeReference : String
    atmosphericExchangeReference : String
    externalWaterAdditionReference : String
    externalNutrientAdditionReference : String
    sedimentOrBiomassExportReference : String
    beforeEvidence : StageTreatmentEvidence fromStage
    afterEvidence : StageTreatmentEvidence toStage

open CascadeTransition public

record PondCascadeExperiment : Set where
  constructor pond-cascade-experiment
  field
    stages : List CascadeStageIdentity
    transitions : List CascadeTransition
    adjacentEvidence : List SOTA.AdjacentSOTASource
    practitionerReportSource : HolzerSources.KrameterhofSource
    beforeObservation : LES.SituatedObservation
    afterObservation : LES.SituatedObservation
    treatmentSequenceReference : String
    comparatorSequenceReference : String
    assignmentOrIdentificationReference : String
    weatherAndSeasonMatchingReference : String
    stockingAndFeedMatchingReference : String
    hydraulicLoadingMatchingReference : String
    samplingPlanReference : String
    uncertaintyModelReference : String
    dashiExperimentOwner : Attribution.ClaimOwner
    dashiOwnsExperimentReconstruction :
      dashiExperimentOwner ≡ Attribution.dashiFormalisationOwner

open PondCascadeExperiment public

------------------------------------------------------------------------
-- Consumer-specific effect receipts.
------------------------------------------------------------------------

record CascadeCoordinateEffectReceipt
    (experiment : PondCascadeExperiment) : Set where
  constructor cascade-coordinate-effect-receipt
  field
    coordinate : WaterQualityCoordinate
    estimandReference : String
    comparatorReference : String
    effectEstimateReference : String
    uncertaintyReference : String
    siteScopeReference : String
    temporalScopeReference : String
    identificationReceiptReference : String
    claimOwner : Attribution.ClaimOwner
    dashiOwnsCrossSourceInference :
      claimOwner ≡ Attribution.dashiInferenceOwner

open CascadeCoordinateEffectReceipt public

------------------------------------------------------------------------
-- Failure / resilience surface.
------------------------------------------------------------------------

data CascadeFailureMode : Set where
  blockedStandpipe
  channelBypass
  shortCircuiting
  vegetationLoss
  sedimentResuspension
  lowFlowStagnation
  highFlowWashout
  thermalStress
  oxygenCrash
  externalContamination : CascadeFailureMode

record CascadeResilienceObservation : Set where
  constructor cascade-resilience-observation
  field
    failureMode : CascadeFailureMode
    detectionReference : String
    affectedStageReference : String
    waterInventoryEffectReference : String
    dissolvedOxygenEffectReference : String
    nitrogenEffectReference : String
    solidsEffectReference : String
    bioticEffectReference : String
    recoveryReference : String

open CascadeResilienceObservation public

------------------------------------------------------------------------
-- Non-laundering / WrongType barriers.
------------------------------------------------------------------------

data PractitionerRegenerationLabelMeansMeasuredTreatmentPermission : Set where
data WetlandReviewMeansKrameterhofStageEffectPermission : Set where
data IncreasedDOMeansImprovedOverallWaterQualityPermission : Set where
data LowerNitrogenMeansPlantUptakePermission : Set where
data VegetatedStageMeansNutrientSinkPermission : Set where
data FinalOutletImprovementIdentifiesWhichStageWorkedPermission : Set where
data SameStageTypeMeansSamePerformancePermission : Set where
data SiteEffectMeansPortableRecommendationPermission : Set where

regenerationLabelDoesNotPayTreatmentEffect :
  PractitionerRegenerationLabelMeansMeasuredTreatmentPermission → ⊥
regenerationLabelDoesNotPayTreatmentEffect ()

wetlandReviewDoesNotPayKrameterhofStageEffect :
  WetlandReviewMeansKrameterhofStageEffectPermission → ⊥
wetlandReviewDoesNotPayKrameterhofStageEffect ()

increasedDODoesNotProveOverallWaterQualityImprovement :
  IncreasedDOMeansImprovedOverallWaterQualityPermission → ⊥
increasedDODoesNotProveOverallWaterQualityImprovement ()

lowerDissolvedNitrogenDoesNotIdentifyPlantUptake :
  LowerNitrogenMeansPlantUptakePermission → ⊥
lowerDissolvedNitrogenDoesNotIdentifyPlantUptake ()

vegetatedStageDoesNotDefinitionallyBecomeNutrientSink :
  VegetatedStageMeansNutrientSinkPermission → ⊥
vegetatedStageDoesNotDefinitionallyBecomeNutrientSink ()

finalOutletDoesNotIdentifyWhichStageCausedChange :
  FinalOutletImprovementIdentifiesWhichStageWorkedPermission → ⊥
finalOutletDoesNotIdentifyWhichStageCausedChange ()

sameStageLabelDoesNotIdentifyPerformance :
  SameStageTypeMeansSamePerformancePermission → ⊥
sameStageLabelDoesNotIdentifyPerformance ()

siteEffectDoesNotBecomePortableRecommendation :
  SiteEffectMeansPortableRecommendationPermission → ⊥
siteEffectDoesNotBecomePortableRecommendation ()

record PondCascadeExperimentBoundary : Set where
  constructor pond-cascade-experiment-boundary
  field
    practitionerReportAndMeasurementRemainDistinct : Bool
    adjacentLiteratureAndDirectValidationRemainDistinct : Bool
    eachStageRequiresOwnMeasurement : Bool
    inletOutletDifferenceDoesNotIdentifyIntermediateMechanism : Bool
    treatmentBenefitIsMultiCoordinate : Bool
    failureModesAreFirstClass : Bool
    dashiExperimentAndInferenceRemainDashiOwned : Bool
    stageLabelAutomaticallyMeansTreatmentBenefit : Bool

canonicalPondCascadeExperimentBoundary : PondCascadeExperimentBoundary
canonicalPondCascadeExperimentBoundary =
  pond-cascade-experiment-boundary true true true true true true true false
