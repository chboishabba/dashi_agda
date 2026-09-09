module DASHI.Environment.YeomansKeylineLESCausalBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.YeomansKeylineSourceAttributionExact as Sources
import DASHI.Environment.YeomansKeylineLandscapeHydrologyExact as Keyline
import DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact as Causal
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- KEYLINE -> EXISTING LES / CAUSAL ESTIMAND BRIDGE
--
-- The Yeomans source identifies a design lineage.  An empirical Keyline effect
-- is paid only by a situated intervention, explicit comparator/outcome/horizon,
-- causal identification receipt and measurement provenance.
------------------------------------------------------------------------

keylineInterventionIdentity :
  Keyline.KeylineLandscapeIntervention → Causal.SituatedInterventionIdentity
keylineInterventionIdentity intervention =
  Causal.situated-intervention-identity
    Causal.landManagementPractice
    (Keyline.implementationReference intervention)
    (Keyline.siteHistoryReference intervention)
    (Keyline.temporalHorizonReference intervention)
    "DASHI.Environment.YeomansKeylineSourceAttributionExact"

record KeylineEstimandBinding : Set₂ where
  constructor keyline-estimand-binding
  field
    intervention : Keyline.KeylineLandscapeIntervention
    accounting : Keyline.KeylineWaterAccountingPacket intervention
    identity : Causal.SituatedInterventionIdentity
    identityIsKeylineIntervention : identity ≡ keylineInterventionIdentity intervention
    estimand : Estimand.CausalEffectEstimand
    interventionMatchesEstimandReference : String
    comparatorIsExplicit : Bool
    populationIsExplicit : Bool
    outcomeIsExplicit : Bool
    horizonIsExplicit : Bool
    siteHistoryRetained : Bool
    sourceAttributionReference : String

open KeylineEstimandBinding public

record KeylineLESExperiment
    (binding : KeylineEstimandBinding) : Set₂ where
  constructor keyline-les-experiment
  field
    before : LES.SituatedObservation
    after : LES.SituatedObservation
    comparatorReference : String
    assignmentOrIdentificationReference : String
    topographicMeasurementReference : String
    waterMeasurementReference : String
    erosionOrSedimentMeasurementReference : String
    cropOrEcologicalOutcomeReference : String
    sourceDataProvenanceReference : String
    uncertaintyReference : String
    heldOutOrReplicationReference : String

open KeylineLESExperiment public

record KeylineSOTAEvidenceAdmission : Set where
  constructor keyline-sota-evidence-admission
  field
    source : Sources.KeylineSource
    relation : Sources.KeylineEvidenceRelation
    sourceRelationMatches : relation ≡ Sources.relation source
    implementationMatchReference : String
    siteClimateSoilMatchReference : String
    outcomeDefinitionMatchReference : String
    horizonMatchReference : String
    evidenceMayPayThisEstimand : Bool

open KeylineSOTAEvidenceAdmission public

------------------------------------------------------------------------
-- SOTA evidence cannot cross relation types silently.
------------------------------------------------------------------------

data HistoricalReviewMeansEffectPermission : Set where
data DirectStudyMeansPortableEffectPermission : Set where
data ModelStudyMeansObservedEffectPermission : Set where
data AdjacentMethodMeansDirectKeylineEffectPermission : Set where
data BeforeAfterMeansCausalEffectPermission : Set where
data SameOutcomeMeansSameMechanismPermission : Set where

historicalReviewDoesNotPayEffect : HistoricalReviewMeansEffectPermission → ⊥
historicalReviewDoesNotPayEffect ()
directStudyDoesNotAutomaticallyTransport : DirectStudyMeansPortableEffectPermission → ⊥
directStudyDoesNotAutomaticallyTransport ()
modelStudyDoesNotPayObservedEffect : ModelStudyMeansObservedEffectPermission → ⊥
modelStudyDoesNotPayObservedEffect ()
adjacentMethodDoesNotPayDirectKeylineEffect : AdjacentMethodMeansDirectKeylineEffectPermission → ⊥
adjacentMethodDoesNotPayDirectKeylineEffect ()
beforeAfterDifferenceDoesNotIdentifyCause : BeforeAfterMeansCausalEffectPermission → ⊥
beforeAfterDifferenceDoesNotIdentifyCause ()
sameOutcomeDoesNotIdentifyMechanism : SameOutcomeMeansSameMechanismPermission → ⊥
sameOutcomeDoesNotIdentifyMechanism ()

record KeylineCausalBoundary : Set where
  constructor keyline-causal-boundary
  field
    sourceDesignAndCausalEffectRemainDistinct : Bool
    directModelAndAdjacentEvidenceRemainDistinct : Bool
    populationComparatorOutcomeHorizonRemainExplicit : Bool
    siteTopographyClimateSoilHistoryRemainFirstClass : Bool
    existingCausalEstimandOwnerRemainsAuthoritative : Bool
    onePositiveStudyAutomaticallyPromotesWholeSystem : Bool

canonicalKeylineCausalBoundary : KeylineCausalBoundary
canonicalKeylineCausalBoundary =
  keyline-causal-boundary true true true true true false
