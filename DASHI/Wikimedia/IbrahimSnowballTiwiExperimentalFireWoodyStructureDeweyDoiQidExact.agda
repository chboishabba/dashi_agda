module DASHI.Wikimedia.IbrahimSnowballTiwiExperimentalFireWoodyStructureDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiShrubPredationMediationDeweyDoiQidExact as Prior
import DASHI.Wikimedia.IbrahimSnowballTiwiSameExperimentFireBiodiversityCarbonExact as TiwiExperiment

------------------------------------------------------------------------
-- TIWI EXPERIMENTAL FIRE -> WOODY STRUCTURE SNOWBALL
--
-- Freeman et al. 2018 uses the Tiwi Carbon Study experimental fire network.
-- This pays an experimental fire-frequency -> woody size-structure edge on the
-- same experiment family already used by Davies et al. mammal monitoring.
-- It does NOT by itself pay shrub-density mediation, cat access, mammal
-- demography, or full fire -> shrub -> cat -> taxon causality.
------------------------------------------------------------------------

understoryQid : Identity.ExternalIdentityDemand
understoryQid = Identity.mkOptionalIdentityDemand
  "Tiwi experimental fire/woody-structure continuation" "external vegetation-layer identity"
  "understory / understorey" Identity.wikidataQid
  (Identity.verified "Q422666" "Wikidata understory concept inspected 2026-09-11; vegetation-layer identity is not plot-level structure evidence")

woodyPlantQid : Identity.ExternalIdentityDemand
woodyPlantQid = Identity.mkOptionalIdentityDemand
  "Tiwi experimental fire/woody-structure continuation" "external plant-life-form identity"
  "woody plant" Identity.wikidataQid
  (Identity.verified "Q757163" "Wikidata woody-plant concept inspected 2026-09-11; concept identity does not create fire-response evidence")

treeQid : Identity.ExternalIdentityDemand
treeQid = Identity.mkOptionalIdentityDemand
  "Tiwi experimental fire/woody-structure continuation" "external plant-life-form identity"
  "tree" Identity.wikidataQid
  (Identity.verified "Q10884" "Wikidata tree concept inspected 2026-09-11")

------------------------------------------------------------------------
-- Ibrahim / Dewey / DOI / QID navigation coordinates.
------------------------------------------------------------------------

woodyStructureCoordinate : Traversal.DashiKnowledgeCoordinate
woodyStructureCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiExperimentalFireWoodyStructureDeweyDoiQidExact.agda"
  "Tiwi savanna woody-structure / understorey consumer"
  "577.4 — savanna/grassland ecology; classification only"
  "Q422666; Q757163; Q10884"
  "DOI 10.3389/fpls.2018.00644"

mammalFireCoordinate : Traversal.DashiKnowledgeCoordinate
mammalFireCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Wikimedia/IbrahimSnowballTiwiExperimentalFireWoodyStructureDeweyDoiQidExact.agda"
  "Tiwi experimental-fire mammal-response consumer"
  "599 — Mammalia; taxon identity remains separate"
  "Q194272; Q732477; Q1763261; Q303877"
  "DOI 10.1111/1365-2664.13170"

woodyStructureCrossPollinatesMammals : Traversal.DashiFirstLinkEdge
woodyStructureCrossPollinatesMammals = Traversal.dashi-first-link-edge
  woodyStructureCoordinate mammalFireCoordinate Traversal.crossPollinatesWith
  Traversal.canonicalDashiFirstLinkPolicy
  "Freeman vegetation and Davies mammal studies reuse the Tiwi Carbon Study fire-treatment network; same experiment family does not itself prove vegetation mediation"
  true

------------------------------------------------------------------------
-- Primary source attribution.
------------------------------------------------------------------------

record ExperimentalFireWoodyPrimarySource : Set where
  constructor experimental-fire-woody-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open ExperimentalFireWoodyPrimarySource public

freemanEtAl2018 : ExperimentalFireWoodyPrimarySource
freemanEtAl2018 = experimental-fire-woody-primary-source
  "Michelle E. Freeman; Brett P. Murphy; Anna E. Richards; Peter A. Vesk; Garry D. Cook"
  "Facultative and Obligate Trees in a Mesic Savanna: Fire Effects on Savanna Structure Imply Contrasting Strategies of Eco-Taxonomic Groups"
  "Frontiers in Plant Science 9:644"
  2018
  "DOI 10.3389/fpls.2018.00644; PMID 29868096"
  "Primary census on Melville Island Tiwi Carbon Study annual, triennial and fire-exclusion treatments. Total tree density did not significantly differ among treatments, while sapling densities were higher in triennial and unburnt treatments than annual burning; eco-taxonomic groups showed different size-structure strategies."
  "This pays fire-frequency effects on measured woody size structure under the study design. It does not directly measure shrub density as used by Davies/Penton, does not identify cat access, and does not prove mammal mediation or universal savanna response."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Same-experiment-family composition.  Keep exact plot/sample joins distinct.
------------------------------------------------------------------------

record TiwiExperimentalFireStructureJoin : Set where
  constructor tiwi-experimental-fire-structure-join
  field
    TiwiCarbonStudyExperimentFamily : Bool
    annualTriennialUnburntTreatments : Bool
    FreemanWoodyStructureMeasured : Bool
    DaviesMammalResponseMeasured : Bool
    sameExperimentFamilyPaid : Bool
    exactSamePlotJoinPaid : Bool
    exactSameSamplingUnitPaid : Bool
    exactSameMeasurementWindowPaid : Bool
    fireToWoodyStructureEffectPaid : Bool
    fireToShrubDensityEffectPaid : Bool
    woodyStructureToMammalMediationPaid : Bool
    shrubToCatMediationPaid : Bool
    completeFireStructurePredatorTaxonMediationPaid : Bool
    dashiCrossSourceOwner : Attribution.ClaimOwner
    dashiOwnsCrossSourceInferenceOnly : dashiCrossSourceOwner ≡ Attribution.dashiInferenceOwner

open TiwiExperimentalFireStructureJoin public

canonicalTiwiExperimentalFireStructureJoin : TiwiExperimentalFireStructureJoin
canonicalTiwiExperimentalFireStructureJoin = tiwi-experimental-fire-structure-join
  true true true true true
  false false false
  true false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Snowball acquisition and payment remain separate.
------------------------------------------------------------------------

record TiwiExperimentalFireStructureAcquisitionState : Set where
  constructor tiwi-experimental-fire-structure-acquisition-state
  field
    understoryQidAcquired : Bool
    woodyPlantQidAcquired : Bool
    treeQidAcquired : Bool
    FreemanPrimaryAcquired : Bool
    DaviesPrimaryAcquired : Bool
    TiwiExperimentIdentityAcquired : Bool
    treatmentHistoryAcquired : Bool
    woodySizeStructureAcquired : Bool
    mammalResponseAcquired : Bool
    shrubPredationEvidenceRetained : Bool
    outOfOrderEvidenceRetained : Bool

open TiwiExperimentalFireStructureAcquisitionState public

record TiwiExperimentalFireStructurePaymentState : Set where
  constructor tiwi-experimental-fire-structure-payment-state
  field
    qidIdentityPaid : Bool
    deweyClassificationPaid : Bool
    doiSourceIdentityPaid : Bool
    sourceAttributionPaid : Bool
    sameExperimentFamilyPaid : Bool
    treatmentIdentityPaid : Bool
    woodyStructureConsumerPaid : Bool
    experimentalFireToWoodyStructurePaid : Bool
    exactPlotJoinPaid : Bool
    shrubDensityConsumerPaid : Bool
    fireToShrubDensityPaid : Bool
    shrubToCatAccessPaid : Bool
    predatorToTaxonResponsePaid : Bool
    jointMediationPaid : Bool
    CountryAuthorityRetained : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open TiwiExperimentalFireStructurePaymentState public

snowballAcquisitionDoesNotAdvanceTiwiExperimentalFireStructurePayment :
  TiwiExperimentalFireStructureAcquisitionState →
  TiwiExperimentalFireStructurePaymentState →
  TiwiExperimentalFireStructurePaymentState
snowballAcquisitionDoesNotAdvanceTiwiExperimentalFireStructurePayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data UnderstoryQidMeansMeasuredUnderstory : Set where
data WoodyPlantQidMeansFireResponse : Set where
data TreeDensityMeansShrubDensity : Set where
data SameExperimentFamilyMeansSamePlot : Set where
data FireToWoodyStructureMeansFireToShrubDensity : Set where
data FireToStructureMeansMammalMediation : Set where
data SameTreatmentVocabularyMeansSameSample : Set where
data AcquisitionCreatesPayment : Set where

understoryQidDoesNotCreateMeasuredUnderstory : UnderstoryQidMeansMeasuredUnderstory → ⊥
understoryQidDoesNotCreateMeasuredUnderstory ()

woodyPlantQidDoesNotCreateFireResponse : WoodyPlantQidMeansFireResponse → ⊥
woodyPlantQidDoesNotCreateFireResponse ()

treeDensityDoesNotEqualShrubDensity : TreeDensityMeansShrubDensity → ⊥
treeDensityDoesNotEqualShrubDensity ()

sameExperimentFamilyDoesNotMeanSamePlot : SameExperimentFamilyMeansSamePlot → ⊥
sameExperimentFamilyDoesNotMeanSamePlot ()

fireWoodyEffectDoesNotCreateShrubEffect : FireToWoodyStructureMeansFireToShrubDensity → ⊥
fireWoodyEffectDoesNotCreateShrubEffect ()

fireStructureDoesNotCreateMammalMediation : FireToStructureMeansMammalMediation → ⊥
fireStructureDoesNotCreateMammalMediation ()

sameTreatmentVocabularyDoesNotMeanSameSample : SameTreatmentVocabularyMeansSameSample → ⊥
sameTreatmentVocabularyDoesNotMeanSameSample ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorShrubSnowball :
  Prior.TiwiShrubPredationAcquisitionState →
  Prior.TiwiShrubPredationPaymentState →
  Prior.TiwiShrubPredationPaymentState
priorShrubSnowball = Prior.snowballAcquisitionDoesNotAdvanceTiwiShrubPredationPayment

priorExperimentSnowball :
  TiwiExperiment.TiwiSameExperimentAcquisitionState →
  TiwiExperiment.TiwiSameExperimentPaymentState →
  TiwiExperiment.TiwiSameExperimentPaymentState
priorExperimentSnowball = TiwiExperiment.snowballAcquisitionDoesNotAdvanceTiwiSameExperimentPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

traversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
traversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary
