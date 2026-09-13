module DASHI.Wikimedia.IbrahimSnowballIndigenousPyrodiversityFaunaProductivityCarbonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballIndigenousCustodianshipSavannaCarbonProductivityLESExact as Prior
import DASHI.Wikimedia.IbrahimSnowballBiodiversityNutrientRestorationLESExact as Biodiversity

------------------------------------------------------------------------
-- INDIGENOUS PYRODIVERSITY / VEGETATION / FAUNA / PRODUCTIVITY / CARBON
--
-- Continuation of the Indigenous custodianship LES snowball.  Country and
-- community authority stay separate from measured fire-mosaic, biodiversity,
-- productivity and carbon effects.  QIDs are navigation coordinates only;
-- primary studies retain their own authorship and bounded experimental role.
------------------------------------------------------------------------

pyrodiversityQid : Identity.ExternalIdentityDemand
pyrodiversityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim Indigenous pyrodiversity LES continuation" "external ecological concept identity"
  "pyrodiversity" Identity.wikidataQid
  (Identity.unresolved "No safely resolved broad pyrodiversity concept QID promoted on 2026-09-10; article QIDs are not concept substitutes")

fireRegimeQid : Identity.ExternalIdentityDemand
fireRegimeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim Indigenous pyrodiversity LES continuation" "external ecological process identity"
  "fire regime" Identity.wikidataQid
  (Identity.unresolved "No safely resolved broad fire-regime concept QID promoted on 2026-09-10")

savannaQid : Identity.ExternalIdentityDemand
savannaQid = Prior.savannaQid

biodiversityQid : Identity.ExternalIdentityDemand
biodiversityQid = Biodiversity.biodiversityQid

primaryProductionQid : Identity.ExternalIdentityDemand
primaryProductionQid = Prior.primaryProductionQid

carbonSequestrationQid : Identity.ExternalIdentityDemand
carbonSequestrationQid = Prior.carbonSequestrationQid

yibarbukArticleQid : Identity.ExternalIdentityDemand
yibarbukArticleQid = Prior.yibarbukArticleQid

------------------------------------------------------------------------
-- Primary empirical carriers.
------------------------------------------------------------------------

data PyrodiversitySourceRole : Set where
  fineScaleMosaicFieldModelStudy
  indigenousPlantDiversityFieldStudy
  fireSensitiveConiferManagementComparison
  tiwiLandscapeCarbonBiodiversityExperiment : PyrodiversitySourceRole

record PyrodiversityPrimarySource : Set where
  constructor pyrodiversity-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : PyrodiversitySourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PyrodiversityPrimarySource public

trauernichtEtAl2015 : PyrodiversityPrimarySource
trauernichtEtAl2015 = pyrodiversity-primary-source
  "Clay Trauernicht; Barry W. Brook; Brett P. Murphy; Grant J. Williamson; David M. J. S. Bowman"
  "Local and global pyrogeographic evidence that Indigenous fire management creates pyrodiversity"
  "Ecology and Evolution 5(9):1908-1918"
  2015
  "DOI 10.1002/ece3.1494; PMID 26140206"
  fineScaleMosaicFieldModelStudy
  "Primary study combining Arnhem Land field evidence on long-unburnt Callitris habitat with cellular-automata fire-size simulations to examine how small patchy burning can generate fine-scale fire-age diversity."
  "Field observation plus simulation does not establish a universal pyrodiversity-benefit law, Country authority, or direct productivity/carbon effect."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

greenwoodEtAl2024 : PyrodiversityPrimarySource
greenwoodEtAl2024 = pyrodiversity-primary-source
  "Leanne Greenwood; Rebecca Bliege Bird; C. McGuire; N. Jadai; J. Price; A. Skroblin; S. van Leeuwen; D. Nimmo"
  "Indigenous pyrodiversity promotes plant diversity"
  "Biological Conservation 291:110479"
  2024
  "DOI 10.1016/j.biocon.2024.110479"
  indigenousPlantDiversityFieldStudy
  "Primary north-western Australian study comparing landscapes spanning active Indigenous burning and coarser lightning-driven mosaics, relating time-since-fire and fire-frequency diversity to plant richness/diversity including edible plants."
  "Observational landscape associations do not by themselves identify every causal mechanism, universal biodiversity benefit, net ecosystem productivity, sequestration, or transferable authority."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

bowmanEtAl2022 : PyrodiversityPrimarySource
bowmanEtAl2022 = pyrodiversity-primary-source
  "David M. J. S. Bowman; Grant J. Williamson; Fay H. Johnston; Clarence J. W. Bowman; Brett P. Murphy; Christopher I. Roos; Clay Trauernicht; Joshua Rostron; Lynda D. Prior"
  "Population collapse of a Gondwanan conifer follows the loss of Indigenous fire regimes in a northern Australian savanna"
  "Scientific Reports 12:9081"
  2022
  "DOI 10.1038/s41598-022-12946-3"
  fireSensitiveConiferManagementComparison
  "Primary Arnhem Plateau comparison using fire-sensitive Callitris intratropica as a bio-indicator across an Aboriginal estate retaining traditional burning and adjacent country where that fire-management system was disrupted."
  "Does not turn one indicator species into whole-biodiversity equivalence and does not make management history a randomized treatment or universal carbon-productivity result."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

richardsTiwi2012 : PyrodiversityPrimarySource
richardsTiwi2012 = pyrodiversity-primary-source
  "Anna E. Richards et al."
  "Savanna burning, greenhouse gas emissions and indigenous livelihoods: Introducing the Tiwi Carbon Study"
  "Austral Ecology 37(6):712-723"
  2012
  "DOI 10.1111/j.1442-9993.2012.02395.x"
  tiwiLandscapeCarbonBiodiversityExperiment
  "Primary Tiwi landscape fire/carbon study with fire history, ecosystem-carbon stocks, experimental-fire plots and biodiversity survey components supporting long-term full-carbon and biodiversity evaluation."
  "Scenario abatement, measured stocks and biodiversity observations remain distinct from realized sequestration, NEP/NBP and universal ecological benefit."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Exact consumer coordinates and source admissions.
------------------------------------------------------------------------

data IndigenousPyroConsumer : Set where
  timeSinceFireDiversity
  fireFrequencyDiversity
  maximumLandscapeBurnFraction
  longUnburntPatchAvailability
  fireSensitiveVegetationCondition
  plantSpeciesRichness
  plantSpeciesComposition
  ediblePlantDiversity
  faunaOccurrence
  grossPrimaryProduction
  netEcosystemProductivity
  vegetationCarbonStock
  soilCarbonStock
  accountableFireGHG : IndigenousPyroConsumer

record IndigenousPyroSourceAdmission : Set where
  constructor indigenous-pyro-source-admission
  field
    source : PyrodiversityPrimarySource
    exactCountryOrSite : String
    exactCommunityOrManagementContext : String
    exactFireHistoryOrTreatment : String
    exactConsumer : IndigenousPyroConsumer
    exactMeasurement : String
    comparatorOrReference : String
    timeBoundary : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open IndigenousPyroSourceAdmission public

------------------------------------------------------------------------
-- Same-site payment geometry.
------------------------------------------------------------------------

record PyrodiversityToEcologyWeld : Set where
  constructor pyrodiversity-to-ecology-weld
  field
    authorityReference : String
    CountryReference : String
    managementReference : String
    fireMosaicReference : String
    vegetationReference : String
    faunaReference : String
    productivityReference : String
    carbonReference : String
    sameSiteReceipt : String
    sameTimeBoundaryReceipt : String
    sourceRoleReceipt : String
    authorityCreatesEffect : Bool
    effectCreatesAuthority : Bool
    biodiversityCreatesProductivity : Bool
    productivityCreatesCarbonBenefit : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsWeldInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open PyrodiversityToEcologyWeld public

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record IndigenousPyroAcquisitionState : Set where
  constructor indigenous-pyro-acquisition-state
  field
    pyrodiversityQidResolved : Bool
    fireRegimeQidResolved : Bool
    savannaQidAcquired : Bool
    biodiversityQidAcquired : Bool
    primaryProductionQidAcquired : Bool
    trauernichtPrimaryAcquired : Bool
    greenwoodPrimaryAcquired : Bool
    bowmanCallitrisPrimaryAcquired : Bool
    tiwiPrimaryAcquired : Bool
    fireHistoryEvidenceAcquired : Bool
    patchSizeEvidenceAcquired : Bool
    plantDiversityEvidenceAcquired : Bool
    fireSensitiveVegetationEvidenceAcquired : Bool
    faunaEvidenceAcquired : Bool
    productivityEvidenceAcquired : Bool
    carbonStockEvidenceAcquired : Bool
    authorityEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open IndigenousPyroAcquisitionState public

record IndigenousPyroPaymentState : Set where
  constructor indigenous-pyro-payment-state
  field
    qidIdentityPaid : Bool
    exactPrimarySourcePaid : Bool
    sourceRoleAttributionPaid : Bool
    exactCountryCommunityPaid : Bool
    custodialAuthorityPaid : Bool
    managementIdentityPaid : Bool
    fireMosaicIdentityPaid : Bool
    comparatorOrReferencePaid : Bool
    vegetationConsumerPaid : Bool
    faunaConsumerPaid : Bool
    biodiversityConsumerPaid : Bool
    productivityConsumerPaid : Bool
    carbonConsumerPaid : Bool
    sameSiteCrossConsumerPaid : Bool
    causalIdentificationPaid : Bool
    replicationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open IndigenousPyroPaymentState public

snowballAcquisitionDoesNotAdvanceIndigenousPyroPayment :
  IndigenousPyroAcquisitionState → IndigenousPyroPaymentState → IndigenousPyroPaymentState
snowballAcquisitionDoesNotAdvanceIndigenousPyroPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data PyrodiversityMeansBiodiversityBenefit : Set where
data PlantDiversityMeansFaunaBenefit : Set where
data BiodiversityMeansProductivity : Set where
data ProductivityMeansNetCarbonBenefit : Set where
data FineScaleMosaicMeansLowerGHG : Set where
data CallitrisResponseMeansWholeBiodiversity : Set where
data IndigenousBurningLabelCreatesCountryAuthority : Set where
data ArticleQidCreatesExperimentalEvidence : Set where
data CrossStudyCompositionCreatesSameSite : Set where
data AcquisitionCreatesPayment : Set where

pyrodiversityDoesNotDefinitionallyCreateBiodiversityBenefit : PyrodiversityMeansBiodiversityBenefit → ⊥
pyrodiversityDoesNotDefinitionallyCreateBiodiversityBenefit ()

plantDiversityDoesNotDefinitionallyCreateFaunaBenefit : PlantDiversityMeansFaunaBenefit → ⊥
plantDiversityDoesNotDefinitionallyCreateFaunaBenefit ()

biodiversityDoesNotDefinitionallyCreateProductivity : BiodiversityMeansProductivity → ⊥
biodiversityDoesNotDefinitionallyCreateProductivity ()

productivityDoesNotDefinitionallyCreateNetCarbonBenefit : ProductivityMeansNetCarbonBenefit → ⊥
productivityDoesNotDefinitionallyCreateNetCarbonBenefit ()

fineScaleMosaicDoesNotDefinitionallyCreateLowerGHG : FineScaleMosaicMeansLowerGHG → ⊥
fineScaleMosaicDoesNotDefinitionallyCreateLowerGHG ()

callitrisDoesNotExhaustBiodiversity : CallitrisResponseMeansWholeBiodiversity → ⊥
callitrisDoesNotExhaustBiodiversity ()

indigenousBurningLabelDoesNotCreateCountryAuthority : IndigenousBurningLabelCreatesCountryAuthority → ⊥
indigenousBurningLabelDoesNotCreateCountryAuthority ()

articleQidDoesNotCreateExperimentalEvidence : ArticleQidCreatesExperimentalEvidence → ⊥
articleQidDoesNotCreateExperimentalEvidence ()

crossStudyCompositionDoesNotCreateSameSite : CrossStudyCompositionCreatesSameSite → ⊥
crossStudyCompositionDoesNotCreateSameSite ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorCustodianshipBoundary : Prior.IndigenousCustodianshipCarbonLESBoundary
priorCustodianshipBoundary = Prior.canonicalIndigenousCustodianshipCarbonLESBoundary

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary
