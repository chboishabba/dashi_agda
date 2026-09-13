module DASHI.Wikimedia.IbrahimSnowballIndigenousCustodianshipSavannaCarbonProductivityLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSoilWarmingCarbonNatClimateLESExact as Climate
import DASHI.Wikimedia.IbrahimCountryCommunityKnowledgeAuthorityBridgeExact as CountryAuthority
import DASHI.Governance.SteffensenCulturalFireAuthorityExact as CulturalFire

------------------------------------------------------------------------
-- INDIGENOUS CUSTODIANSHIP / SAVANNA / CARBON-PRODUCTIVITY SNOWBALL
--
-- Country/community authority and empirical ecological effect remain separate.
-- QIDs are identity/navigation coordinates only.  Primary field studies retain
-- their own authorship.  DASHI owns only the crosswalk/formalisation/inference.
------------------------------------------------------------------------

indigenousAustraliansQid : Identity.ExternalIdentityDemand
indigenousAustraliansQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "external people identity"
  "Indigenous Australians" Identity.wikidataQid
  (Identity.verified "Q170355" "Wikidata identity checked 2026-09-10")

aboriginalAustraliansQid : Identity.ExternalIdentityDemand
aboriginalAustraliansQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "external people identity"
  "Aboriginal Australians" Identity.wikidataQid
  (Identity.verified "Q12060728" "Wikidata identity checked 2026-09-10")

savannaQid : Identity.ExternalIdentityDemand
savannaQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "external ecosystem identity"
  "savanna" Identity.wikidataQid
  (Identity.verified "Q42320" "Wikidata savanna identity checked 2026-09-10")

primaryProductionQid : Identity.ExternalIdentityDemand
primaryProductionQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "external ecological-process identity"
  "primary production" Identity.wikidataQid
  (Identity.verified "Q515905" "Wikidata primary-production identity checked 2026-09-10")

carbonSequestrationQid : Identity.ExternalIdentityDemand
carbonSequestrationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "external carbon-process identity"
  "carbon sequestration" Identity.wikidataQid
  (Identity.verified "Q15305550" "Wikidata carbon-sequestration identity checked 2026-09-10")

yibarbukArticleQid : Identity.ExternalIdentityDemand
yibarbukArticleQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "external publication identity"
  "Fire ecology and Aboriginal land management in central Arnhem Land, northern Australia: a tradition of ecosystem management"
  Identity.wikidataQid
  (Identity.verified "Q115431935" "Wikidata scholarly-article identity checked 2026-09-10")

indigenousLandManagementQid : Identity.ExternalIdentityDemand
indigenousLandManagementQid = Identity.mkOptionalIdentityDemand
  "Ibrahim LES Indigenous custodianship continuation" "broad Indigenous land-management concept identity"
  "Indigenous land management" Identity.wikidataQid
  (Identity.unresolved "No safely resolved broad concept QID promoted on 2026-09-10; place/IPA/category items are not substitutes")

------------------------------------------------------------------------
-- Primary empirical / operational sources.
------------------------------------------------------------------------

data CustodianshipCarbonSourceRole : Set where
  continuousAboriginalManagementComparison
  savannaCarbonProductivityFluxStudy
  indigenousFireGHGOperationalStudy
  tiwiCarbonLandscapeExperiment : CustodianshipCarbonSourceRole

record CustodianshipCarbonPrimarySource : Set where
  constructor custodianship-carbon-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : CustodianshipCarbonSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open CustodianshipCarbonPrimarySource public

yibarbukEtAl2001 : CustodianshipCarbonPrimarySource
yibarbukEtAl2001 = custodianship-carbon-primary-source
  "D. Yibarbuk; P. J. Whitehead; J. Russell-Smith; D. Jackson; C. Godjuwa; A. Fisher; P. Cooke; D. Choquenot; D. M. J. S. Bowman"
  "Fire ecology and Aboriginal land management in central Arnhem Land, northern Australia: a tradition of ecosystem management"
  "Journal of Biogeography 28(3):325-343"
  2001
  "DOI 10.1046/j.1365-2699.2001.00555.x"
  continuousAboriginalManagementComparison
  "Primary ecological study comparing fire behaviour and landscape-condition indicators at Dukaladjarranj, a clan estate managed continuously by traditional Aboriginal owners, with other north-Australian sites."
  "Does not establish a universal Indigenous-management effect size, universal carbon benefit, or authority outside the relevant Country/community."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

beringerEtAl2007 : CustodianshipCarbonPrimarySource
beringerEtAl2007 = custodianship-carbon-primary-source
  "Jason Beringer; Lindsay B. Hutley; Nigel J. Tapper; Lucas A. Cernusak"
  "Savanna fires and their impact on net ecosystem productivity in North Australia"
  "Global Change Biology 13:990-1004"
  2007
  "DOI 10.1111/j.1365-2486.2007.01334.x"
  savannaCarbonProductivityFluxStudy
  "Primary five-year eddy-covariance savanna study quantifying net ecosystem productivity and fire impacts on carbon balance at Howard Springs."
  "Does not by itself identify Indigenous custodianship as the treatment, nor make NEP/NBP equivalent to cultural authority or carbon credits."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

russellSmithEtAl2013 : CustodianshipCarbonPrimarySource
russellSmithEtAl2013 = custodianship-carbon-primary-source
  "Jeremy Russell-Smith et al."
  "Managing fire regimes in north Australian savannas: applying Aboriginal approaches to contemporary global problems"
  "Frontiers in Ecology and the Environment"
  2013
  "DOI 10.1890/120251"
  indigenousFireGHGOperationalStudy
  "Primary project-scale analysis of the Western Arnhem Land Fire Abatement programme on Aboriginal lands, reporting accountable methane/nitrous-oxide emissions reductions relative to the pre-project baseline."
  "Does not make project-scale abatement identical to CO2 primary productivity, whole-carbon-cycle sequestration, or transferable Country authority."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

richardsEtAl2012 : CustodianshipCarbonPrimarySource
richardsEtAl2012 = custodianship-carbon-primary-source
  "Anna E. Richards et al."
  "Savanna burning, greenhouse gas emissions and indigenous livelihoods: Introducing the Tiwi Carbon Study"
  "Austral Ecology 37(6):712-723"
  2012
  "DOI 10.1111/j.1442-9993.2012.02395.x"
  tiwiCarbonLandscapeExperiment
  "Primary Tiwi Islands fire-history/carbon study defining landscape-scale experiments and fire-management scenarios with measured ecosystem-carbon stocks and accountable non-CO2 GHG emissions."
  "Scenario abatement and measured stocks do not by themselves prove realized long-term sequestration, productivity gain, or applicability beyond Tiwi conditions."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Consumer separation: productivity, carbon storage, emissions and authority.
------------------------------------------------------------------------

data CustodianshipLESConsumer : Set where
  fireRegime
  habitatMosaic
  biodiversityCondition
  grossPrimaryProduction
  netEcosystemProductivity
  netBiomeProductivity
  vegetationCarbonStock
  soilCarbonStock
  methaneNitrousOxideFireEmissions
  carbonSequestration
  culturalCountryAuthority
  livelihoodOutcome : CustodianshipLESConsumer

record CustodianshipSourceAdmission : Set where
  constructor custodianship-source-admission
  field
    source : CustodianshipCarbonPrimarySource
    exactCountryOrSiteReference : String
    exactManagementReference : String
    exactMeasurementReference : String
    exactTimeBoundaryReference : String
    exactCarbonOrProductivityConsumer : CustodianshipLESConsumer
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open CustodianshipSourceAdmission public

record CountryAuthorityEcologyWeld : Set where
  constructor country-authority-ecology-weld
  field
    countryCommunityAuthorityReference : String
    culturalFireAuthorityReference : String
    empiricalSiteReference : String
    empiricalManagementReference : String
    authorityAndMeasurementSameCountryReceipt : String
    sourceRoleReference : String
    ecologicalEffectReference : String
    authorityCreatesEcologicalEffect : Bool
    ecologicalEffectCreatesAuthority : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsWeldInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open CountryAuthorityEcologyWeld public

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record CustodianshipCarbonAcquisitionState : Set where
  constructor custodianship-carbon-acquisition-state
  field
    peopleQidsAcquired : Bool
    savannaQidAcquired : Bool
    productivityQidAcquired : Bool
    carbonSequestrationQidAcquired : Bool
    broadIndigenousLandManagementQidResolved : Bool
    yibarbukPrimaryAcquired : Bool
    beringerFluxStudyAcquired : Bool
    walfaPrimaryAcquired : Bool
    tiwiPrimaryAcquired : Bool
    fireRegimeEvidenceAcquired : Bool
    biodiversityEvidenceAcquired : Bool
    productivityFluxEvidenceAcquired : Bool
    carbonStockEvidenceAcquired : Bool
    nonCO2FireEmissionEvidenceAcquired : Bool
    communityAuthorityEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open CustodianshipCarbonAcquisitionState public

record CustodianshipCarbonPaymentState : Set where
  constructor custodianship-carbon-payment-state
  field
    qidIdentityPaid : Bool
    exactPrimarySourcePaid : Bool
    sourceRoleAttributionPaid : Bool
    exactCountryCommunityPaid : Bool
    custodialAuthorityPaid : Bool
    managementInterventionIdentityPaid : Bool
    comparatorOrBaselinePaid : Bool
    fireRegimePaid : Bool
    productivityMeasurementPaid : Bool
    ecosystemCarbonBalancePaid : Bool
    fireEmissionAccountingPaid : Bool
    sequestrationPaid : Bool
    biodiversityConsumerPaid : Bool
    livelihoodConsumerPaid : Bool
    causalIdentificationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open CustodianshipCarbonPaymentState public

snowballAcquisitionDoesNotAdvanceCustodianshipCarbonPayment :
  CustodianshipCarbonAcquisitionState → CustodianshipCarbonPaymentState → CustodianshipCarbonPaymentState
snowballAcquisitionDoesNotAdvanceCustodianshipCarbonPayment _ payment = payment

------------------------------------------------------------------------
-- Reuse existing authority and Nat-climate boundaries.
------------------------------------------------------------------------

countryAuthorityBridge : CountryAuthority.CountryCommunityKnowledgeAuthorityBridgeReceipt
countryAuthorityBridge = CountryAuthority.canonicalCountryCommunityKnowledgeAuthorityBridgeReceipt

culturalFireAuthorityBoundary : CulturalFire.CulturalFireAuthorityBoundary
culturalFireAuthorityBoundary = CulturalFire.canonicalCulturalFireAuthorityBoundary

soilClimateBoundary : Climate.SoilClimateLESBoundary
soilClimateBoundary = Climate.canonicalSoilClimateLESBoundary

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data IndigenousIdentityCreatesCountryAuthority : Set where
data CountryAuthorityCreatesCarbonBenefit : Set where
data CarbonBenefitCreatesCountryAuthority : Set where
data FireEmissionAbatementEqualsPrimaryProduction : Set where
data PrimaryProductionEqualsNetEcosystemProductivity : Set where
data NetEcosystemProductivityEqualsNetBiomeProductivity : Set where
data CarbonStockEqualsSequestration : Set where
data NonCO2AbatementEqualsCO2Sequestration : Set where
data OneArnhemStudyCreatesUniversalIndigenousEffect : Set where
data QidCreatesCustodianshipEvidence : Set where
data AcquisitionCreatesPayment : Set where

indigenousIdentityDoesNotCreateCountryAuthority : IndigenousIdentityCreatesCountryAuthority → ⊥
indigenousIdentityDoesNotCreateCountryAuthority ()

countryAuthorityDoesNotCreateCarbonBenefit : CountryAuthorityCreatesCarbonBenefit → ⊥
countryAuthorityDoesNotCreateCarbonBenefit ()

carbonBenefitDoesNotCreateCountryAuthority : CarbonBenefitCreatesCountryAuthority → ⊥
carbonBenefitDoesNotCreateCountryAuthority ()

fireAbatementDoesNotEqualPrimaryProduction : FireEmissionAbatementEqualsPrimaryProduction → ⊥
fireAbatementDoesNotEqualPrimaryProduction ()

primaryProductionDoesNotEqualNEP : PrimaryProductionEqualsNetEcosystemProductivity → ⊥
primaryProductionDoesNotEqualNEP ()

nepDoesNotEqualNBP : NetEcosystemProductivityEqualsNetBiomeProductivity → ⊥
nepDoesNotEqualNBP ()

carbonStockDoesNotEqualSequestration : CarbonStockEqualsSequestration → ⊥
carbonStockDoesNotEqualSequestration ()

nonCO2AbatementDoesNotEqualCO2Sequestration : NonCO2AbatementEqualsCO2Sequestration → ⊥
nonCO2AbatementDoesNotEqualCO2Sequestration ()

oneArnhemStudyDoesNotCreateUniversalIndigenousEffect : OneArnhemStudyCreatesUniversalIndigenousEffect → ⊥
oneArnhemStudyDoesNotCreateUniversalIndigenousEffect ()

qidDoesNotCreateCustodianshipEvidence : QidCreatesCustodianshipEvidence → ⊥
qidDoesNotCreateCustodianshipEvidence ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

record IndigenousCustodianshipCarbonLESBoundary : Set where
  constructor indigenous-custodianship-carbon-les-boundary
  field
    countryAuthorityReused : Bool
    culturalFireAuthorityReused : Bool
    soilClimateConsumerSeparationReused : Bool
    primarySourcesStayExternal : Bool
    broadIndigenousLandManagementQidMayRemainUnresolved : Bool
    productivityAndCarbonMetricsRemainDistinct : Bool
    authorityAndEcologicalEffectRemainDistinct : Bool
    IndigenousManagementUniversalProductivityLawClaimed : Bool
    acquisitionAutomaticallyAdvancesPayment : Bool

canonicalIndigenousCustodianshipCarbonLESBoundary : IndigenousCustodianshipCarbonLESBoundary
canonicalIndigenousCustodianshipCarbonLESBoundary =
  indigenous-custodianship-carbon-les-boundary true true true true true true true false false
