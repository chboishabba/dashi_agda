module DASHI.Wikimedia.IbrahimSnowballTiwiHabitatConnectivityRangerAuthorshipQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiMammalTaxaFireResponseQidExact as Prior

------------------------------------------------------------------------
-- TIWI HABITAT / CONNECTIVITY / RANGER-AUTHORSHIP QID SNOWBALL
--
-- Ibrahim follow from taxon-indexed fire-response into habitat structure and
-- landscape genetics. QIDs remain identity-only. Species-level QIDs are not
-- silently promoted to subspecies identities. Published collective authorship,
-- Country authority, research permission, data-use permission and scientific
-- inference remain distinct attribution/authority coordinates.
------------------------------------------------------------------------

northernBrownBandicootQid : Identity.ExternalIdentityDemand
northernBrownBandicootQid = Prior.northernBrownBandicootQid

commonBrushtailPossumSpeciesQid : Identity.ExternalIdentityDemand
commonBrushtailPossumSpeciesQid = Prior.commonBrushtailPossumQid

blackFootedTreeRatSpeciesQid : Identity.ExternalIdentityDemand
blackFootedTreeRatSpeciesQid = Prior.blackFootedTreeRatQid

northernBrushtailPossumSubspeciesQid : Identity.ExternalIdentityDemand
northernBrushtailPossumSubspeciesQid = Identity.mkOptionalIdentityDemand
  "Tiwi habitat/connectivity continuation" "external subspecies identity"
  "northern brushtail possum / Trichosurus vulpecula arnhemensis"
  Identity.wikidataQid
  (Identity.unresolved "No safely verified direct Wikidata subspecies item promoted on 2026-09-11; article Q99969256 is a scholarly article, not the taxon")

blackFootedTreeRatMelvilleSubspeciesQid : Identity.ExternalIdentityDemand
blackFootedTreeRatMelvilleSubspeciesQid = Identity.mkOptionalIdentityDemand
  "Tiwi habitat/connectivity continuation" "external subspecies identity"
  "black-footed tree-rat (Melville Island) / Mesembriomys gouldii melvillensis"
  Identity.wikidataQid
  (Identity.unresolved "Accepted subspecies identity is externally supported, but no safely verified direct Wikidata subspecies item was promoted in this tranche")

------------------------------------------------------------------------
-- Primary 2026 landscape-genetic continuation.
------------------------------------------------------------------------

data TiwiConnectivitySourceRole : Set where
  multiSpeciesLandscapeGeneticStudy : TiwiConnectivitySourceRole

record TiwiConnectivityPrimarySource : Set where
  constructor tiwi-connectivity-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : TiwiConnectivitySourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open TiwiConnectivityPrimarySource public

careyEtAl2026 : TiwiConnectivityPrimarySource
careyEtAl2026 = tiwi-connectivity-primary-source
  "Alexander R. Carey; Teigan Cremona; Georgina Neave; Hugh F. Davies; Brett P. Murphy; Geoffrey J. Cary; Tiwi Rangers; Sam C. Banks"
  "The Contrasting Role of Fire in Shaping Landscape Genetic Patterns of Small Mammals Across Two Islands"
  "Ecology and Evolution 16(4):e73320"
  2026
  "DOI 10.1002/ece3.73320; PMID 42040838; PMCID PMC13107275"
  multiSpeciesLandscapeGeneticStudy
  "Primary landscape-genetic study of northern brown bandicoot, northern brushtail possum and Melville black-footed tree-rat across Bathurst and Melville Islands; resistance surfaces include fire history, rainfall, vegetation, topography, watercourses and feral species at fine and broad scales."
  "Species-, island- and scale-specific gene-flow results do not create a universal fire response, abundance response, habitat mediation law, or transferable Country authority."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Attribution and data-governance roles are not interchangeable.
------------------------------------------------------------------------

data TiwiCareyRole : Set where
  publishedNamedIndividualAuthor
  publishedNamedCollectiveAuthor
  acknowledgedTraditionalOwnerSupport
  acknowledgedInstitutionalSupport
  researchPermitAuthority
  dataUsePermissionAuthority : TiwiCareyRole

record TiwiCareyAttributionReceipt : Set where
  constructor tiwi-carey-attribution-receipt
  field
    source : TiwiConnectivityPrimarySource
    publishedAuthorListReference : String
    tiwiRangersRole : TiwiCareyRole
    tiwiRangersContributionReference : String
    tiwiLandCouncilSupportRole : TiwiCareyRole
    traditionalOwnersRole : TiwiCareyRole
    researchPermitReference : String
    dataAvailabilityReference : String
    dataPermissionRole : TiwiCareyRole
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open TiwiCareyAttributionReceipt public

canonicalCareyAttribution : TiwiCareyAttributionReceipt
canonicalCareyAttribution = tiwi-carey-attribution-receipt
  careyEtAl2026
  "Published author list names Tiwi Rangers as a collective author alongside seven named individual authors."
  publishedNamedCollectiveAuthor
  "Author Contributions: Tiwi Rangers — methodology (equal)."
  acknowledgedInstitutionalSupport
  acknowledgedTraditionalOwnerSupport
  "Tiwi Land Council research permit NRM015; Charles Darwin University Animal Ethics Permit A22010."
  "Publication states the underlying data are available via Zenodo record 16598763 but use requires permission of the Tiwi Land Council."
  dataUsePermissionAuthority
  Attribution.externalSourceOwner refl
  Attribution.dashiFormalisationOwner refl

------------------------------------------------------------------------
-- Habitat / connectivity consumers.
------------------------------------------------------------------------

data ConnectivityScale : Set where
  fineScale broadIslandScale : ConnectivityScale

data TiwiLandscapeVariable : Set where
  fireHistory fireFrequency rainfall vegetation topography watercourses
  feralPredators feralHerbivores geographicDistance midStoreyStructure : TiwiLandscapeVariable

data TiwiConnectivityTaxon : Set where
  bandicoot northernBrushtailPossum melvilleBlackFootedTreeRat : TiwiConnectivityTaxon

record LandscapeGeneticEvidenceCell : Set where
  constructor landscape-genetic-evidence-cell
  field
    taxon : TiwiConnectivityTaxon
    taxonIdentityReference : String
    exactSubspeciesIdentityReference : String
    islandReference : String
    scale : ConnectivityScale
    landscapeVariable : TiwiLandscapeVariable
    geneticResponseReference : String
    modelReference : String
    source : TiwiConnectivityPrimarySource
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open LandscapeGeneticEvidenceCell public

record HabitatAbundanceMediationFrontier : Set where
  constructor habitat-abundance-mediation-frontier
  field
    taxonReference : String
    fireHistoryReference : String
    vegetationStructureReference : String
    geneticConnectivityReference : String
    abundanceReference : String
    samePopulationPaid : Bool
    sameMeasurementWindowPaid : Bool
    vegetationMediationPaid : Bool
    connectivityToAbundancePaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open HabitatAbundanceMediationFrontier public

canonicalHabitatMediationFrontier : HabitatAbundanceMediationFrontier
canonicalHabitatMediationFrontier = habitat-abundance-mediation-frontier
  "Carey 2026 taxa overlap the Davies/Tiwi mammal lineage but use genetic samples collected 2018-2023 rather than the 2015 abundance carrier"
  "Carey resistance surfaces retain long-term fire-history variables"
  "Carey includes vegetation among candidate resistance surfaces; black-footed tree-rat ecology is discussed in relation to well-developed mid-storey under lower fire frequency"
  "Carey landscape-genetic response / gene-flow resistance"
  "Davies 2015 plot-level relative abundance carrier"
  false false false false
  Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Snowball acquisition/payment.
------------------------------------------------------------------------

record TiwiConnectivityAcquisitionState : Set where
  constructor tiwi-connectivity-acquisition-state
  field
    speciesQidsAcquired : Bool
    subspeciesQidsResolved : Bool
    careyPrimaryAcquired : Bool
    collectiveAuthorRoleAcquired : Bool
    researchPermitAcquired : Bool
    dataPermissionAcquired : Bool
    fireHistoryEvidenceAcquired : Bool
    vegetationEvidenceAcquired : Bool
    topographyEvidenceAcquired : Bool
    rainfallEvidenceAcquired : Bool
    feralThreatEvidenceAcquired : Bool
    geneticConnectivityEvidenceAcquired : Bool
    DaviesAbundanceEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open TiwiConnectivityAcquisitionState public

record TiwiConnectivityPaymentState : Set where
  constructor tiwi-connectivity-payment-state
  field
    taxonQidIdentityPaid : Bool
    exactSubspeciesIdentityPaid : Bool
    exactPrimarySourcePaid : Bool
    sourceRoleAttributionPaid : Bool
    collectiveAuthorAttributionPaid : Bool
    researchPermitRolePaid : Bool
    dataPermissionRolePaid : Bool
    exactIslandPaid : Bool
    spatialScalePaid : Bool
    landscapeVariablePaid : Bool
    geneticResponsePaid : Bool
    samePopulationWithDaviesPaid : Bool
    sameTimeWithDaviesPaid : Bool
    habitatMediationPaid : Bool
    connectivityToAbundancePaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open TiwiConnectivityPaymentState public

snowballAcquisitionDoesNotAdvanceTiwiConnectivityPayment :
  TiwiConnectivityAcquisitionState → TiwiConnectivityPaymentState → TiwiConnectivityPaymentState
snowballAcquisitionDoesNotAdvanceTiwiConnectivityPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data SpeciesQidMeansSubspeciesIdentity : Set where
data GeneticConnectivityMeansPopulationAbundance : Set where
data LowFireFrequencyBenefitsEveryTaxon : Set where
data BathurstFireEffectTransfersToMelville : Set where
data MidStoreyAssociationMeansMediation : Set where
data CollectiveAuthorMeansEveryRangerIsNamedAuthor : Set where
data CollectiveAuthorCreatesCountryAuthority : Set where
data AcknowledgementCreatesAuthorship : Set where
data DataPermissionCreatesScientificAuthorship : Set where
data OpenArticleMeansOpenDataUse : Set where
data ResearchPermitEqualsCountryAuthority : Set where
data AcquisitionCreatesPayment : Set where

speciesQidDoesNotPaySubspeciesIdentity : SpeciesQidMeansSubspeciesIdentity → ⊥
speciesQidDoesNotPaySubspeciesIdentity ()

geneticConnectivityDoesNotEqualPopulationAbundance : GeneticConnectivityMeansPopulationAbundance → ⊥
geneticConnectivityDoesNotEqualPopulationAbundance ()

lowFireFrequencyDoesNotBenefitEveryTaxon : LowFireFrequencyBenefitsEveryTaxon → ⊥
lowFireFrequencyDoesNotBenefitEveryTaxon ()

bathurstEffectDoesNotSilentlyTransferToMelville : BathurstFireEffectTransfersToMelville → ⊥
bathurstEffectDoesNotSilentlyTransferToMelville ()

midStoreyAssociationDoesNotCreateMediation : MidStoreyAssociationMeansMediation → ⊥
midStoreyAssociationDoesNotCreateMediation ()

collectiveAuthorDoesNotNameEveryRangerIndividually : CollectiveAuthorMeansEveryRangerIsNamedAuthor → ⊥
collectiveAuthorDoesNotNameEveryRangerIndividually ()

collectiveAuthorshipDoesNotCreateCountryAuthority : CollectiveAuthorCreatesCountryAuthority → ⊥
collectiveAuthorshipDoesNotCreateCountryAuthority ()

acknowledgementDoesNotCreateAuthorship : AcknowledgementCreatesAuthorship → ⊥
acknowledgementDoesNotCreateAuthorship ()

dataPermissionDoesNotCreateScientificAuthorship : DataPermissionCreatesScientificAuthorship → ⊥
dataPermissionDoesNotCreateScientificAuthorship ()

openArticleDoesNotEraseDataPermission : OpenArticleMeansOpenDataUse → ⊥
openArticleDoesNotEraseDataPermission ()

researchPermitDoesNotExhaustCountryAuthority : ResearchPermitEqualsCountryAuthority → ⊥
researchPermitDoesNotExhaustCountryAuthority ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorMammalSnowball : Prior.TiwiMammalQidAcquisitionState → Prior.TiwiMammalQidPaymentState → Prior.TiwiMammalQidPaymentState
priorMammalSnowball = Prior.snowballAcquisitionDoesNotAdvanceTiwiMammalPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary
