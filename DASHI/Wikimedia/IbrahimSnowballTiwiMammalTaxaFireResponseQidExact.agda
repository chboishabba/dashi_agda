module DASHI.Wikimedia.IbrahimSnowballTiwiMammalTaxaFireResponseQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiPlotJoinTemporalQidExact as Prior

------------------------------------------------------------------------
-- TIWI MAMMAL TAXA / FIRE-RESPONSE / QID SNOWBALL
--
-- Continue the Ibrahim walk from the Tiwi same-plot carrier down into the
-- actual mammal taxa measured in Davies et al.  Taxon QIDs are identity-only;
-- the Dryad/article carrier pays abundance/fire-response evidence separately.
------------------------------------------------------------------------

northernBrownBandicootQid : Identity.ExternalIdentityDemand
northernBrownBandicootQid = Identity.mkOptionalIdentityDemand
  "Tiwi mammal fire-response continuation" "external taxon identity"
  "northern brown bandicoot / Isoodon macrourus" Identity.wikidataQid
  (Identity.verified "Q194272" "Wikidata taxon identity checked 2026-09-10")

commonBrushtailPossumQid : Identity.ExternalIdentityDemand
commonBrushtailPossumQid = Identity.mkOptionalIdentityDemand
  "Tiwi mammal fire-response continuation" "external taxon identity"
  "common brushtail possum / Trichosurus vulpecula" Identity.wikidataQid
  (Identity.verified "Q732477" "Wikidata taxon identity checked 2026-09-10")

blackFootedTreeRatQid : Identity.ExternalIdentityDemand
blackFootedTreeRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi mammal fire-response continuation" "external taxon identity"
  "black-footed tree-rat / Mesembriomys gouldii" Identity.wikidataQid
  (Identity.verified "Q1763261" "Wikidata taxon identity checked 2026-09-10")

brushTailedRabbitRatQid : Identity.ExternalIdentityDemand
brushTailedRabbitRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi mammal fire-response continuation" "external taxon identity"
  "brush-tailed rabbit-rat / Conilurus penicillatus" Identity.wikidataQid
  (Identity.verified "Q303877" "Wikidata taxon identity checked 2026-09-10")

grasslandMelomysQid : Identity.ExternalIdentityDemand
grasslandMelomysQid = Identity.mkOptionalIdentityDemand
  "Tiwi mammal fire-response continuation" "external taxon identity"
  "grassland melomys / Melomys burtoni" Identity.wikidataQid
  (Identity.unresolved "Search located article/category surfaces but no safely verified direct taxon QID promoted in this tranche")

paleFieldRatQid : Identity.ExternalIdentityDemand
paleFieldRatQid = Identity.mkOptionalIdentityDemand
  "Tiwi mammal fire-response continuation" "external taxon identity"
  "pale field-rat / Rattus tunneyi" Identity.wikidataQid
  (Identity.unresolved "A secondary page exposed a candidate Wikidata identifier, but no direct Wikidata taxon verification was promoted in this tranche")

------------------------------------------------------------------------
-- Primary empirical carrier: Davies article + Dryad data.
------------------------------------------------------------------------

data TiwiMammalSourceRole : Set where
  experimentalFireMammalResponse
  exactPlotRelativeAbundanceDataset : TiwiMammalSourceRole

record TiwiMammalPrimarySource : Set where
  constructor tiwi-mammal-primary-source
  field
    authors : String
    title : String
    year : Nat
    identifier : String
    role : TiwiMammalSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open TiwiMammalPrimarySource public

daviesEtAl2018 : TiwiMammalPrimarySource
daviesEtAl2018 = tiwi-mammal-primary-source
  "Hugh F. Davies; Michael A. McCarthy; Willie Rioli; José Puruntatameri; Willie Roberts; Colin Kerinaiua; Vivian Kerinauia; Kim Brooks Womatakimi; Alan N. Andersen; Brett P. Murphy"
  "An experimental test of whether pyrodiversity promotes mammal diversity in a northern Australian savanna"
  2018
  "DOI 10.1111/1365-2664.13170"
  experimentalFireMammalResponse
  "Primary study of nine years of experimentally manipulated fire frequency across the 18 Tiwi Carbon Study plots, modelling species-level native-mammal abundance responses."
  "Does not imply every mammal responds to fire frequency, does not make pyrodiversity universally beneficial, and does not by itself identify vegetation mediation or carbon effects."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

daviesDryad2018 : TiwiMammalPrimarySource
daviesDryad2018 = tiwi-mammal-primary-source
  "Hugh F. Davies et al."
  "Data from: An experimental test of whether pyrodiversity promotes mammal diversity in a northern Australian savanna"
  2018
  "Dryad DOI 10.5061/dryad.4gm2r5m; file PropGLMs4.csv"
  exactPlotRelativeAbundanceDataset
  "Primary deposited dataset reports 2015 relative abundance/detection nights for named mammal taxa by experimental fire plot on Melville Island."
  "Dataset rows do not create taxon identity, causal mediation through vegetation, exact Freeman-transect identity, or whole-fauna biodiversity conclusions."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Species-level evidence cells.
------------------------------------------------------------------------

data TiwiMammalTaxon : Set where
  northernBrownBandicoot
  commonBrushtailPossum
  blackFootedTreeRat
  brushTailedRabbitRat
  grasslandMelomys
  paleFieldRat
  miceAndDunnartsAggregate : TiwiMammalTaxon

record TiwiMammalEvidenceCell : Set where
  constructor tiwi-mammal-evidence-cell
  field
    taxon : TiwiMammalTaxon
    source : TiwiMammalPrimarySource
    taxonIdentityReference : String
    exactPlotReference : String
    exactFireTreatmentReference : String
    exactMeasurementWindow : String
    responseMeasureReference : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open TiwiMammalEvidenceCell public

------------------------------------------------------------------------
-- BIDI / snowball state.
------------------------------------------------------------------------

record TiwiMammalQidAcquisitionState : Set where
  constructor tiwi-mammal-qid-acquisition-state
  field
    bandicootQidAcquired : Bool
    brushtailPossumQidAcquired : Bool
    blackFootedTreeRatQidAcquired : Bool
    brushTailedRabbitRatQidAcquired : Bool
    grasslandMelomysQidResolved : Bool
    paleFieldRatQidResolved : Bool
    DaviesArticleAcquired : Bool
    DryadDatasetAcquired : Bool
    plotRowsAcquired : Bool
    speciesColumnsAcquired : Bool
    fireTreatmentHistoryAcquired : Bool
    vegetationJoinEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open TiwiMammalQidAcquisitionState public

record TiwiMammalQidPaymentState : Set where
  constructor tiwi-mammal-qid-payment-state
  field
    taxonQidIdentityPaid : Bool
    exactPrimarySourcePaid : Bool
    sourceRoleAttributionPaid : Bool
    exactPlotIdentityPaid : Bool
    exactTaxonColumnPaid : Bool
    fireTreatmentPaid : Bool
    responseMeasurePaid : Bool
    speciesSpecificFireResponsePaid : Bool
    vegetationSamePlotJoinPaid : Bool
    vegetationMediationPaid : Bool
    assemblageAggregationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open TiwiMammalQidPaymentState public

snowballAcquisitionDoesNotAdvanceTiwiMammalPayment :
  TiwiMammalQidAcquisitionState → TiwiMammalQidPaymentState → TiwiMammalQidPaymentState
snowballAcquisitionDoesNotAdvanceTiwiMammalPayment _ payment = payment

------------------------------------------------------------------------
-- Graph follow / relation constraints.
------------------------------------------------------------------------

record TiwiMammalFireResponseWeld : Set where
  constructor tiwi-mammal-fire-response-weld
  field
    taxonCell : TiwiMammalEvidenceCell
    priorPlotJoinReference : String
    exactDryadRowPaid : Bool
    exactFreemanPlotJoinPaid : Bool
    same2015CarrierPaid : Bool
    fireFrequencyResponsePaid : Bool
    vegetationMediatorPaid : Bool
    carbonMediatorPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open TiwiMammalFireResponseWeld public

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data TaxonQidMeansObservedPopulation : Set where
data ConservationStatusMeansFireResponse : Set where
data ArticleQidMeansTaxonIdentity : Set where
data SpeciesColumnMeansWholeAssemblage : Set where
data OneSpeciesResponseMeansAllMammals : Set where
data FireResponseMeansVegetationMediation : Set where
data SamePlotSetMeansSameSamplingUnit : Set where
data IndigenousProjectContextCreatesTaxonResponse : Set where
data AcquisitionCreatesPayment : Set where

taxonQidDoesNotCreateObservedPopulation : TaxonQidMeansObservedPopulation → ⊥
taxonQidDoesNotCreateObservedPopulation ()

conservationStatusDoesNotCreateFireResponse : ConservationStatusMeansFireResponse → ⊥
conservationStatusDoesNotCreateFireResponse ()

articleQidDoesNotSubstituteForTaxonIdentity : ArticleQidMeansTaxonIdentity → ⊥
articleQidDoesNotSubstituteForTaxonIdentity ()

speciesColumnDoesNotEqualWholeAssemblage : SpeciesColumnMeansWholeAssemblage → ⊥
speciesColumnDoesNotEqualWholeAssemblage ()

oneSpeciesResponseDoesNotGeneraliseToAllMammals : OneSpeciesResponseMeansAllMammals → ⊥
oneSpeciesResponseDoesNotGeneraliseToAllMammals ()

fireResponseDoesNotCreateVegetationMediation : FireResponseMeansVegetationMediation → ⊥
fireResponseDoesNotCreateVegetationMediation ()

samePlotSetDoesNotCreateSameSamplingUnit : SamePlotSetMeansSameSamplingUnit → ⊥
samePlotSetDoesNotCreateSameSamplingUnit ()

IndigenousContextDoesNotManufactureTaxonResponse : IndigenousProjectContextCreatesTaxonResponse → ⊥
IndigenousContextDoesNotManufactureTaxonResponse ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorPlotJoinSnowball : Prior.TiwiPlotJoinAcquisitionState → Prior.TiwiPlotJoinPaymentState → Prior.TiwiPlotJoinPaymentState
priorPlotJoinSnowball = Prior.snowballAcquisitionDoesNotAdvanceTiwiPlotJoinPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary
