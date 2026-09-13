module DASHI.Wikimedia.IbrahimSnowballTiwiPlotJoinTemporalQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballTiwiSameExperimentFireBiodiversityCarbonExact as Prior

------------------------------------------------------------------------
-- TIWI PLOT-JOIN / TEMPORAL ALIGNMENT / QID SNOWBALL
--
-- QIDs below are external identity/navigation coordinates only.  Exact plot
-- identity, measurement timing and ecological/carbon effects remain source-paid.
------------------------------------------------------------------------

tiwiPeopleQid : Identity.ExternalIdentityDemand
tiwiPeopleQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-experiment plot join" "external people identity"
  "Tiwi people" Identity.wikidataQid
  (Identity.verified "Q2933374" "Wikidata Tiwi people identity checked 2026-09-10")

tiwiIslandsQid : Identity.ExternalIdentityDemand
tiwiIslandsQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-experiment plot join" "external place identity"
  "Tiwi Islands" Identity.wikidataQid
  (Identity.verified "Q1323908" "Wikidata Tiwi Islands identity checked 2026-09-10")

melvilleIslandQid : Identity.ExternalIdentityDemand
melvilleIslandQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-experiment plot join" "external place identity"
  "Melville Island / Yermalner" Identity.wikidataQid
  (Identity.verified "Q504763" "Wikidata Melville Island identity checked 2026-09-10")

tiwiLandCouncilQid : Identity.ExternalIdentityDemand
tiwiLandCouncilQid = Identity.mkOptionalIdentityDemand
  "Tiwi same-experiment plot join" "external organisation identity"
  "Tiwi Land Council" Identity.wikidataQid
  (Identity.unresolved "No safely verified Tiwi Land Council QID promoted in this tranche")

------------------------------------------------------------------------
-- Primary sources / datasets that expose progressively stronger join keys.
------------------------------------------------------------------------

data TiwiJoinSourceRole : Set where
  experimentDefinitionAnd2009Baseline
  vegetation2015SameTreatmentSites
  mammal2015ExactPlotDataset
  longTermCarbonFollowup : TiwiJoinSourceRole

record TiwiJoinPrimarySource : Set where
  constructor tiwi-join-primary-source
  field
    authors : String
    title : String
    year : Nat
    identifier : String
    role : TiwiJoinSourceRole
    joinContribution : String
    temporalBoundary : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open TiwiJoinPrimarySource public

richards2012 : TiwiJoinPrimarySource
richards2012 = tiwi-join-primary-source
  "Anna E. Richards et al."
  "Savanna burning, greenhouse gas emissions and indigenous livelihoods: Introducing the Tiwi Carbon Study"
  2012
  "DOI 10.1111/j.1442-9993.2012.02395.x"
  experimentDefinitionAnd2009Baseline
  "Defines Tiwi Carbon Study fire experiment; appendices provide 2009/2010 total carbon stocks and 2009 bird/frog/reptile/mammal/ant/termite observations by fire plot."
  "2009-2010 baseline / early experiment period"
  "Does not make later 2015 vegetation or mammal measurements contemporaneous with 2009/2010 carbon measurements."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

freeman2018 : TiwiJoinPrimarySource
freeman2018 = tiwi-join-primary-source
  "Michelle E. Freeman; Brett P. Murphy; Anna E. Richards; Peter A. Vesk; Garry D. Cook"
  "Facultative and Obligate Trees in a Mesic Savanna: Fire Effects on Savanna Structure Imply Contrasting Strategies of Eco-Taxonomic Groups"
  2018
  "DOI 10.3389/fpls.2018.00644"
  vegetation2015SameTreatmentSites
  "Uses Tiwi Carbon Study fire-treatment sites; records 18 sites across Imalu, Taracumbi, Pikertaramoor and Shark Bay and measures woody vegetation in May 2015."
  "May 2015, immediately before planned 2015 burns"
  "Same treatment network does not by itself prove exact row-for-row identity with mammal or later carbon observations."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

daviesDryad2018 : TiwiJoinPrimarySource
daviesDryad2018 = tiwi-join-primary-source
  "Hugh F. Davies; Michael A. McCarthy; Willie Rioli; José Puruntatameri; Willie Roberts; Colin Kerinaiua; Vivian Kerinauia; Kim Brooks Womatakimi; Alan N. Andersen; Brett P. Murphy"
  "Data from: An experimental test of whether pyrodiversity promotes mammal diversity in a northern Australian savanna"
  2018
  "Dryad DOI 10.5061/dryad.4gm2r5m; article DOI 10.1111/1365-2664.13170"
  mammal2015ExactPlotDataset
  "Dryad exposes mammal relative-abundance data by experimental fire plot; source states measurements are from Melville Island experimental plots in 2015."
  "2015 mammal monitoring"
  "Dataset-level plot labels do not automatically identify Freeman transects or Richards carbon rows without explicit join-key reconciliation."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

ng2026 : TiwiJoinPrimarySource
ng2026 = tiwi-join-primary-source
  "Ee Ling Ng; Jacqueline R. England; Keryn I. Paul; Melissa Piper; Anna E. Richards; Robyn A. Cowley; Rodd M. Dyer; Jon Schatz; David I. Forrester"
  "Effects of fire management on biomass and debris carbon stocks in Australia's northern savannas: results from long-term trials"
  2026
  "DOI 10.1071/WF26061"
  longTermCarbonFollowup
  "Includes Tiwi long-term fire-trial locations and measures woody/debris/litter carbon after 17-18 years of contrasting fire management."
  "long-term follow-up, not contemporaneous with 2009 or 2015 observations"
  "Multi-site long-term carbon results do not retroactively pay exact same-plot or same-time joins with earlier vegetation/fauna measurements."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Join-key hierarchy.
------------------------------------------------------------------------

data TiwiJoinAxis : Set where
  programmeAxis locationAxis treatmentAxis plotSetAxis exactPlotAxis transectAxis
  sampleAxis measurementWindowAxis fireHistoryAxis covariateAxis : TiwiJoinAxis

record TiwiJoinReceipt : Set where
  constructor tiwi-join-receipt
  field
    leftSource : TiwiJoinPrimarySource
    rightSource : TiwiJoinPrimarySource
    sameProgrammePaid : Bool
    sameLocationVocabularyPaid : Bool
    sameTreatmentVocabularyPaid : Bool
    samePlotSetPaid : Bool
    sameExactPlotPaid : Bool
    sameTransectOrSamplingUnitPaid : Bool
    sameMeasurementWindowPaid : Bool
    fireHistoryAlignmentPaid : Bool
    exactJoinKeyReference : String
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsJoinInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open TiwiJoinReceipt public

freemanDavies2015JoinFrontier : TiwiJoinReceipt
freemanDavies2015JoinFrontier = tiwi-join-receipt
  freeman2018 daviesDryad2018
  true true true true false false true true
  "Both source families use the 18 Tiwi Carbon Study plots and 2015 observations; exact plot/transect row-key reconciliation remains an explicit unpaid gate."
  Attribution.dashiInferenceOwner refl

richardsFreemanTemporalFrontier : TiwiJoinReceipt
richardsFreemanTemporalFrontier = tiwi-join-receipt
  richards2012 freeman2018
  true true true true false false false true
  "Richards appendices expose plot-level 2009/2010 carbon/biodiversity; Freeman measures the treatment sites in May 2015. Same experiment family survives, same measurement window does not."
  Attribution.dashiInferenceOwner refl

record TiwiPlotJoinAcquisitionState : Set where
  constructor tiwi-plot-join-acquisition-state
  field
    tiwiPeopleQidAcquired : Bool
    tiwiIslandsQidAcquired : Bool
    melvilleIslandQidAcquired : Bool
    tiwiLandCouncilQidResolved : Bool
    richardsAppendicesAcquired : Bool
    freemanSiteTableAcquired : Bool
    daviesDryadAcquired : Bool
    ngLongTermCarbonAcquired : Bool
    locationLabelsAcquired : Bool
    treatmentLabelsAcquired : Bool
    exactPlotLabelsAcquired : Bool
    measurementDatesAcquired : Bool
    fireHistoryAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open TiwiPlotJoinAcquisitionState public

record TiwiPlotJoinPaymentState : Set where
  constructor tiwi-plot-join-payment-state
  field
    qidIdentityPaid : Bool
    exactPrimarySourcesPaid : Bool
    sourceRoleAttributionPaid : Bool
    sameProgrammePaid : Bool
    sameLocationVocabularyPaid : Bool
    sameTreatmentVocabularyPaid : Bool
    samePlotSetPaid : Bool
    sameExactPlotPaid : Bool
    sameSamplingUnitPaid : Bool
    sameMeasurementWindowPaid : Bool
    fireHistoryAlignmentPaid : Bool
    crossConsumerJoinPaid : Bool
    causalMediationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open TiwiPlotJoinPaymentState public

snowballAcquisitionDoesNotAdvanceTiwiPlotJoinPayment :
  TiwiPlotJoinAcquisitionState → TiwiPlotJoinPaymentState → TiwiPlotJoinPaymentState
snowballAcquisitionDoesNotAdvanceTiwiPlotJoinPayment _ payment = payment

------------------------------------------------------------------------
-- Attribution/QID/same-object firewalls.
------------------------------------------------------------------------

data QidMeansCountryAuthority : Set where
data PlaceQidMeansExactExperimentalPlot : Set where
data SameYearMeansSameMeasurementWindow : Set where
data SamePlotSetMeansSameSamplingUnit : Set where
data DryadRowMeansFreemanTransect : Set where
data SameExperimentMeansSameTime : Set where
data SourceAuthorMeansTiwiCustodialAuthority : Set where
data ProjectAcknowledgementMeansAuthorship : Set where
data AcquisitionMeansPayment : Set where

qidDoesNotCreateCountryAuthority : QidMeansCountryAuthority → ⊥
qidDoesNotCreateCountryAuthority ()

placeQidDoesNotIdentifyExperimentalPlot : PlaceQidMeansExactExperimentalPlot → ⊥
placeQidDoesNotIdentifyExperimentalPlot ()

sameYearDoesNotGuaranteeSameWindow : SameYearMeansSameMeasurementWindow → ⊥
sameYearDoesNotGuaranteeSameWindow ()

samePlotSetDoesNotGuaranteeSameSamplingUnit : SamePlotSetMeansSameSamplingUnit → ⊥
samePlotSetDoesNotGuaranteeSameSamplingUnit ()

dryadRowDoesNotIdentifyFreemanTransect : DryadRowMeansFreemanTransect → ⊥
dryadRowDoesNotIdentifyFreemanTransect ()

sameExperimentDoesNotMeanSameTime : SameExperimentMeansSameTime → ⊥
sameExperimentDoesNotMeanSameTime ()

sourceAuthorDoesNotCreateCustodialAuthority : SourceAuthorMeansTiwiCustodialAuthority → ⊥
sourceAuthorDoesNotCreateCustodialAuthority ()

acknowledgementDoesNotCreateAuthorship : ProjectAcknowledgementMeansAuthorship → ⊥
acknowledgementDoesNotCreateAuthorship ()

acquisitionDoesNotCreatePayment : AcquisitionMeansPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorTiwiSnowball : Prior.TiwiSameExperimentAcquisitionState → Prior.TiwiSameExperimentPaymentState → Prior.TiwiSameExperimentPaymentState
priorTiwiSnowball = Prior.snowballAcquisitionDoesNotAdvanceTiwiSameExperimentPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary
