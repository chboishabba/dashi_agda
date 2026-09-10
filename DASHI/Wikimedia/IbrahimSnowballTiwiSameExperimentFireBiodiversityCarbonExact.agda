module DASHI.Wikimedia.IbrahimSnowballTiwiSameExperimentFireBiodiversityCarbonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.IbrahimSnowballIndigenousPyrodiversityFaunaProductivityCarbonExact as Prior

------------------------------------------------------------------------
-- TIWI SAME-EXPERIMENT FIRE / VEGETATION / FAUNA / CARBON SNOWBALL
--
-- The Tiwi Carbon Study gives a rare long-term Indigenous-land experiment in
-- which the same 18 fire-treatment plots are reused across carbon, vegetation
-- and mammal studies.  Same experiment family is stronger than cross-study
-- adjacency, but still weaker than same measurement time / exact same sample.
------------------------------------------------------------------------

data TiwiSameExperimentSourceRole : Set where
  experimentAndCarbonBaseline
  vegetationStructureFollowup
  mammalFireResponseFollowup
  longTermCarbonStockFollowup : TiwiSameExperimentSourceRole

record TiwiSameExperimentPrimarySource : Set where
  constructor tiwi-same-experiment-primary-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifier : String
    role : TiwiSameExperimentSourceRole
    exactExperimentFamily : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open TiwiSameExperimentPrimarySource public

richardsEtAl2012 : TiwiSameExperimentPrimarySource
richardsEtAl2012 = tiwi-same-experiment-primary-source
  "Anna E. Richards et al."
  "Savanna burning, greenhouse gas emissions and indigenous livelihoods: Introducing the Tiwi Carbon Study"
  "Austral Ecology 37(6):712-723"
  2012
  "DOI 10.1111/j.1442-9993.2012.02395.x"
  experimentAndCarbonBaseline
  "Tiwi Carbon Study; 18 experimental fire plots across Imalu, Taracumbi, Pickertaramoor and Shark Bay; annual early-dry-season, triennial early-dry-season and unburnt treatments"
  "Primary experiment-defining paper with plot-level carbon stocks, fire-consumed carbon pools and baseline fauna/biodiversity appendices."
  "Does not by itself identify long-term mammal response, later vegetation response, NEP/NBP, or universal Tiwi/Indigenous fire-management effects."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

freemanEtAl2018 : TiwiSameExperimentPrimarySource
freemanEtAl2018 = tiwi-same-experiment-primary-source
  "Michelle E. Freeman; Brett P. Murphy; Anna E. Richards; Peter A. Vesk; Garry D. Cook"
  "Facultative and Obligate Trees in a Mesic Savanna: Fire Effects on Savanna Structure Imply Contrasting Strategies of Eco-Taxonomic Groups"
  "Frontiers in Plant Science 9:644"
  2018
  "DOI 10.3389/fpls.2018.00644"
  vegetationStructureFollowup
  "Tiwi Carbon Study experimental fire areas on western Melville Island"
  "Primary vegetation follow-up using the Tiwi Carbon Study fire-treatment areas to quantify tree size-class and structural responses to contrasting fire frequencies."
  "Vegetation-structure response is not whole biodiversity, fauna response, productivity or carbon balance; measurement dates must not be silently aligned with other follow-ups."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

daviesEtAl2018 : TiwiSameExperimentPrimarySource
daviesEtAl2018 = tiwi-same-experiment-primary-source
  "Hugh F. Davies; Michael A. McCarthy; Willie Rioli; José Puruntatameri; Willie Roberts; Colin Kerinaiua; Vivian Kerinauia; Kim Brooks Womatakimi; Alan N. Andersen; Brett P. Murphy"
  "An experimental test of whether pyrodiversity promotes mammal diversity in a northern Australian savanna"
  "Journal of Applied Ecology 55(5):2124-2134"
  2018
  "DOI 10.1111/1365-2664.13170; Dryad 10.5061/dryad.4gm2r5m"
  mammalFireResponseFollowup
  "Same 18 Tiwi Carbon Study experimental fire plots; 50-100 ha; four western Melville Island locations"
  "Primary nine-year mammal follow-up using all 18 experimental fire plots; evaluates abundance/diversity responses to manipulated fire frequency."
  "Does not establish a generic pyrodiversity-benefit law, whole-fauna response, vegetation-carbon effect, or same-year identity with carbon/vegetation measurements."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

ngEtAl2026 : TiwiSameExperimentPrimarySource
ngEtAl2026 = tiwi-same-experiment-primary-source
  "Ee Ling Ng; Jacqueline R. England; Keryn I. Paul; Melissa Piper; Anna E. Richards; Robyn A. Cowley; Rodd M. Dyer; Jon Schatz; David I. Forrester"
  "Effects of fire management on biomass and debris carbon stocks in Australia's northern savannas: results from long-term trials"
  "International Journal of Wildland Fire 35:WF26061"
  2026
  "DOI 10.1071/WF26061"
  longTermCarbonStockFollowup
  "Northern-Australian long-term fire-trial analysis including Tiwi Carbon Study sites Imalu, Pickertaramoor, Shark Bay and Taracumbi"
  "Primary long-term field analysis of above-/below-ground woody biomass C, standing-dead C, coarse woody debris C and litter C under contrasting fire regimes, including Tiwi trial sites after 17-18 years."
  "Multi-site carbon analysis does not by itself provide plot-matched mammal/vegetation values, NEP/NBP, soil-C response or a universal carbon benefit from any one fire prescription."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Exact levels of identity.  These must not be collapsed.
------------------------------------------------------------------------

data SameCarrierStrength : Set where
  sameProgramme
  sameExperimentFamily
  samePlotSet
  sameExactPlot
  sameMeasurementWindow
  sameSample : SameCarrierStrength

record TiwiExperimentFamilyReceipt : Set where
  constructor tiwi-experiment-family-receipt
  field
    experimentReference : String
    plotCountReference : String
    locationsReference : String
    treatmentReference : String
    IndigenousLandContextReference : String
    TiwiLandRangerOrLandCouncilRoleReference : String
    carbonSource : TiwiSameExperimentPrimarySource
    vegetationSource : TiwiSameExperimentPrimarySource
    mammalSource : TiwiSameExperimentPrimarySource
    longTermCarbonSource : TiwiSameExperimentPrimarySource
    carbonVegetationSameExperimentFamily : Bool
    carbonMammalSameExperimentFamily : Bool
    vegetationMammalSameExperimentFamily : Bool
    allConsumersSameMeasurementWindow : Bool
    allConsumersSameExactSample : Bool
    sourceOwnersRemainExternal : Bool
    dashiCrosswalkOwner : Attribution.ClaimOwner
    dashiOwnsCrosswalkOnly : dashiCrosswalkOwner ≡ Attribution.dashiFormalisationOwner

open TiwiExperimentFamilyReceipt public

canonicalTiwiExperimentFamilyReceipt : TiwiExperimentFamilyReceipt
canonicalTiwiExperimentFamilyReceipt = tiwi-experiment-family-receipt
  "Tiwi Carbon Study long-term experimental fire network"
  "18 experimental plots, each approximately 50-100 ha"
  "Imalu; Taracumbi; Pickertaramoor; Shark Bay, western Melville Island"
  "annual early-dry-season burn; triennial early-dry-season burn; unburnt/long-unburnt treatment"
  "Tiwi Islands / Melville Island Indigenous land-management context"
  "Tiwi Land Council / Tiwi Land Rangers participation and maintenance must be retained from exact source acknowledgements/project records"
  richardsEtAl2012 freemanEtAl2018 daviesEtAl2018 ngEtAl2026
  true true true false false true
  Attribution.dashiFormalisationOwner refl

------------------------------------------------------------------------
-- Consumer-specific same-object payment.
------------------------------------------------------------------------

data TiwiCrossConsumer : Set where
  fireTreatment
  woodyVegetationStructure
  nativeMammalAssemblage
  aboveGroundBiomassCarbon
  belowGroundBiomassCarbon
  standingDeadCarbon
  coarseWoodyDebrisCarbon
  litterCarbon
  wholeEcosystemCarbon
  soilCarbon
  grossPrimaryProduction
  netEcosystemProductivity
  netBiomeProductivity : TiwiCrossConsumer

record TiwiCrossConsumerAdmission : Set where
  constructor tiwi-cross-consumer-admission
  field
    source : TiwiSameExperimentPrimarySource
    consumer : TiwiCrossConsumer
    exactLocation : String
    exactPlotOrPlotSet : String
    exactFireTreatment : String
    measurementDateOrWindow : String
    measurementMethod : String
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternal : sourceOwner ≡ Attribution.externalSourceOwner

open TiwiCrossConsumerAdmission public

record TiwiSamePlotCrossConsumerWeld : Set where
  constructor tiwi-same-plot-cross-consumer-weld
  field
    fireAdmission : TiwiCrossConsumerAdmission
    vegetationAdmission : TiwiCrossConsumerAdmission
    faunaAdmission : TiwiCrossConsumerAdmission
    carbonAdmission : TiwiCrossConsumerAdmission
    sameExperimentFamilyPaid : Bool
    samePlotSetPaid : Bool
    sameExactPlotPaid : Bool
    sameMeasurementWindowPaid : Bool
    treatmentHistoryAlignmentPaid : Bool
    sameSiteCovariatesPaid : Bool
    ecologicalCrossConsumerModelPaid : Bool
    carbonCrossConsumerModelPaid : Bool
    causalInteractionPaid : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsCompositionInference : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open TiwiSamePlotCrossConsumerWeld public

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record TiwiSameExperimentAcquisitionState : Set where
  constructor tiwi-same-experiment-acquisition-state
  field
    RichardsExperimentSourceAcquired : Bool
    FreemanVegetationSourceAcquired : Bool
    DaviesMammalSourceAcquired : Bool
    NgLongTermCarbonSourceAcquired : Bool
    plotNetworkIdentityAcquired : Bool
    fireTreatmentHistoryAcquired : Bool
    carbonStocksAcquired : Bool
    vegetationStructureAcquired : Bool
    mammalResponseAcquired : Bool
    exactPlotLevelJoinKeysAcquired : Bool
    exactMeasurementWindowsAcquired : Bool
    siteCovariatesAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open TiwiSameExperimentAcquisitionState public

record TiwiSameExperimentPaymentState : Set where
  constructor tiwi-same-experiment-payment-state
  field
    exactPrimarySourcesPaid : Bool
    sourceAttributionPaid : Bool
    experimentFamilyIdentityPaid : Bool
    IndigenousProjectContextPaid : Bool
    exactTreatmentDefinitionsPaid : Bool
    samePlotSetPaid : Bool
    sameExactPlotPaid : Bool
    sameMeasurementWindowPaid : Bool
    vegetationConsumerPaid : Bool
    mammalConsumerPaid : Bool
    carbonConsumerPaid : Bool
    productivityConsumerPaid : Bool
    sameSiteCrossConsumerPaid : Bool
    causalInteractionPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open TiwiSameExperimentPaymentState public

snowballAcquisitionDoesNotAdvanceTiwiSameExperimentPayment :
  TiwiSameExperimentAcquisitionState → TiwiSameExperimentPaymentState → TiwiSameExperimentPaymentState
snowballAcquisitionDoesNotAdvanceTiwiSameExperimentPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / no-promotion barriers.
------------------------------------------------------------------------

data SameExperimentFamilyMeansSameMeasurementTime : Set where
data SamePlotSetMeansSameExactPlot : Set where
data CarbonStockMeansProductivity : Set where
data VegetationResponseMeansMammalResponse : Set where
data MammalDiversityMeansWholeBiodiversity : Set where
data ExperimentalFireEffectMeansCustodialAuthority : Set where
data IndigenousProjectContextMeansUniversalIndigenousEffect : Set where
data CrossConsumerAssociationMeansCausalMediation : Set where
data LaterCarbonFollowupRetroactivelyPaysEarlierSameTime : Set where
data AcquisitionCreatesPayment : Set where

sameExperimentFamilyDoesNotMeanSameMeasurementTime : SameExperimentFamilyMeansSameMeasurementTime → ⊥
sameExperimentFamilyDoesNotMeanSameMeasurementTime ()

samePlotSetDoesNotMeanSameExactPlot : SamePlotSetMeansSameExactPlot → ⊥
samePlotSetDoesNotMeanSameExactPlot ()

carbonStockDoesNotMeanProductivity : CarbonStockMeansProductivity → ⊥
carbonStockDoesNotMeanProductivity ()

vegetationResponseDoesNotMeanMammalResponse : VegetationResponseMeansMammalResponse → ⊥
vegetationResponseDoesNotMeanMammalResponse ()

mammalDiversityDoesNotExhaustBiodiversity : MammalDiversityMeansWholeBiodiversity → ⊥
mammalDiversityDoesNotExhaustBiodiversity ()

experimentalEffectDoesNotCreateCustodialAuthority : ExperimentalFireEffectMeansCustodialAuthority → ⊥
experimentalEffectDoesNotCreateCustodialAuthority ()

IndigenousProjectContextDoesNotCreateUniversalEffect : IndigenousProjectContextMeansUniversalIndigenousEffect → ⊥
IndigenousProjectContextDoesNotCreateUniversalEffect ()

crossConsumerAssociationDoesNotCreateCausalMediation : CrossConsumerAssociationMeansCausalMediation → ⊥
crossConsumerAssociationDoesNotCreateCausalMediation ()

laterCarbonDoesNotRetroactivelyCreateSameTime : LaterCarbonFollowupRetroactivelyPaysEarlierSameTime → ⊥
laterCarbonDoesNotRetroactivelyCreateSameTime ()

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

priorPyroBoundary : Prior.IndigenousPyroAcquisitionState → Prior.IndigenousPyroPaymentState → Prior.IndigenousPyroPaymentState
priorPyroBoundary = Prior.snowballAcquisitionDoesNotAdvanceIndigenousPyroPayment

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary
