module DASHI.Environment.PlasmaActivatedWaterSameObjectSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.PlasmaActivatedWaterSameObjectPrimarySourceExact as Primary
import DASHI.Environment.PlasmaActivatedWaterAquaticNutrientBridgeExact as PAW
import DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact as Nitrogen
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC

------------------------------------------------------------------------
-- SAME-OBJECT PAW SNOWBALL
--
-- The primary paper can carry one experiment across reactor -> chemistry ->
-- application -> plant response.  Snowball acquisition may retain every later
-- observation immediately, but payment advances only through exact identity
-- gates.  Isotopic N recovery / instantaneous root flux remain stronger gates.
------------------------------------------------------------------------

record SameObjectPAWAdmission
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (application : PAW.PlasmaWaterApplication composition) : Set₁ where
  constructor same-object-paw-admission
  field
    source : Primary.PAWSameObjectPrimarySource
    sourceIsCanonicalKizerStudy :
      source ≡ Primary.kizerArabidopsisPAW2025
    exactReactorReference : String
    exactProductionBatchReference : String
    exactPowerReference : String
    exactTreatmentDurationReference : String
    exactFeedGasReference : String
    exactWaterVolumeReference : String
    exactFinalChemistryReference : String
    nitrateReference : String
    nitriteReference : String
    peroxideReference : String
    ammoniumReference : String
    neutralisationReference : String
    storageReference : String
    applicationUsesDeclaredPAWReference : String
    nitrateMatchedComparatorReference : String
    rootResponseReference : String
    transcriptomicNResponseReference : String
    fiveWeekPlantOutcomeReference : String
    sourceClaimOwner : Attribution.ClaimOwner
    sourceRemainsExternal :
      sourceClaimOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsSameObjectWeld :
      dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open SameObjectPAWAdmission public

record SameObjectPAWNitrogenWeld
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    {application : PAW.PlasmaWaterApplication composition}
    (admission : SameObjectPAWAdmission application)
    (nitrogenInput : PAW.PlasmaNitrogenInputReceipt composition)
    (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor same-object-paw-nitrogen-weld
  field
    productionMatchesNitrogenLedgerReference : String
    chemistryMatchesNitrogenLedgerReference : String
    applicationMatchesNitrogenLedgerReference : String
    sameBatchAcrossChemistryAndApplicationReference : String
    sameTemporalBoundaryReference : String
    sameRootZoneOrDeclaredApplicationBoundaryReference : String
    spacRootUptakeSocketReference : String
    nitrogenInputToRootZoneReference : String
    rootResponseToSPACConsumerReference : String
    conservationReference : String
    exactPAWPacketReference : String
    packetCompilationReference : String
    growthOutcomeIsNotNUptakeMeasurement : Bool
    transcriptomicResponseIsNotFluxMeasurement : Bool

open SameObjectPAWNitrogenWeld public

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record SameObjectPAWAcquisitionState : Set where
  constructor same-object-paw-acquisition-state
  field
    primaryPublicationAcquired : Bool
    reactorParametersAcquired : Bool
    powerAcquired : Bool
    treatmentDurationAcquired : Bool
    finalChemistryAcquired : Bool
    batchIdentityAcquired : Bool
    applicationProtocolAcquired : Bool
    nitrateComparatorAcquired : Bool
    rootResponseAcquired : Bool
    transcriptomeAcquired : Bool
    fiveWeekOutcomeAcquired : Bool
    isotopeRecoveryEvidenceAcquired : Bool
    directRootFluxEvidenceAcquired : Bool
    fieldTransportEvidenceAcquired : Bool
    lifecycleEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open SameObjectPAWAcquisitionState public

record SameObjectPAWPaymentState : Set where
  constructor same-object-paw-payment-state
  field
    sourceIdentityPaid : Bool
    reactorIdentityPaid : Bool
    powerAndDurationPaid : Bool
    exactProductionBatchPaid : Bool
    finalChemistryPaid : Bool
    sameBatchChemistryApplicationPaid : Bool
    nitrogenLedgerPaid : Bool
    nitrateComparatorPaid : Bool
    rootResponseIdentityPaid : Bool
    transcriptomicResponsePaid : Bool
    fiveWeekOutcomePaid : Bool
    isotopicNitrogenRecoveryPaid : Bool
    instantaneousRootFluxPaid : Bool
    spacSameObjectPaid : Bool
    fieldTransportPaid : Bool
    lifecyclePaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open SameObjectPAWPaymentState public

snowballAcquisitionDoesNotAdvanceSameObjectPAWPayment :
  SameObjectPAWAcquisitionState →
  SameObjectPAWPaymentState →
  SameObjectPAWPaymentState
snowballAcquisitionDoesNotAdvanceSameObjectPAWPayment _ payment = payment

------------------------------------------------------------------------
-- Strong residuals: the same-study carrier is broad, but does not manufacture
-- measurement modalities it did not perform.
------------------------------------------------------------------------

data GrowthMeansIsotopicRecoveryPermission : Set where
data TranscriptomeMeansRootFluxPermission : Set where
data SamePublicationMeansSameBatchPermission : Set where
data SameBatchMeansFieldTransportPermission : Set where
data SameObjectCarrierMeansRecommendationPermission : Set where
data ExternalSourceOwnsDashiWeldPermission : Set where

growthDoesNotPayIsotopicRecovery : GrowthMeansIsotopicRecoveryPermission → ⊥
growthDoesNotPayIsotopicRecovery ()

transcriptomeDoesNotPayRootFlux : TranscriptomeMeansRootFluxPermission → ⊥
transcriptomeDoesNotPayRootFlux ()

samePublicationDoesNotByItselfProveSameBatch :
  SamePublicationMeansSameBatchPermission → ⊥
samePublicationDoesNotByItselfProveSameBatch ()

sameBatchDoesNotPayFieldTransport : SameBatchMeansFieldTransportPermission → ⊥
sameBatchDoesNotPayFieldTransport ()

sameObjectCarrierDoesNotPayRecommendation :
  SameObjectCarrierMeansRecommendationPermission → ⊥
sameObjectCarrierDoesNotPayRecommendation ()

externalSourceDoesNotOwnDashiSameObjectWeld :
  ExternalSourceOwnsDashiWeldPermission → ⊥
externalSourceDoesNotOwnDashiSameObjectWeld ()

record SameObjectPAWBoundary : Set where
  constructor same-object-paw-boundary
  field
    publicationCarrierAndBatchIdentityRemainDistinct : Bool
    productionChemistryApplicationAndOutcomeRemainTyped : Bool
    growthTranscriptomeIsotopeRecoveryAndFluxRemainDistinct : Bool
    primarySourceAndDashiWeldRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    sameStudyAutomaticallyPaysFieldTransport : Bool
    sameStudyAutomaticallyPaysRecommendation : Bool

canonicalSameObjectPAWBoundary : SameObjectPAWBoundary
canonicalSameObjectPAWBoundary =
  same-object-paw-boundary true true true true true false false
