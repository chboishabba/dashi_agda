module DASHI.Environment.PlasmaActivatedWaterNitrogenSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.PlasmaActivatedWaterPrimaryPlantNitrogenSourceExact as Primary
import DASHI.Environment.PlasmaActivatedWaterAquaticNutrientBridgeExact as PAW
import DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact as Nitrogen
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.NitrogenPathwayLESCausalTransitionBridgeExact as NitrogenLES

------------------------------------------------------------------------
-- PAW NITROGEN SNOWBALL
--
-- plasma production -> measured composition -> measured N input ->
-- hydroponic nitrate-source comparator -> bounded root-N uptake mechanism ->
-- SPAC/root-zone transport -> plant trajectory -> causal outcome.
--
-- Acquisition order is opportunistic; payment order is exact and receipt-bound.
-- External studies own only their reported experiments. DASHI owns these welds.
------------------------------------------------------------------------

record PAWHydroponicNitrateComparatorAdmission
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition) : Set₁ where
  constructor paw-hydroponic-nitrate-comparator-admission
  field
    source : Primary.PAWPlantPrimarySource
    sourceIsCanonicalLettuceStudy :
      source ≡ Primary.ruamrungsriHydroponicLettuce2023
    exactPAWProductionReference : String
    exactPAWCompositionReference : String
    exactPlasmaNitrateReference : String
    exactCommercialNitrateComparatorReference : String
    exactNoNitrateComparatorReference : String
    nutrientSolutionIdentityReference : String
    lettuceCultivarAndGrowthSystemReference : String
    nitrateDoseMatchReference : String
    measuredGrowthOutcomeReference : String
    measuredRootOutcomeReference : String
    measuredNutritionalQualityReference : String
    pawLedgerMatchesExperimentalNitrateReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsWeld :
      dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open PAWHydroponicNitrateComparatorAdmission public

record PAWRootNitrogenMechanismAdmission
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (application : PAW.PlasmaWaterApplication composition) : Set₁ where
  constructor paw-root-nitrogen-mechanism-admission
  field
    source : Primary.PAWPlantPrimarySource
    sourceIsCanonicalRootStudy :
      source ≡ Primary.panjaRootNitrogen2026
    exactReactorAndPAWReference : String
    exactPAWFractionReference : String
    exactBrassicaRootReference : String
    exactPhytofluidicGeometryReference : String
    nitrateNitriteChemistryReference : String
    nitrogenUptakeKineticsReference : String
    inwardFluxReference : String
    rootLengthReference : String
    corticalCellReference : String
    oxidativeStressReference : String
    nonMonotoneDoseResponseReference : String
    applicationMatchesDeclaredPAWReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsWeld :
      dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open PAWRootNitrogenMechanismAdmission public

------------------------------------------------------------------------
-- Same-object weld to common N packet and existing SPAC transition.
------------------------------------------------------------------------

record PAWNitrogenPacketSPACWeld
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition)
    (packetAdapter : Nitrogen.PAWComparisonAdapter pawNitrogen)
    (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor paw-nitrogen-packet-spac-weld
  field
    compiledPacket : Nitrogen.NitrogenDeliveryPacket
    packetIsCanonicalPAWCompilation :
      compiledPacket ≡ Nitrogen.compilePAWPacket pawNitrogen packetAdapter
    sameProductionReference : String
    sameCompositionReference : String
    sameNitrogenMassReference : String
    sameApplicationBoundaryReference : String
    sameSiteHistoryReference : String
    sameTemporalBoundaryReference : String
    spacRootUptakeSocketReference : String
    pawToRootZoneTransportReference : String
    rootZoneToUptakeReference : String
    crossDomainConservationReference : String
    uncertaintyReference : String

open PAWNitrogenPacketSPACWeld public

record PAWNitrogenTransitionCalibration
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    {pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition}
    {packetAdapter : Nitrogen.PAWComparisonAdapter pawNitrogen}
    {spac : SPAC.SPACDomainRealization}
    (weld : PAWNitrogenPacketSPACWeld pawNitrogen packetAdapter spac)
    (transition : NitrogenLES.NitrogenSPACTransitionWeld) : Set₁ where
  constructor paw-nitrogen-transition-calibration
  field
    transitionPacketMatchesCompiledPAWReference : String
    transitionSPACMatchesReference : String
    deliveredNToRootZoneReference : String
    uptakeMeasurementOrModelReference : String
    primaryMechanismAdmissionReference : String
    primaryHydroponicComparatorReference : String
    outcomeEvidenceReference : String
    sourceCalibrationDoesNotReplaceTransitionModel : Bool
    rootMechanismDoesNotPayAllocationOrYield : Bool

open PAWNitrogenTransitionCalibration public

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record PAWNitrogenAcquisitionState : Set where
  constructor paw-nitrogen-acquisition-state
  field
    productionIdentityAcquired : Bool
    compositionMeasurementAcquired : Bool
    nitrogenLedgerAcquired : Bool
    energyMeasurementAcquired : Bool
    hydroponicComparatorAcquired : Bool
    rootMechanismStudyAcquired : Bool
    rootZoneTransportEvidenceAcquired : Bool
    spacRealisationAcquired : Bool
    plantOutcomeEvidenceAcquired : Bool
    safetyCompatibilityEvidenceAcquired : Bool
    causalDesignEvidenceAcquired : Bool
    replicationTransportEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open PAWNitrogenAcquisitionState public

record PAWNitrogenPaymentState : Set where
  constructor paw-nitrogen-payment-state
  field
    productionIdentityPaid : Bool
    measuredCompositionPaid : Bool
    nitrogenMassPaid : Bool
    externalEnergyBoundaryPaid : Bool
    hydroponicComparatorIdentityPaid : Bool
    plasmaNitrateDoseMatchPaid : Bool
    rootMechanismIdentityPaid : Bool
    rootUptakeSemanticsPaid : Bool
    rootZoneTransportPaid : Bool
    spacSameObjectPaid : Bool
    uptakeToAllocationPaid : Bool
    plantOutcomePaid : Bool
    aquaticOrRootSafetyPaid : Bool
    causalIdentificationPaid : Bool
    replicationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open PAWNitrogenPaymentState public

snowballAcquisitionDoesNotAdvancePAWNitrogenPayment :
  PAWNitrogenAcquisitionState →
  PAWNitrogenPaymentState →
  PAWNitrogenPaymentState
snowballAcquisitionDoesNotAdvancePAWNitrogenPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / attribution barriers.
------------------------------------------------------------------------

data PlasmaNitrateComparatorMeansSamePAWPermission : Set where
data PAWRootMechanismMeansFieldTransportPermission : Set where
data PAWRootMechanismMeansSeasonUptakePermission : Set where
data TwentyPercentPAWMeansUniversalOptimumPermission : Set where
data PAWNitrogenMeansCompleteNutritionPermission : Set where
data PAWPlantEvidenceMeansAquacultureSafetyPermission : Set where
data ExternalStudyOwnsDashiPAWWeldPermission : Set where
data AcquisitionMeansPAWPaymentPermission : Set where

plasmaNitrateComparatorDoesNotIdentifyAllPAW :
  PlasmaNitrateComparatorMeansSamePAWPermission → ⊥
plasmaNitrateComparatorDoesNotIdentifyAllPAW ()

pawRootMechanismDoesNotPayFieldTransport :
  PAWRootMechanismMeansFieldTransportPermission → ⊥
pawRootMechanismDoesNotPayFieldTransport ()

pawRootMechanismDoesNotPaySeasonUptake :
  PAWRootMechanismMeansSeasonUptakePermission → ⊥
pawRootMechanismDoesNotPaySeasonUptake ()

twentyPercentPAWDoesNotBecomeUniversalOptimum :
  TwentyPercentPAWMeansUniversalOptimumPermission → ⊥
twentyPercentPAWDoesNotBecomeUniversalOptimum ()

pawNitrogenDoesNotDefinitionallyMeanCompleteNutrition :
  PAWNitrogenMeansCompleteNutritionPermission → ⊥
pawNitrogenDoesNotDefinitionallyMeanCompleteNutrition ()

pawPlantEvidenceDoesNotPayAquacultureSafety :
  PAWPlantEvidenceMeansAquacultureSafetyPermission → ⊥
pawPlantEvidenceDoesNotPayAquacultureSafety ()

externalStudyDoesNotOwnDashiPAWWeld :
  ExternalStudyOwnsDashiPAWWeldPermission → ⊥
externalStudyDoesNotOwnDashiPAWWeld ()

acquisitionDoesNotManufacturePAWPayment :
  AcquisitionMeansPAWPaymentPermission → ⊥
acquisitionDoesNotManufacturePAWPayment ()

record PAWNitrogenSnowballBoundary : Set where
  constructor paw-nitrogen-snowball-boundary
  field
    productionCompositionInputUptakeAndOutcomeRemainDistinct : Bool
    primarySourceAndDashiWeldRemainDistinct : Bool
    hydroponicComparatorAndRootMechanismRemainDistinct : Bool
    rootMechanismAndFieldTransportRemainDistinct : Bool
    plantEvidenceAndAquaticSafetyRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    pawLabelAutomaticallyPaysFertiliserRecommendation : Bool

canonicalPAWNitrogenSnowballBoundary : PAWNitrogenSnowballBoundary
canonicalPAWNitrogenSnowballBoundary =
  paw-nitrogen-snowball-boundary true true true true true true false
