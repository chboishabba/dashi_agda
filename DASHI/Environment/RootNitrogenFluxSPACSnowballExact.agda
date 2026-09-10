module DASHI.Environment.RootNitrogenFluxSPACSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.RootNitrogenFluxPrimarySourceExact as Sources
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.Nitrogen15NTracerSPACPrimaryWeldExact as SeasonTracer
import DASHI.Environment.WholeLandscapePrimaryDependencyReceiptsExact as Primary

------------------------------------------------------------------------
-- SHORT-TERM ROOT 15N FLUX -> EXISTING SPAC ROOT-N UPTAKE SOCKET
--
-- External source owns the bounded hydroponic isotope-flux observation.
-- DASHI owns the admission/weld.  The source does not automatically validate
-- a field SPAC realization and does not replace the whole-season tracer lane.
------------------------------------------------------------------------

record RootFluxSPACAdmission
    (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor root-flux-spac-admission
  field
    source : Sources.RootNitrogenFluxPrimarySource
    sourceIsCanonicalMaizeFluxStudy :
      source ≡ Sources.garnettMaizeRootFlux2015
    nitrogenSpeciesReference : String
    exactSpeciesGenotypeReference : String
    exactGrowthNStateReference : String
    exactAssayConcentrationReference : String
    exactAssayDurationReference : String
    rootCompartmentReference : String
    isotopeFluxMeasurementReference : String
    spacRootUptakeSocketReference : String
    measuredFluxToDeclaredSPACConsumerReference : String
    hydroponicToSPACEnvironmentRelationReference : String
    sameTemporalSemanticsReference : String
    validationReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsWeld :
      dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open RootFluxSPACAdmission public

spacRootNitrogenSocket :
  (spac : SPAC.SPACDomainRealization) → String
spacRootNitrogenSocket spac =
  SPAC.rootUptakeToMineralNReference (SPAC.biogeochemistryFeedback spac)

------------------------------------------------------------------------
-- Snowball: acquisition can happen out of order; payment cannot.
------------------------------------------------------------------------

record RootFluxAcquisitionState : Set where
  constructor root-flux-acquisition-state
  field
    primarySourceAcquired : Bool
    isotopeMethodAcquired : Bool
    speciesGenotypeAcquired : Bool
    nitrogenSpeciesAcquired : Bool
    concentrationAcquired : Bool
    assayDurationAcquired : Bool
    hydroponicEnvironmentAcquired : Bool
    spacRealisationAcquired : Bool
    seasonTracerAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open RootFluxAcquisitionState public

record RootFluxPaymentState : Set where
  constructor root-flux-payment-state
  field
    sourceIdentityPaid : Bool
    speciesGenotypePaid : Bool
    nitrogenSpeciesPaid : Bool
    assayConcentrationPaid : Bool
    assayDurationPaid : Bool
    rootCompartmentPaid : Bool
    uptakeCapacitySemanticsPaid : Bool
    spacSocketIdentityPaid : Bool
    environmentTransportPaid : Bool
    netFluxInterpretationPaid : Bool
    fieldValidationPaid : Bool
    firstUnpaidGateReference : String

open RootFluxPaymentState public

snowballAcquisitionDoesNotAdvanceRootFluxPayment :
  RootFluxAcquisitionState → RootFluxPaymentState → RootFluxPaymentState
snowballAcquisitionDoesNotAdvanceRootFluxPayment _ payment = payment

------------------------------------------------------------------------
-- The short assay and whole-season tracer are complementary consumers.
------------------------------------------------------------------------

record ShortFluxSeasonTracerBidi
    {spac : SPAC.SPACDomainRealization}
    (shortFlux : RootFluxSPACAdmission spac)
    {receipt : Primary.NitrogenToCropSoilPrimaryReceipt}
    (season : SeasonTracer.TracerSPACAdmission receipt spac) : Set₁ where
  constructor short-flux-season-tracer-bidi
  field
    commonPlantNitrogenConsumerReference : String
    temporalAggregationReference : String
    compartmentAggregationReference : String
    sourceStudyDifferenceReference : String
    shortFluxDoesNotDefinitionallyIntegrateToSeasonUptake : Bool
    seasonUptakeDoesNotRecoverInstantaneousFlux : Bool

open ShortFluxSeasonTracerBidi public

------------------------------------------------------------------------
-- WrongType barriers.
------------------------------------------------------------------------

data ShortFluxMeansSeasonUptakePermission : Set where
data SeasonUptakeMeansShortFluxPermission : Set where
data HydroponicAssayMeansFieldTransportPermission : Set where
data RootFluxMeansAllocationPermission : Set where
data ExternalAssayOwnsDashiSPACWeldPermission : Set where

shortFluxDoesNotDefinitionallyMeanSeasonUptake :
  ShortFluxMeansSeasonUptakePermission → ⊥
shortFluxDoesNotDefinitionallyMeanSeasonUptake ()

seasonUptakeDoesNotRecoverShortFlux :
  SeasonUptakeMeansShortFluxPermission → ⊥
seasonUptakeDoesNotRecoverShortFlux ()

hydroponicAssayDoesNotPayFieldTransport :
  HydroponicAssayMeansFieldTransportPermission → ⊥
hydroponicAssayDoesNotPayFieldTransport ()

rootFluxDoesNotPayAllocation :
  RootFluxMeansAllocationPermission → ⊥
rootFluxDoesNotPayAllocation ()

externalAssayDoesNotOwnDashiSPACWeld :
  ExternalAssayOwnsDashiSPACWeldPermission → ⊥
externalAssayDoesNotOwnDashiSPACWeld ()

record RootFluxSPACBoundary : Set where
  constructor root-flux-spac-boundary
  field
    sourceAndDashiWeldRemainDistinct : Bool
    uptakeCapacityNetFluxAndSeasonUptakeRemainDistinct : Bool
    hydroponicAndFieldEnvironmentRemainDistinct : Bool
    rootFluxAndAllocationRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    sourceAutomaticallyPaysFieldSPAC : Bool

canonicalRootFluxSPACBoundary : RootFluxSPACBoundary
canonicalRootFluxSPACBoundary =
  root-flux-spac-boundary true true true true true false
