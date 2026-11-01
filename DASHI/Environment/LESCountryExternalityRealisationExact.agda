module DASHI.Environment.LESCountryExternalityRealisationExact where

------------------------------------------------------------------------
-- LES / COUNTRY / EXTERNALITY REALISATION
--
-- Cross-pollinates the existing LES situated socio-ecological fabric with the
-- Country/remedy programme.  The coordinate carrier is DASHI reconstruction.
-- It does not attribute this exact list to Holmgren, Kimmerer, Two-Eyed Seeing,
-- any Indigenous community, or an external environmental-economics source.
--
-- Crucial vocabulary boundary:
-- Country, collective authority, reciprocal obligation and cultural relation
-- are not defined as assets or commodities. Monetary valuation is one optional
-- observer coordinate among many.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Environment.LESObservationSourceRegistryExact as LESSources
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed

------------------------------------------------------------------------
-- Externalities / realised effects are multi-coordinate.
------------------------------------------------------------------------

data CountryEcologicalCoordinate : Set where
  carbonStorageAndSequestration : CountryEcologicalCoordinate
  avoidedEmissions : CountryEcologicalCoordinate
  waterRetentionAndQuality : CountryEcologicalCoordinate
  biodiversityAndHabitat : CountryEcologicalCoordinate
  soilIntegrity : CountryEcologicalCoordinate
  fireAndDisturbanceRegime : CountryEcologicalCoordinate
  countryRelationContinuity : CountryEcologicalCoordinate
  culturalContinuity : CountryEcologicalCoordinate
  intergenerationalBurden : CountryEcologicalCoordinate
  collectiveDecisionAuthority : CountryEcologicalCoordinate
  reciprocalObligationRealisation : CountryEcologicalCoordinate
  materialLivelihood : CountryEcologicalCoordinate
  publicFiscalTransfer : CountryEcologicalCoordinate
  privateMarketRevenue : CountryEcologicalCoordinate


data CoordinateObservationState : Set where
  realisedPositive : CoordinateObservationState
  realisedNegative : CoordinateObservationState
  mixedOrContextDependent : CoordinateObservationState
  unmeasured : CoordinateObservationState
  sourceSpecific : CoordinateObservationState


record MultiCoordinateOutcome : Set where
  constructor multi-coordinate-outcome
  field
    stateOf : CountryEcologicalCoordinate → CoordinateObservationState
    outcomeReference : String
    empiricalWorldClaimMadeByThisFixture : Bool
    empiricalWorldClaimMadeByThisFixtureIsFalse :
      empiricalWorldClaimMadeByThisFixture ≡ false

open MultiCoordinateOutcome public

------------------------------------------------------------------------
-- Monetary observers are intentionally coarse.
------------------------------------------------------------------------

data FineCountryState : Set where
  sameRevenueHighStewardship : FineCountryState
  sameRevenueLowStewardship : FineCountryState


data RevenueSurface : Set where
  sameRevenueObservation : RevenueSurface

data CountryStewardshipState : Set where
  authorityBearingEcologicalContinuity : CountryStewardshipState
  authorityPoorEcologicalDegradation : CountryStewardshipState


revenueObserver : FineCountryState → RevenueSurface
revenueObserver _ = sameRevenueObservation

countryStewardship : FineCountryState → CountryStewardshipState
countryStewardship sameRevenueHighStewardship = authorityBearingEcologicalContinuity
countryStewardship sameRevenueLowStewardship = authorityPoorEcologicalDegradation

countryStewardshipDiffers :
  countryStewardship sameRevenueHighStewardship
  ≡ countryStewardship sameRevenueLowStewardship → ⊥
countryStewardshipDiffers ()

revenueCannotRecoverCountryStewardshipWitness :
  INF.NonFactorabilityWitness revenueObserver countryStewardship
revenueCannotRecoverCountryStewardshipWitness =
  INF.nonFactorabilityWitness
    sameRevenueHighStewardship
    sameRevenueLowStewardship
    refl
    countryStewardshipDiffers

revenueCannotRecoverCountryStewardship :
  INF.FactorsThrough revenueObserver countryStewardship → ⊥
revenueCannotRecoverCountryStewardship =
  INF.witnessRulesOutEveryFlatFactorisation
    revenueCannotRecoverCountryStewardshipWitness

revenueReweightingCannotRecoverCountryStewardship :
  ∀ {Reweighted : Set} →
  (reweight : RevenueSurface → Reweighted) →
  INF.FactorsThrough
    (λ state → reweight (revenueObserver state))
    countryStewardship → ⊥
revenueReweightingCannotRecoverCountryStewardship reweight =
  INF.rechartingCannotRecoverErasedPhenomenon
    reweight revenueCannotRecoverCountryStewardshipWitness

------------------------------------------------------------------------
-- Carbon is important but is still not the whole Country relation.
------------------------------------------------------------------------

data CarbonSurface : Set where
  sameCarbonObservation : CarbonSurface

data CountryAuthorityState : Set where
  communityAuthorityPresent : CountryAuthorityState
  communityAuthorityAbsent : CountryAuthorityState


data CarbonAuthorityState : Set where
  sameCarbonWithAuthority : CarbonAuthorityState
  sameCarbonWithoutAuthority : CarbonAuthorityState


carbonObserver : CarbonAuthorityState → CarbonSurface
carbonObserver _ = sameCarbonObservation

communityAuthority : CarbonAuthorityState → CountryAuthorityState
communityAuthority sameCarbonWithAuthority = communityAuthorityPresent
communityAuthority sameCarbonWithoutAuthority = communityAuthorityAbsent

communityAuthorityDiffers :
  communityAuthority sameCarbonWithAuthority
  ≡ communityAuthority sameCarbonWithoutAuthority → ⊥
communityAuthorityDiffers ()

carbonCannotRecoverCommunityAuthority :
  INF.FactorsThrough carbonObserver communityAuthority → ⊥
carbonCannotRecoverCommunityAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameCarbonWithAuthority
      sameCarbonWithoutAuthority
      refl
      communityAuthorityDiffers)

------------------------------------------------------------------------
-- LES provenance/justice/history relation remains required.
------------------------------------------------------------------------

lesCoarseSummaryStillInsufficient :
  INF.FactorsThrough LES.fullCoarseObservation LES.fullPlanningSignature → ⊥
lesCoarseSummaryStillInsufficient =
  LES.fullCoarseSummaryCannotRecoverFullPlanningSignature

lesSourceBoundary : LESSources.LESObservationAttributionBoundary
lesSourceBoundary = LESSources.canonicalLESObservationAttributionBoundary

holmgrenDoesNotOwnThisExternalityHyperfabric :
  LESSources.holmgrenProvesDASHINonFactorability lesSourceBoundary ≡ false
holmgrenDoesNotOwnThisExternalityHyperfabric = refl

sharedObservationDoesNotFuseKnowledgeHistories :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistories = refl

------------------------------------------------------------------------
-- Externality accounting boundary.
------------------------------------------------------------------------

record ExternalityAccountingBoundary : Set where
  constructor externality-accounting-boundary
  field
    marketRevenueExhaustsCountryValue : Bool
    marketRevenueExhaustsCountryValueIsFalse :
      marketRevenueExhaustsCountryValue ≡ false
    carbonPriceExhaustsClimateValue : Bool
    carbonPriceExhaustsClimateValueIsFalse : carbonPriceExhaustsClimateValue ≡ false
    carbonMetricExhaustsCommunityAuthority : Bool
    carbonMetricExhaustsCommunityAuthorityIsFalse :
      carbonMetricExhaustsCommunityAuthority ≡ false
    fiscalTransferExhaustsMaterialRepair : Bool
    fiscalTransferExhaustsMaterialRepairIsFalse :
      fiscalTransferExhaustsMaterialRepair ≡ false
    unpricedEffectMeansEffectDoesNotExist : Bool
    unpricedEffectMeansEffectDoesNotExistIsFalse :
      unpricedEffectMeansEffectDoesNotExist ≡ false
    countryRelationIsAssetByDefault : Bool
    countryRelationIsAssetByDefaultIsFalse : countryRelationIsAssetByDefault ≡ false
    communityAuthorityIsPropertyRightByDefault : Bool
    communityAuthorityIsPropertyRightByDefaultIsFalse :
      communityAuthorityIsPropertyRightByDefault ≡ false
    carbonAndEcologicalCoordinatesRemainRelevantToPlanning : Bool
    carbonAndEcologicalCoordinatesRemainRelevantToPlanningIsTrue :
      carbonAndEcologicalCoordinatesRemainRelevantToPlanning ≡ true

open ExternalityAccountingBoundary public

canonicalExternalityAccountingBoundary : ExternalityAccountingBoundary
canonicalExternalityAccountingBoundary = externality-accounting-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CarbonSequestrationEqualsCountry : Set where
data EcosystemServiceValuationEqualsCommunityAuthority : Set where
data UnpricedEcologyIsZeroValue : Set where
data ExternalityAccountingTransfersIndigenousAuthority : Set where

carbonDoesNotEqualCountryRelation : CarbonSequestrationEqualsCountry → ⊥
carbonDoesNotEqualCountryRelation ()

ecosystemValuationDoesNotEqualCommunityAuthority :
  EcosystemServiceValuationEqualsCommunityAuthority → ⊥
ecosystemValuationDoesNotEqualCommunityAuthority ()

unpricedDoesNotMeanZero : UnpricedEcologyIsZeroValue → ⊥
unpricedDoesNotMeanZero ()

accountingDoesNotTransferAuthority : ExternalityAccountingTransfersIndigenousAuthority → ⊥
accountingDoesNotTransferAuthority ()
