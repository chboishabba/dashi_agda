module DASHI.Cognition.BlackRockMirvacSpringfieldCapitalOverlapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as GasLobby
import DASHI.Law.SensibLawWoogarooSwanbankDataCentreDevelopmentPressureExact as DataCentre

------------------------------------------------------------------------
-- BLACKROCK / MIRVAC / SPRINGFIELD CAPITAL-OVERLAP OWNER
--
-- Narrow same-object statements only:
--   * Mirvac owns Orion Springfield Central 100% and developed/manages it.
--   * BlackRock is a substantial Mirvac securityholder in 2026.
--   * Springfield City Group remains distinct from Mirvac; ownership of Orion
--     does not imply Mirvac controls Greater Springfield as a whole.
--   * BlackRock's Mirvac stake is capital exposure, not operational control of
--     Orion or Springfield.
------------------------------------------------------------------------

record CapitalOverlapReceipt : Set where
  constructor capital-overlap-receipt
  field
    source : String
    boundedFinding : String
    paid : Bool
open CapitalOverlapReceipt public

mirvacOrionReceipt : CapitalOverlapReceipt
mirvacOrionReceipt = capital-overlap-receipt
  "Mirvac Orion Springfield Central portfolio page / FY26 property portfolio"
  "Mirvac reports 100% ownership of Orion Springfield Central, states the centre was developed by Mirvac, and records substantial adjoining land for future expansion. This pays the Orion asset edge, not control of the entire Greater Springfield masterplanned city."
  true

blackRockMirvacReceipt : CapitalOverlapReceipt
blackRockMirvacReceipt = capital-overlap-receipt
  "Mirvac substantial-holder disclosures / 2026 market filing summary"
  "BlackRock Group / BlackRock Investment Management (Australia) is a substantial Mirvac securityholder; 2026 disclosed holding is about 7.70%. This pays listed-equity exposure and voting interest, not day-to-day operational control of Mirvac or Orion."
  true

orionEmbeddedNetworkReceipt : CapitalOverlapReceipt
orionEmbeddedNetworkReceipt = capital-overlap-receipt
  "Australian Energy Regulator Orion Springfield Central network exemption"
  "The AER records Mirvac Real Estate Pty Ltd and Perpetual Nominees Limited as registrants for the current Orion Springfield Central electricity network exemption. This pays an embedded energy-network operational coordinate at Orion, distinct from the broader historical Springfield gas-network lineage."
  true

record CapitalOverlapBoundary : Set where
  constructor capital-overlap-boundary
  field
    blackRockOwnsMirvacShares : Bool
    mirvacOwnsOrion : Bool
    mirvacOwnsGreaterSpringfield : Bool
    blackRockControlsOrionOperations : Bool
    blackRockControlsSpringfieldCityGroup : Bool
    listedEquityExposureEqualsOperationalControl : Bool
    overlapWorthBeneficiaryIncidenceAnalysis : Bool
open CapitalOverlapBoundary public

canonicalCapitalOverlapBoundary : CapitalOverlapBoundary
canonicalCapitalOverlapBoundary = capital-overlap-boundary
  true true false false false false true

data MirvacOrionImpliesGreaterSpringfieldControl : Set where
data BlackRockStakeImpliesOrionOperationalControl : Set where
data BlackRockStakeImpliesSpringfieldCityGroupControl : Set where

mirvacOrionDoesNotCreateGreaterSpringfieldControl :
  MirvacOrionImpliesGreaterSpringfieldControl → ⊥
mirvacOrionDoesNotCreateGreaterSpringfieldControl ()

blackRockStakeDoesNotCreateOrionOperationalControl :
  BlackRockStakeImpliesOrionOperationalControl → ⊥
blackRockStakeDoesNotCreateOrionOperationalControl ()

blackRockStakeDoesNotCreateSpringfieldControl :
  BlackRockStakeImpliesSpringfieldCityGroupControl → ⊥
blackRockStakeDoesNotCreateSpringfieldControl ()

record SpringfieldCapitalIntersection : Set where
  constructor springfield-capital-intersection
  field
    mirvacRetailLandAsset : Bool
    blackRockMirvacExposure : Bool
    springfieldGasAlliancePriorArt : Bool
    springfieldRegisteredLobbyingPriorArt : Bool
    azureLnpDonationPriorArt : Bool
    nearbyDataCentrePressurePriorArt : Bool
    sameSystemControlProved : Bool
open SpringfieldCapitalIntersection public

canonicalSpringfieldCapitalIntersection : SpringfieldCapitalIntersection
canonicalSpringfieldCapitalIntersection = springfield-capital-intersection
  true true true true true true false
