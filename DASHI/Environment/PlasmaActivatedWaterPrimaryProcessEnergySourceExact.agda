module DASHI.Environment.PlasmaActivatedWaterPrimaryProcessEnergySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- PRIMARY PAW PROCESS / ENERGY SOURCE
--
-- This source pays bounded reactor/process coordinates only.
-- Reactor energy yield != agronomic nitrogen-use efficiency != lifecycle
-- emissions != economic or environmental superiority.
------------------------------------------------------------------------

record PAWProcessEnergyPrimarySource : Set where
  constructor paw-process-energy-primary-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PAWProcessEnergyPrimarySource public

zhuangMicrobubbleNFertigation2025 : PAWProcessEnergyPrimarySource
zhuangMicrobubbleNFertigation2025 = paw-process-energy-primary-source
  "Changping Zhuang; Nguyen Van Duc Long; Nam Nghiep Tran; Tianqi Zhang; Patrick Cullen; Galip Akay; Volker Hessel"
  "Microbubble Plasma Processing for N-Fertigation via Plasma Catalysis"
  "ChemCatChem 17(6):e202401838"
  2025
  "DOI 10.1002/cctc.202401838"
  "Primary laboratory process study varying air/nitrogen plasma, catalyst placement and recycling for aqueous nitrogen fixation; reports nitrate/ammonium composition and reactor energy-efficiency coordinates, including fixed-N yield per electrical energy input under declared configurations."
  "Does not establish field nitrogen-use efficiency, crop response, lifecycle carbon advantage, grid/renewable matching, commercial viability, or equivalence across different plasma reactors and source waters."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

data ProcessEnergyMeansAgronomicEfficiencyPermission : Set where
data GramsPerKWhMeansLifecycleBenefitPermission : Set where
data SolarCompatibleMeansZeroEnergyPermission : Set where

processEnergyDoesNotEqualAgronomicEfficiency :
  ProcessEnergyMeansAgronomicEfficiencyPermission → ⊥
processEnergyDoesNotEqualAgronomicEfficiency ()

gramsPerKWhDoesNotProveLifecycleBenefit :
  GramsPerKWhMeansLifecycleBenefitPermission → ⊥
gramsPerKWhDoesNotProveLifecycleBenefit ()

solarCompatibilityDoesNotMeanZeroEnergy :
  SolarCompatibleMeansZeroEnergyPermission → ⊥
solarCompatibleDoesNotMeanZeroEnergy ()

record PAWProcessEnergyAttributionBoundary : Set where
  constructor paw-process-energy-attribution-boundary
  field
    reactorYieldAndAgronomicEfficiencyRemainDistinct : Bool
    electricalInputAndRenewableOriginRemainDistinct : Bool
    processEnergyAndLifecycleEnergyRemainDistinct : Bool
    primaryResultAndDashiPacketWeldRemainDistinct : Bool
    sourceAutomaticallyPaysLowCarbonClaim : Bool

canonicalPAWProcessEnergyAttributionBoundary : PAWProcessEnergyAttributionBoundary
canonicalPAWProcessEnergyAttributionBoundary =
  paw-process-energy-attribution-boundary true true true true false
