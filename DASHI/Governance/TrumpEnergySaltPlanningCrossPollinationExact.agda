module DASHI.Governance.TrumpEnergySaltPlanningCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact as Energy
import DASHI.Chemistry.RefineryFeedstockSaltConstraintBidiExact as Refinery
import DASHI.Planning.EnergyRefineryNetworkConstraintCrossPollinationExact as Planning
import DASHI.Geology.SaltGeochemistryExact as Salt
import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact as Water
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Socio

------------------------------------------------------------------------
-- TRUMP ENERGY / SALT / CHEMISTRY / PLANNING CROSS-POLLINATION
--
-- The current crack-spread observation is deliberately downstream of a process
-- chain.  This bridge makes the chain explicit without attributing the observed
-- spread to one chemistry variable, one policy instrument, one outage, or one
-- named actor.
--
--   crude/feedstock availability
--      -> composition / salt-water assay
--      -> desalting and process admissibility
--      -> corrosion/fouling/reliability burden
--      -> chemistry-qualified effective throughput
--      -> storage/logistics/product-delivery constraints
--      -> product-market / crack-spread observation
--      -> differentiated producer/refiner/consumer incidence.
------------------------------------------------------------------------

data EnergyProcessLayer : Set where
  feedstockAvailabilityLayer
  feedstockChemistryLayer
  pretreatmentLayer
  refineryReliabilityLayer
  effectiveThroughputLayer
  logisticsLayer
  productMarketLayer
  retailIncidenceLayer
  : EnergyProcessLayer

record EnergyProcessChainReceipt : Set where
  constructor energy-process-chain-receipt
  field
    feedstockReference : String
    chemistryAssayReference : String
    pretreatmentReference : String
    reliabilityReference : String
    throughputReference : String
    logisticsReference : String
    productMarketReference : String
    retailIncidenceReference : String
    commonDateContextReference : String
    validationReference : String

------------------------------------------------------------------------
-- Existing exact boundaries are imported as one receipt surface.
------------------------------------------------------------------------

record TrumpEnergySaltPlanningReceipt : Set where
  constructor trump-energy-salt-planning-receipt
  field
    marketBoundary : Energy.TrumpEnergyCrackSpreadBoundary
    refineryChemistryBoundary : Refinery.RefineryFeedstockSaltBoundary
    planningBoundary : Planning.EnergyRefineryPlanningBoundary
    saltBoundary : Salt.SaltGeochemistryBoundary
    waterCorrosionBoundary : Water.DistributionResidualCorrosionBoundary
    socioTechnicalBoundary : Socio.SocioTechnicalPowerSelectionBoundary

canonicalTrumpEnergySaltPlanningReceipt : TrumpEnergySaltPlanningReceipt
canonicalTrumpEnergySaltPlanningReceipt =
  trump-energy-salt-planning-receipt
    Energy.canonicalTrumpEnergyCrackSpreadBoundary
    Refinery.canonicalRefineryFeedstockSaltBoundary
    Planning.canonicalEnergyRefineryPlanningBoundary
    Salt.canonicalSaltGeochemistryBoundary
    Water.canonicalDistributionResidualCorrosionBoundary
    Socio.canonicalSocioTechnicalPowerSelectionBoundary

------------------------------------------------------------------------
-- Cross-domain non-promotion boundary.
------------------------------------------------------------------------

record TrumpEnergySaltPlanningBoundary : Set where
  constructor trump-energy-salt-planning-boundary
  field
    highCrackSpreadIdentifiesHighFeedstockSalt : Bool
    highCrackSpreadIdentifiesHighFeedstockSaltIsFalse :
      highCrackSpreadIdentifiesHighFeedstockSalt ≡ false
    highFeedstockSaltUniquelyIdentifiesCorrosionCause : Bool
    highFeedstockSaltUniquelyIdentifiesCorrosionCauseIsFalse :
      highFeedstockSaltUniquelyIdentifiesCorrosionCause ≡ false
    crudeAbundanceEqualsChemistryQualifiedThroughput : Bool
    crudeAbundanceEqualsChemistryQualifiedThroughputIsFalse :
      crudeAbundanceEqualsChemistryQualifiedThroughput ≡ false
    refineryNameplateCapacityEqualsDeliveredProductCapacity : Bool
    refineryNameplateCapacityEqualsDeliveredProductCapacityIsFalse :
      refineryNameplateCapacityEqualsDeliveredProductCapacity ≡ false
    refineryConstraintUniquelyExplainsRetailPrice : Bool
    refineryConstraintUniquelyExplainsRetailPriceIsFalse :
      refineryConstraintUniquelyExplainsRetailPrice ≡ false
    saltChemistryObservationCreatesTrumpPolicyCausation : Bool
    saltChemistryObservationCreatesTrumpPolicyCausationIsFalse :
      saltChemistryObservationCreatesTrumpPolicyCausation ≡ false
    policyNarrativeDeterminesPhysicalProcessState : Bool
    policyNarrativeDeterminesPhysicalProcessStateIsFalse :
      policyNarrativeDeterminesPhysicalProcessState ≡ false
    wholeChainNeedsDateAlignedEvidence : Bool
    wholeChainNeedsDateAlignedEvidenceIsTrue :
      wholeChainNeedsDateAlignedEvidence ≡ true

canonicalTrumpEnergySaltPlanningBoundary : TrumpEnergySaltPlanningBoundary
canonicalTrumpEnergySaltPlanningBoundary =
  trump-energy-salt-planning-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
