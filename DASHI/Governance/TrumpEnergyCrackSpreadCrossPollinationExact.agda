module DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact as Trump
import DASHI.Biology.TrumpPsychogeographyAuthorityBoundary as TrumpBoundary
import DASHI.Governance.PopulistPlutocraticDualProjection as Dual
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Socio
import DASHI.Governance.ExternalityCarrierAttractor as Externality
import DASHI.Governance.IranUS2026RestitutionObservation as IranUS

------------------------------------------------------------------------
-- TRUMP-ENERGY / CRACK-SPREAD CROSS-POLLINATION
--
-- Date-indexed empirical snapshots are kept distinct from generic DASHI
-- theorems.  The purpose is to prevent crude price, refining margin, retail
-- burden, policy narrative, named-actor motive and causal attribution from
-- collapsing into one political-economic scalar.
------------------------------------------------------------------------

record EnergySourceReceipt : Set where
  constructor energy-source-receipt
  field
    publisher : String
    title : String
    observationDate : String
    sourceURL : String
    boundedRole : String

open EnergySourceReceipt public

eiaDailyPriceSource : EnergySourceReceipt
eiaDailyPriceSource =
  energy-source-receipt
    "U.S. Energy Information Administration"
    "Today in Energy Daily Prices"
    "2026-08-28 page / 2026-08-27 close"
    "https://www.eia.gov/todayinenergy/prices.php"
    "Date-indexed wholesale/retail petroleum and Gulf Coast 3:2:1 crack-spread snapshot; not a causal attribution source."

eiaAugustSTEOSource : EnergySourceReceipt
eiaAugustSTEOSource =
  energy-source-receipt
    "U.S. Energy Information Administration"
    "Short-Term Energy Outlook, August 2026"
    "2026-08"
    "https://www.eia.gov/outlooks/steo/archives/aug26.pdf"
    "Forecast/source context that tight global petroleum-product markets support U.S. refinery margins through end-2026; not a Trump-policy effect theorem."

reutersAugust31OilSource : EnergySourceReceipt
reutersAugust31OilSource =
  energy-source-receipt
    "Reuters"
    "Oil rises over 3% as US, Iran resumes military attacks"
    "2026-08-31"
    "https://www.reuters.com/business/energy/oil-jumps-more-than-2-after-us-attack-irans-larak-island-2026-08-30/"
    "Current geopolitical/oil-price observation; not unique-cause, motive, legality or policy-merit authority."

------------------------------------------------------------------------
-- Exact integer encoding of the latest EIA daily snapshot used here.
-- Dollars are encoded as cents.  Crack spread is cents per barrel; product
-- prices are cents per gallon.
------------------------------------------------------------------------

record EnergyMarketSnapshot : Set where
  constructor energy-market-snapshot
  field
    wtiCentsPerBarrel : Nat
    brentCentsPerBarrel : Nat
    gulfRBOBCentsPerGallon : Nat
    gulfDieselCentsPerGallon : Nat
    gulf321CrackCentsPerBarrel : Nat
    usRetailGasolineCentsPerGallon : Nat
    usRetailDieselCentsPerGallon : Nat

open EnergyMarketSnapshot public

eia20260827Close : EnergyMarketSnapshot
eia20260827Close =
  energy-market-snapshot
    8481   -- WTI $84.81/bbl
    9018   -- Brent $90.18/bbl
    343    -- Gulf Coast RBOB $3.43/gal
    427    -- Gulf Coast low-sulfur diesel $4.27/gal
    6790   -- Gulf Coast 3:2:1 crack $67.90/bbl
    409    -- U.S. retail regular gasoline $4.09/gal
    561    -- U.S. retail diesel $5.61/gal

------------------------------------------------------------------------
-- Market fibres: one headline cannot recover all material positions.
------------------------------------------------------------------------

data MarketPosition : Set where
  upstreamProducer refiner consumerTransportUser : MarketPosition

data PositionInterest : Set where
  crudeRevenue refineryMargin retailAffordability : PositionInterest

positionInterest : MarketPosition → PositionInterest
positionInterest upstreamProducer = crudeRevenue
positionInterest refiner = refineryMargin
positionInterest consumerTransportUser = retailAffordability

upstreamAndRefinerInterestsAreDistinct :
  positionInterest upstreamProducer ≡ positionInterest refiner → ⊥
upstreamAndRefinerInterestsAreDistinct ()

refinerAndConsumerInterestsAreDistinct :
  positionInterest refiner ≡ positionInterest consumerTransportUser → ⊥
refinerAndConsumerInterestsAreDistinct ()

------------------------------------------------------------------------
-- Crude abundance / crude price does not by itself settle product affordability.
------------------------------------------------------------------------

data EnergyNarrative : Set where
  domesticAbundance cheapEnergyForConsumers : EnergyNarrative

data MarketLayer : Set where
  crudeLayer refiningLayer retailLayer : MarketLayer

data BindingConstraint : Set where
  crudeSupplyConstraint refiningCapacityConstraint transportConstraint mixedConstraint : BindingConstraint

record ProductMarketState : Set where
  constructor product-market-state
  field
    crudeLayerState : MarketLayer
    downstreamConstraint : BindingConstraint

adequateCrudeTightProducts : ProductMarketState
adequateCrudeTightProducts =
  product-market-state crudeLayer refiningCapacityConstraint

data CrudeAdequacyAutomaticallyMeansCheapRetail
    (s : ProductMarketState) : Set where

crudeAdequacyDoesNotAutomaticallyMeanCheapRetail :
  CrudeAdequacyAutomaticallyMeansCheapRetail adequateCrudeTightProducts → ⊥
crudeAdequacyDoesNotAutomaticallyMeanCheapRetail ()

------------------------------------------------------------------------
-- Policy/source boundaries already present in the Trump atlas remain active.
------------------------------------------------------------------------

existingTariffSurface : Trump.PolicyCaseSurface
existingTariffSurface = Trump.tariffIndustrialPolicySurface

existingTrumpBoundary : TrumpBoundary.TrumpPsychogeographicCrossPollination
existingTrumpBoundary = TrumpBoundary.canonicalTrumpPsychogeographicCrossPollination

tariffPolicyStillDoesNotGuaranteeWorkerBenefit :
  TrumpBoundary.tariffPolicyGuaranteesWorkerBenefit existingTrumpBoundary ≡ false
tariffPolicyStillDoesNotGuaranteeWorkerBenefit = refl

tradePolicySourceDoesNotCreateOutcome :
  Trump.sourceCreatesPolicyEndorsement Trump.tradePolicySource ≡ false
tradePolicySourceDoesNotCreateOutcome = refl

------------------------------------------------------------------------
-- Populist identification / material position separation.
------------------------------------------------------------------------

record EnergyPublicPosition : Set where
  constructor energy-public-position
  field
    popularIdentification : Bool
    materialBeneficiary : MarketPosition

producerPopulist : EnergyPublicPosition
producerPopulist = energy-public-position true upstreamProducer

refinerPopulist : EnergyPublicPosition
refinerPopulist = energy-public-position true refiner

consumerPopulist : EnergyPublicPosition
consumerPopulist = energy-public-position true consumerTransportUser

samePopularIdentificationDifferentMaterialInterest :
  popularIdentification producerPopulist ≡ popularIdentification consumerPopulist
samePopularIdentificationDifferentMaterialInterest = refl

materialInterestStillDiffers :
  positionInterest (materialBeneficiary producerPopulist)
  ≡ positionInterest (materialBeneficiary consumerPopulist) → ⊥
materialInterestStillDiffers ()

------------------------------------------------------------------------
-- Causal compression boundaries.
------------------------------------------------------------------------

data CandidateDriver : Set where
  crudeSupply
  refineryCapacity
  productInventory
  shippingRisk
  sanctionsPolicy
  militaryEscalation
  tariffsAndTrade
  seasonalDemand
  refineryOutage
  : CandidateDriver

record EnergyCausalClaim : Set where
  constructor energy-causal-claim
  field
    selectedDriver : CandidateDriver
    sourceSpecific : Bool
    dateBound : Bool
    establishesUniqueCause : Bool

geopoliticalContributionClaim : EnergyCausalClaim
geopoliticalContributionClaim =
  energy-causal-claim militaryEscalation true true false

tariffContributionClaim : EnergyCausalClaim
tariffContributionClaim =
  energy-causal-claim tariffsAndTrade true true false

------------------------------------------------------------------------
-- Cross-pollinated existing owners.
------------------------------------------------------------------------

socioTechnicalBoundary : Socio.SocioTechnicalPowerSelectionBoundary
socioTechnicalBoundary = Socio.canonicalSocioTechnicalPowerSelectionBoundary

externalityBoundary : Externality.ExternalityCarrierBoundary
externalityBoundary = Externality.canonicalExternalityCarrierBoundary

iranUSObservation : IranUS.IranUS2026Observation
iranUSObservation = IranUS.canonicalIranUS2026Observation

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record TrumpEnergyCrackSpreadBoundary : Set where
  constructor trump-energy-crack-spread-boundary
  field
    crudePriceEqualsRetailFuelBurden : Bool
    crudePriceEqualsRetailFuelBurdenIsFalse : crudePriceEqualsRetailFuelBurden ≡ false
    crudeSupplyAdequacyGuaranteesCheapProducts : Bool
    crudeSupplyAdequacyGuaranteesCheapProductsIsFalse :
      crudeSupplyAdequacyGuaranteesCheapProducts ≡ false
    highRefiningMarginImpliesConsumerBenefit : Bool
    highRefiningMarginImpliesConsumerBenefitIsFalse : highRefiningMarginImpliesConsumerBenefit ≡ false
    energyAbundanceNarrativeDeterminesMaterialBenefit : Bool
    energyAbundanceNarrativeDeterminesMaterialBenefitIsFalse :
      energyAbundanceNarrativeDeterminesMaterialBenefit ≡ false
    tariffPolicyUniquelyCausesCurrentCrackSpread : Bool
    tariffPolicyUniquelyCausesCurrentCrackSpreadIsFalse :
      tariffPolicyUniquelyCausesCurrentCrackSpread ≡ false
    militaryEscalationUniquelyCausesCurrentCrackSpread : Bool
    militaryEscalationUniquelyCausesCurrentCrackSpreadIsFalse :
      militaryEscalationUniquelyCausesCurrentCrackSpread ≡ false
    dailySnapshotProvesStructuralTrend : Bool
    dailySnapshotProvesStructuralTrendIsFalse : dailySnapshotProvesStructuralTrend ≡ false
    namedActorMotiveFollowsFromMarketOutcome : Bool
    namedActorMotiveFollowsFromMarketOutcomeIsFalse :
      namedActorMotiveFollowsFromMarketOutcome ≡ false
    reading : String

canonicalTrumpEnergyCrackSpreadBoundary : TrumpEnergyCrackSpreadBoundary
canonicalTrumpEnergyCrackSpreadBoundary =
  trump-energy-crack-spread-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Current oil/refining conditions are a multi-fibre political-economy assay: crude price, refinery margin, retail burden, upstream/refiner/consumer position, trade policy and geopolitical risk remain distinct. Trump-policy and populist/plutocratic owners may structure the questions, but current spreads do not by themselves establish named-actor motive, unique causation, worker benefit or consumer benefit."
