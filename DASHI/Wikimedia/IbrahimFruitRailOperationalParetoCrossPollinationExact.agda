module DASHI.Wikimedia.IbrahimFruitRailOperationalParetoCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimOracleCrossDomainFibreCrossPollinationExact as Cross
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Planning.ChemicalManufacturingInventoryLogisticsCrossPollinationExact as Logistics
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- IBRAHIM FRUIT / RAIL OPERATIONAL PARETO CROSS-POLLINATION
--
-- The paper-owned edges
--
--   Banana -> fruit
--   Train  -> rail transport
--
-- are used as traversal seeds.  Rail has a stronger immediate reuse seam than
-- fruit because the existing chemical-logistics owner already has a literal
-- network-leg carrier with transport-mode, capacity, inventory, custody,
-- hazard, state and validation references.  Fruit has no canonical yield or
-- reproductive-output theorem owner, so the honest next layer is an admission
-- receipt over an existing SPAC realization, not a new yield model.
------------------------------------------------------------------------

ibrahimSource : String
ibrahimSource =
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds, Connecting every bit of knowledge: The structure of Wikipedia's First Link Network, Journal of Computational Science 19 (2017) 21-30, DOI 10.1016/j.jocs.2016.12.001"

ibrahimDOILink : String
ibrahimDOILink = "https://doi.org/10.1016/j.jocs.2016.12.001"

bananaQid : String
bananaQid = "Q503"

fruitQid : String
fruitQid = "Q1364"

trainQid : String
trainQid = "Q870"

railTransportQid : String
railTransportQid = "Q3565868"

unresolvedDewey : String
unresolvedDewey = "unresolved"

------------------------------------------------------------------------
-- RAIL: direct specialization of the existing chemical network leg.
------------------------------------------------------------------------

record RailChemicalNetworkAdmission
    (leg : Logistics.ChemicalNetworkLeg) : Set where
  constructor rail-chemical-network-admission
  field
    railTransportIdentityReference : String
    railTransportQidReference : String
    exactShipmentReference : String
    exactOriginReference : String
    exactDestinationReference : String
    timeReference : String
    rollingStockOrConsistReference : String
    routeOrCorridorReference : String
    transportModeMatchesRailReference : String
    sameObjectCustodyReference : String
    capacityReceiptReference : String
    validationReference : String
    railIdentityPaid : Bool
    sameObjectShipmentPaid : Bool
    transportModePaid : Bool
open RailChemicalNetworkAdmission public

record RailAdmissionBoundary : Set where
  constructor rail-admission-boundary
  field
    trainQidIdentifiesShipment : Bool
    railQidIdentifiesMaterial : Bool
    railModeCreatesCustody : Bool
    networkLegStillOwnsMaterialAndCapacity : Bool
    sameObjectShipmentStillRequired : Bool
open RailAdmissionBoundary public

canonicalRailAdmissionBoundary : RailAdmissionBoundary
canonicalRailAdmissionBoundary =
  rail-admission-boundary false false false true true

------------------------------------------------------------------------
-- FRUIT: consumer admission over an existing SPAC realization.
------------------------------------------------------------------------

record FruitLESOutputAdmission
    (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor fruit-les-output-admission
  field
    fruitObjectReference : String
    speciesOrCultivarReference : String
    reproductiveStageReference : String
    measuredFruitOutputReference : String
    outputUnitReference : String
    plantCarbonAllocationReference : String
    plantWaterStateReference : String
    nutrientStateReference : String
    photosynthesisReference : String
    commonSpatialReference : String
    commonTemporalReference : String
    interventionOrControlReference : String
    discrepancyModelReference : String
    heldOutValidationReference : String
    exactPlantObjectPaid : Bool
    exactFruitOutputPaid : Bool
    sameSPACStateJoinPaid : Bool
open FruitLESOutputAdmission public

spacPrimarySourceDOI : String
spacPrimarySourceDOI = SPAC.sperryStillerHackeDOI

record FruitAdmissionBoundary : Set where
  constructor fruit-admission-boundary
  field
    fruitQidCreatesYieldObservation : Bool
    bananaIdentityCreatesCultivarIdentity : Bool
    plantCarbonAllocationCreatesFruitOutput : Bool
    waterStateAloneCreatesFruitOutput : Bool
    nutrientStateAloneCreatesFruitOutput : Bool
    concreteFruitConsumerMustJoinSameSPACState : Bool
open FruitAdmissionBoundary public

canonicalFruitAdmissionBoundary : FruitAdmissionBoundary
canonicalFruitAdmissionBoundary =
  fruit-admission-boundary false false false false false true

------------------------------------------------------------------------
-- Pareto routing.
------------------------------------------------------------------------

data OperationalTarget : Set where
  railSameObjectNetworkLeg
  fruitSameObjectOutputConsumer
  railFleetOrRouteDynamics
  fruitCausalYieldModel : OperationalTarget

record OperationalParetoStep : Set where
  constructor operational-pareto-step
  field
    priority : Nat
    target : OperationalTarget
    acquisition : String
    pays : String
    dominatedReason : String
open OperationalParetoStep public

firstOperationalTarget : OperationalParetoStep
firstOperationalTarget = operational-pareto-step
  0 railSameObjectNetworkLeg
  "bind one concrete rail shipment to an existing ChemicalNetworkLeg with material, capacity, inventory, transport mode and custody receipts"
  "turns Train -> rail transport from navigation into a same-object logistics specialization without creating chemistry facts"
  "none: existing carrier already contains the needed operational coordinates"

secondOperationalTarget : OperationalParetoStep
secondOperationalTarget = operational-pareto-step
  1 fruitSameObjectOutputConsumer
  "bind one concrete fruit observation to an existing SPACDomainRealization and explicit reproductive/output measurements"
  "adds the missing plant-output consumer while retaining water, carbon, nutrient and validation fibres"
  "requires a concrete fruit/crop observation; generic fruit identity cannot instantiate output"

thirdOperationalTarget : OperationalParetoStep
thirdOperationalTarget = operational-pareto-step
  4 railFleetOrRouteDynamics
  "add rolling-stock, schedule and route dynamics only after a same-object network leg exists"
  "transport dynamics for a specific shipment"
  "dominated by shipment/material/custody identity"

fourthOperationalTarget : OperationalParetoStep
fourthOperationalTarget = operational-pareto-step
  8 fruitCausalYieldModel
  "fit or prove a causal/yield relation only after same-state fruit output, controls, discrepancy model and held-out validation are paid"
  "situated causal fruit-output claim"
  "dominated by output identity and SPAC same-object join"

------------------------------------------------------------------------
-- Fibres over time.
------------------------------------------------------------------------

data OperationalTime : Set where
  ibrahimNavigationTime
  dashiStructuralBridgeTime
  sameObjectAdmissionTime
  validatedConsumerTime : OperationalTime

data OperationalInterpretation : Set where
  navigationOnly
  structuralConsumerCandidate
  sameObjectConsumer
  validatedConsumer : OperationalInterpretation

data OperationalSummary : Set where operationalFrontierOpen : OperationalSummary

OperationalCompatible : OperationalTime → OperationalInterpretation → Set
OperationalCompatible ibrahimNavigationTime navigationOnly = ⊤
OperationalCompatible ibrahimNavigationTime structuralConsumerCandidate = ⊥
OperationalCompatible ibrahimNavigationTime sameObjectConsumer = ⊥
OperationalCompatible ibrahimNavigationTime validatedConsumer = ⊥
OperationalCompatible dashiStructuralBridgeTime navigationOnly = ⊤
OperationalCompatible dashiStructuralBridgeTime structuralConsumerCandidate = ⊤
OperationalCompatible dashiStructuralBridgeTime sameObjectConsumer = ⊥
OperationalCompatible dashiStructuralBridgeTime validatedConsumer = ⊥
OperationalCompatible sameObjectAdmissionTime navigationOnly = ⊤
OperationalCompatible sameObjectAdmissionTime structuralConsumerCandidate = ⊤
OperationalCompatible sameObjectAdmissionTime sameObjectConsumer = ⊤
OperationalCompatible sameObjectAdmissionTime validatedConsumer = ⊥
OperationalCompatible validatedConsumerTime navigationOnly = ⊤
OperationalCompatible validatedConsumerTime structuralConsumerCandidate = ⊤
OperationalCompatible validatedConsumerTime sameObjectConsumer = ⊤
OperationalCompatible validatedConsumerTime validatedConsumer = ⊤

operationalTemporalSystem : Temporal.TemporalEvidenceSystem
operationalTemporalSystem = record
  { Time = OperationalTime
  ; Interpretation = OperationalInterpretation
  ; Compatible = OperationalCompatible
  ; Summary = OperationalSummary
  ; summarize = λ _ → operationalFrontierOpen
  ; timeReference = λ
      { ibrahimNavigationTime → "Ibrahim paper-owned first-link navigation edges, DOI 10.1016/j.jocs.2016.12.001"
      ; dashiStructuralBridgeTime → "current DASHI fruit/LES and rail/chemical-logistics cross-pollination"
      ; sameObjectAdmissionTime → "future concrete shipment or fruit-output same-object admission"
      ; validatedConsumerTime → "future held-out/validation receipt"
      }
  }

currentOperationalCandidate : Temporal.EvidenceFibre operationalTemporalSystem dashiStructuralBridgeTime
currentOperationalCandidate = Temporal.liveInterpretationAt structuralConsumerCandidate tt

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data TrainCreatesRailShipment : Set where
data RailCreatesChemicalMaterial : Set where
data FruitCreatesMeasuredOutput : Set where
data SPACCreatesFruitCausalEffect : Set where
data QidCreatesSameObjectAdmission : Set where

trainDoesNotCreateRailShipment : TrainCreatesRailShipment → ⊥
trainDoesNotCreateRailShipment ()

railDoesNotCreateChemicalMaterial : RailCreatesChemicalMaterial → ⊥
railDoesNotCreateChemicalMaterial ()

fruitDoesNotCreateMeasuredOutput : FruitCreatesMeasuredOutput → ⊥
fruitDoesNotCreateMeasuredOutput ()

spacDoesNotCreateFruitCausalEffect : SPACCreatesFruitCausalEffect → ⊥
spacDoesNotCreateFruitCausalEffect ()

qidDoesNotCreateSameObjectAdmission : QidCreatesSameObjectAdmission → ⊥
qidDoesNotCreateSameObjectAdmission ()

crossDomainBoundary : Cross.IbrahimOracleCrossDomainBoundary
crossDomainBoundary = Cross.canonicalIbrahimOracleCrossDomainBoundary

logisticsBoundary : Logistics.ChemicalManufacturingInventoryLogisticsBoundary
logisticsBoundary = Logistics.canonicalChemicalManufacturingInventoryLogisticsBoundary

spacBoundary : SPAC.SPACBoundary
spacBoundary = SPAC.canonicalSPACBoundary

record FruitRailOperationalBoundary : Set where
  constructor fruit-rail-operational-boundary
  field
    ibrahimDOIRetained : Bool
    qidsRetainedAsIdentityOnly : Bool
    unresolvedDeweyRemainsUnresolved : Bool
    railReusesExistingNetworkLeg : Bool
    fruitReusesExistingSPACRealization : Bool
    sameObjectAdmissionRequired : Bool
    validationStillRequired : Bool
    navigationCreatesMechanism : Bool
open FruitRailOperationalBoundary public

canonicalFruitRailOperationalBoundary : FruitRailOperationalBoundary
canonicalFruitRailOperationalBoundary =
  fruit-rail-operational-boundary true true true true true true true false
