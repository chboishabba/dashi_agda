module DASHI.Wikimedia.IbrahimDisposableVapeChemicalUniverseObserverParetoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimDisposableVapeUnknownIngredientFibreExact as Fibre
import DASHI.Wikimedia.IbrahimDisposableVapeChemicalCensusExperimentExact as Census
import DASHI.Wikimedia.IbrahimDisposableVapeUnknownFeatureLedgerExact as Ledger

------------------------------------------------------------------------
-- CHEMICAL-UNIVERSE OBSERVER PARETO
--
-- Consumer: "what chemicals is this disposable capable of delivering over its
-- life?"  No single analytical modality is promoted to a complete observer.
------------------------------------------------------------------------

data ObserverModality : Set where
  labelAudit : ObserverModality
  targetedGCMS : ObserverModality
  targetedLCMS : ObserverModality
  nonTargetGCHRMS : ObserverModality
  nonTargetLCHRMS : ObserverModality
  carbonylAssay : ObserverModality
  elementalICPMS : ObserverModality
  deviceMaterialAnalysis : ObserverModality

record ObserverCapability : Set where
  constructor observer-capability
  field
    modality : ObserverModality
    carrierSolvents : Bool
    nicotineAndAcids : Bool
    volatileFlavoursCoolants : Bool
    semipolarNonTarget : Bool
    nonvolatileNonTarget : Bool
    reactiveCarbonyls : Bool
    metalsMetalloids : Bool
    solidDeviceMaterials : Bool
    unidentifiedFeatureRetention : Bool
    quantitativeTargeted : Bool
    burden : Nat
open ObserverCapability public

labelCapability : ObserverCapability
labelCapability = observer-capability labelAudit false false false false false false false false false false 0

targetedGCCapability : ObserverCapability
targetedGCCapability = observer-capability targetedGCMS true true true false false false false false false true 1

targetedLCCapability : ObserverCapability
targetedLCCapability = observer-capability targetedLCMS false true true false false false false false false true 1

nonTargetGCCapability : ObserverCapability
nonTargetGCCapability = observer-capability nonTargetGCHRMS true true true true false false false false true false 3

nonTargetLCCapability : ObserverCapability
nonTargetLCCapability = observer-capability nonTargetLCHRMS false true true false true false false false true false 3

carbonylCapability : ObserverCapability
carbonylCapability = observer-capability carbonylAssay false false false false false true false false false true 2

metalCapability : ObserverCapability
metalCapability = observer-capability elementalICPMS false false false false false false true false false true 2

materialCapability : ObserverCapability
materialCapability = observer-capability deviceMaterialAnalysis false false false false false false true true false false 3

------------------------------------------------------------------------
-- ADEQUACY PACKETS
------------------------------------------------------------------------

record ObserverPacket : Set where
  constructor observer-packet
  field
    name : String
    modalities : String
    answersVirginLiquidInventory : Bool
    answersAerosolOrganicInventory : Bool
    answersReactiveCarbonyls : Bool
    answersMetals : Bool
    answersDeviceOrigin : Bool
    retainsUnknownFeatures : Bool
    burden : Nat
open ObserverPacket public

cheapTargetedPacket : ObserverPacket
cheapTargetedPacket = observer-packet
  "targeted liquid screen"
  "targeted GC-MS + targeted LC-MS"
  true false false false false false 2

organicDiscoveryPacket : ObserverPacket
organicDiscoveryPacket = observer-packet
  "organic discovery"
  "targeted GC/LC + non-target GC-HRMS + non-target LC-HRMS"
  true true false false false true 8

wholeAerosolPacket : ObserverPacket
wholeAerosolPacket = observer-packet
  "whole aerosol chemistry"
  "organic discovery + targeted carbonyl assay + ICP-MS metals"
  true true true true false true 12

originResolvingPacket : ObserverPacket
originResolvingPacket = observer-packet
  "origin-resolving life-cycle census"
  "whole aerosol chemistry + device material analysis + early/mid/late stage sampling"
  true true true true true true 16

------------------------------------------------------------------------
-- COLLISIONS THAT FORCE ESCALATION
------------------------------------------------------------------------

record ObserverCollision : Set where
  constructor observer-collision
  field
    coarsePacket : String
    worldA : String
    worldB : String
    sameCoarseObservation : Bool
    differentConsumerAnswer : Bool
    missingModality : String
open ObserverCollision public

targetedUnknownCollision : ObserverCollision
targetedUnknownCollision = observer-collision
  "targeted liquid screen"
  "only predeclared analytes present"
  "off-panel reaction product / flavour adduct / unexpected additive also present"
  true true
  "non-target GC-HRMS and/or LC-HRMS"

liquidEmissionCollision : ObserverCollision
liquidEmissionCollision = observer-collision
  "virgin-liquid organic discovery"
  "aerosol mirrors liquid"
  "heating creates carbonyls / decomposition products or enriches features"
  true true
  "generated-aerosol analysis including dedicated carbonyl observer"

organicMetalCollision : ObserverCollision
organicMetalCollision = observer-collision
  "organic aerosol chemistry"
  "device contributes negligible metal burden"
  "coil/solder/contact materials contribute aerosol metals"
  true true
  "ICP-MS aerosol metals plus device-material analysis"

wholeLifeCollision : ObserverCollision
wholeLifeCollision = observer-collision
  "early-life whole-aerosol packet"
  "emissions stable over device life"
  "used-fluid chemistry / corrosion / coil aging changes later emissions"
  true true
  "same-device early/mid/late census"

------------------------------------------------------------------------
-- ADAPTIVE PARETO POLICY
------------------------------------------------------------------------

record AdaptiveObserverPolicy : Set where
  constructor adaptive-observer-policy
  field
    start : String
    firstEscalation : String
    secondEscalation : String
    thirdEscalation : String
    stopRule : String
    globalBestObserverClaimed : Bool
open AdaptiveObserverPolicy public

canonicalAdaptiveObserverPolicy : AdaptiveObserverPolicy
canonicalAdaptiveObserverPolicy = adaptive-observer-policy
  "label audit + targeted liquid screen"
  "if off-panel composition matters, add non-target GC/LC feature discovery"
  "if inhaled chemistry matters, add generated-aerosol non-target + carbonyl + metals"
  "if source/origin or whole-life exposure matters, add early/mid/late stage sampling plus device-material analysis"
  "stop only when the declared consumer factors through the retained observer; a finite method set never creates complete chemistry"
  false

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data OneInstrumentSeesWholeChemicalUniverse : Set where
data TargetedNegativeCreatesUnknownNegative : Set where
data OrganicScreenCreatesMetalAbsence : Set where
data EarlyAerosolCreatesWholeLifeExposure : Set where
data MaximalPacketCreatesScientificAuthority : Set where

oneInstrumentNotComplete : OneInstrumentSeesWholeChemicalUniverse → ⊥
oneInstrumentNotComplete ()

targetedNegativeNotUnknownNegative : TargetedNegativeCreatesUnknownNegative → ⊥
targetedNegativeNotUnknownNegative ()

organicNotMetalAbsence : OrganicScreenCreatesMetalAbsence → ⊥
organicNotMetalAbsence ()

earlyNotWholeLife : EarlyAerosolCreatesWholeLifeExposure → ⊥
earlyNotWholeLife ()

maximalPacketNotAuthority : MaximalPacketCreatesScientificAuthority → ⊥
maximalPacketNotAuthority ()

record ChemicalUniverseObserverBoundary : Set where
  constructor chemical-universe-observer-boundary
  field
    targetedObserverUseful : Bool
    nonTargetRequiredForUnknownConsumer : Bool
    aerosolRequiredForInhaledConsumer : Bool
    metalsNeedSeparateObserver : Bool
    materialsNeedSeparateObserver : Bool
    lifeCycleNeedsRepeatedStages : Bool
    finitePacketCreatesCompleteChemistry : Bool
open ChemicalUniverseObserverBoundary public

canonicalChemicalUniverseObserverBoundary : ChemicalUniverseObserverBoundary
canonicalChemicalUniverseObserverBoundary = chemical-universe-observer-boundary
  true true true true true true false
