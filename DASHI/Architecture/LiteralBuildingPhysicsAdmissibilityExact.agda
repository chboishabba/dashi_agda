module DASHI.Architecture.LiteralBuildingPhysicsAdmissibilityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- LITERAL ARCHITECTURAL PHYSICS / LIFE-SAFETY SURFACE
------------------------------------------------------------------------

data BuildingSystem : Set where
  egress accessibility thermal daylight structure services occupancy : BuildingSystem

data Status : Set where
  passes fails : Status

record BuildingAssessment : Set where
  constructor buildingAssessment
  field status : BuildingSystem → Status

open BuildingAssessment public

locallyGoodButEgressFails : BuildingAssessment
locallyGoodButEgressFails = buildingAssessment assess
  where
  assess : BuildingSystem → Status
  assess egress = fails
  assess accessibility = passes
  assess thermal = passes
  assess daylight = passes
  assess structure = passes
  assess services = passes
  assess occupancy = passes

record WholeBuildingAdmissible (a : BuildingAssessment) : Set where
  constructor wholeBuildingAdmissible
  field
    egressPasses : status a egress ≡ passes
    accessibilityPasses : status a accessibility ≡ passes
    thermalPasses : status a thermal ≡ passes
    daylightPasses : status a daylight ≡ passes
    structurePasses : status a structure ≡ passes
    servicesPass : status a services ≡ passes
    occupancyPasses : status a occupancy ≡ passes

open WholeBuildingAdmissible public

oneFailedSubsystemBlocksWholeBuildingClosure :
  WholeBuildingAdmissible locallyGoodButEgressFails → ⊥
oneFailedSubsystemBlocksWholeBuildingClosure admissible = egressPasses admissible

data Opening : Set where opening : Opening
data SafeEgress : Opening → Set where

data GeometricConnection : Set where geometricConnection : GeometricConnection
data AccessibleConnection : GeometricConnection → Set where

openingDoesNotAutomaticallyCreateSafeEgress : SafeEgress opening → ⊥
openingDoesNotAutomaticallyCreateSafeEgress ()

connectionDoesNotAutomaticallyCreateAccessibility :
  AccessibleConnection geometricConnection → ⊥
connectionDoesNotAutomaticallyCreateAccessibility ()

record BuildingPhysicsBoundary : Set where
  constructor buildingPhysicsBoundary
  field
    openingEqualsSafeEgress : Bool
    openingEqualsSafeEgressIsFalse : openingEqualsSafeEgress ≡ false
    connectivityEqualsAccessibility : Bool
    connectivityEqualsAccessibilityIsFalse : connectivityEqualsAccessibility ≡ false
    subsystemChecksMayBeSilentlyAggregated : Bool
    subsystemChecksMayBeSilentlyAggregatedIsFalse :
      subsystemChecksMayBeSilentlyAggregated ≡ false

canonicalBuildingPhysicsBoundary : BuildingPhysicsBoundary
canonicalBuildingPhysicsBoundary = buildingPhysicsBoundary false refl false refl false refl
