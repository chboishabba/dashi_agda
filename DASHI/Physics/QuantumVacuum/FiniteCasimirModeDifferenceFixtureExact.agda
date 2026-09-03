module DASHI.Physics.QuantumVacuum.FiniteCasimirModeDifferenceFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.HarmonicOscillatorDoubledEnergyExact as Osc

------------------------------------------------------------------------
-- FINITE SAME-FIELD / DIFFERENT-BOUNDARY COMPUTATIONAL FIXTURE
------------------------------------------------------------------------

data FieldToken : Set where
  electromagneticField : FieldToken

data BoundaryToken : Set where
  freeBoundary : BoundaryToken
  cavityBoundary : BoundaryToken

record FiniteBoundaryModeFabric : Set where
  field
    field : FieldToken
    boundary : BoundaryToken
    frequencies : List Nat
    reading : String

open FiniteBoundaryModeFabric public

modewiseDoubledGroundEnergy : Nat → Nat
modewiseDoubledGroundEnergy omega = Osc.doubledEnergy omega 0

modewiseDoubledGroundEnergyIsFrequency :
  (omega : Nat) →
  modewiseDoubledGroundEnergy omega ≡ omega
modewiseDoubledGroundEnergyIsFrequency omega =
  Osc.groundDoubledEnergy omega

sumModewiseDoubledGroundEnergy : List Nat → Nat
sumModewiseDoubledGroundEnergy [] = 0
sumModewiseDoubledGroundEnergy (omega ∷ rest) =
  modewiseDoubledGroundEnergy omega + sumModewiseDoubledGroundEnergy rest

doubledVacuumGroundAggregate : FiniteBoundaryModeFabric → Nat
doubledVacuumGroundAggregate fabric =
  sumModewiseDoubledGroundEnergy (frequencies fabric)

freeFabric : FiniteBoundaryModeFabric
freeFabric =
  record
    { field = electromagneticField
    ; boundary = freeBoundary
    ; frequencies = 1 ∷ 2 ∷ 3 ∷ []
    ; reading = "Finite reference fabric with three admitted mode-frequency tokens."
    }

cavityFabric : FiniteBoundaryModeFabric
cavityFabric =
  record
    { field = electromagneticField
    ; boundary = cavityBoundary
    ; frequencies = 1 ∷ 3 ∷ []
    ; reading = "Finite cavity fabric with the middle reference mode removed."
    }

sameField : field freeFabric ≡ field cavityFabric
sameField = refl

freeDoubledVacuumGroundAggregate :
  doubledVacuumGroundAggregate freeFabric ≡ 6
freeDoubledVacuumGroundAggregate = refl

cavityDoubledVacuumGroundAggregate :
  doubledVacuumGroundAggregate cavityFabric ≡ 4
cavityDoubledVacuumGroundAggregate = refl

record DifferentNat (left right : Nat) : Set where
  constructor differentNat
  field
    distinguish : left ≡ right → ⊥

open DifferentNat public

sixNotFour : 6 ≡ 4 → ⊥
sixNotFour ()

aggregateDifference :
  DifferentNat
    (doubledVacuumGroundAggregate freeFabric)
    (doubledVacuumGroundAggregate cavityFabric)
aggregateDifference = differentNat sixNotFour

record FieldIdentityDoesNotDetermineVacuumAggregate : Set where
  field
    left right : FiniteBoundaryModeFabric
    sameFieldCoordinate : field left ≡ field right
    aggregateSeparates :
      DifferentNat
        (doubledVacuumGroundAggregate left)
        (doubledVacuumGroundAggregate right)

open FieldIdentityDoesNotDetermineVacuumAggregate public

finiteNonFactorabilityWitness :
  FieldIdentityDoesNotDetermineVacuumAggregate
finiteNonFactorabilityWitness =
  record
    { left = freeFabric
    ; right = cavityFabric
    ; sameFieldCoordinate = refl
    ; aggregateSeparates = aggregateDifference
    }

boundaryChanged : BoundaryToken → BoundaryToken → Set
boundaryChanged freeBoundary cavityBoundary = ⊤
boundaryChanged cavityBoundary freeBoundary = ⊤
boundaryChanged freeBoundary freeBoundary = ⊥
boundaryChanged cavityBoundary cavityBoundary = ⊥

freeToCavityBoundaryChanged :
  boundaryChanged (boundary freeFabric) (boundary cavityFabric)
freeToCavityBoundaryChanged = tt

record FiniteRetopologyReceipt : Set where
  field
    initial final : FiniteBoundaryModeFabric
    sameFieldCoordinate : field initial ≡ field final
    boundaryDifference : boundaryChanged (boundary initial) (boundary final)
    aggregateDifference :
      DifferentNat
        (doubledVacuumGroundAggregate initial)
        (doubledVacuumGroundAggregate final)

open FiniteRetopologyReceipt public

finiteRetopologyReceipt : FiniteRetopologyReceipt
finiteRetopologyReceipt =
  record
    { initial = freeFabric
    ; final = cavityFabric
    ; sameFieldCoordinate = refl
    ; boundaryDifference = tt
    ; aggregateDifference = aggregateDifference
    }

record FixtureAuthorityBoundary : Set where
  field
    physicalParallelPlateSpectrumClaimed : Bool
    renormalisedCasimirObservableClaimed : Bool
    closedExtractionCycleClaimed : Bool

    physicalParallelPlateSpectrumClaimedIsFalse :
      physicalParallelPlateSpectrumClaimed ≡ false
    renormalisedCasimirObservableClaimedIsFalse :
      renormalisedCasimirObservableClaimed ≡ false
    closedExtractionCycleClaimedIsFalse :
      closedExtractionCycleClaimed ≡ false

open FixtureAuthorityBoundary public

canonicalFixtureAuthorityBoundary : FixtureAuthorityBoundary
canonicalFixtureAuthorityBoundary =
  record
    { physicalParallelPlateSpectrumClaimed = false
    ; renormalisedCasimirObservableClaimed = false
    ; closedExtractionCycleClaimed = false
    ; physicalParallelPlateSpectrumClaimedIsFalse = refl
    ; renormalisedCasimirObservableClaimedIsFalse = refl
    ; closedExtractionCycleClaimedIsFalse = refl
    }
