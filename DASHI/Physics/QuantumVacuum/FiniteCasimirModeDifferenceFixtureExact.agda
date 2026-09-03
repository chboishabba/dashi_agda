module DASHI.Physics.QuantumVacuum.FiniteCasimirModeDifferenceFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.HarmonicOscillatorDoubledEnergyExact as Osc

------------------------------------------------------------------------
-- FINITE SAME-FIELD / DIFFERENT-BOUNDARY COMPUTATIONAL FIXTURE
--
-- This is deliberately a finite toy witness.  It does not claim that these
-- three frequencies are a physical parallel-plate spectrum.  Its role is to
-- prove, by reduction, that once the boundary coordinate changes the admitted
-- mode list can change and so can the aggregate zero-point coordinate.
--
-- In doubled-energy units each ground mode contributes exactly omega:
--
--   2 E0(omega) = omega.
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

sumNat : List Nat → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

doubledVacuumGroundAggregate : FiniteBoundaryModeFabric → Nat
doubledVacuumGroundAggregate fabric =
  sumNat (frequencies fabric)

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

------------------------------------------------------------------------
-- Explicit non-factorability witness.
--
-- The field chart is identical, but the boundary chart distinguishes the two
-- hypervoxels and their finite zero-point aggregates differ.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Boundary retopology is not ground-state-alone extraction.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Authority boundary: this fixture is only a computational witness that mode
-- admission and raw finite zero-point coordinates can depend on boundary data.
-- It is not a physical Casimir spectrum, a renormalised observable, or a
-- closed energy cycle.
------------------------------------------------------------------------

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
