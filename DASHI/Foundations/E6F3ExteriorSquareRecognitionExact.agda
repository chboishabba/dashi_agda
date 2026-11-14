module DASHI.Foundations.E6F3ExteriorSquareRecognitionExact where

------------------------------------------------------------------------
-- E6 MOD-3 / F3^5 RECOGNITION SOCKET THROUGH THE PRIMITIVE EXTERIOR SQUARE
--
-- DASHI CONTRIBUTION
--
-- This file does not infer E6 from 72, 80, 243 or 51840.  It states the exact
-- same-object/action data required to weld an actual E6 mod-3 quadratic model
-- to the primitive exterior-square construction on F3^4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.F3SymplecticFourExteriorSquareExact as Exterior
import DASHI.Foundations.F3PrimitiveQuadraticStandardChartExact as Chart

record E6Mod3QuadraticModel : Set₁ where
  field
    Actor Root : Set
    act5 : Actor → Chart.Standard5 → Chart.Standard5
    rootVector : Root → Chart.Standard5
    rootNormTwo : Root → Set
    rootAction : Actor → Root → Root
    rootVectorIntertwines :
      (g : Actor) → (r : Root) →
      rootVector (rootAction g r) ≡ act5 g (rootVector r)
open E6Mod3QuadraticModel public

record PGSp4WE6Recognition (E6 : E6Mod3QuadraticModel) : Set₁ where
  field
    PGSpActor : Set
    lagAction : PGSpActor → Exterior.PrimitiveNullPoint → Exterior.PrimitiveNullPoint
    toWeyl : PGSpActor → Actor E6
    fromWeyl : Actor E6 → PGSpActor
    fromAfterToActor : (g : PGSpActor) → fromWeyl (toWeyl g) ≡ g
    toAfterFromActor : (g : Actor E6) → toWeyl (fromWeyl g) ≡ g
    nullToStandard : Exterior.PrimitiveNullPoint → Chart.Standard5
    nullActionIntertwines :
      (g : PGSpActor) → (p : Exterior.PrimitiveNullPoint) →
      nullToStandard (lagAction g p)
      ≡ act5 E6 (toWeyl g) (nullToStandard p)
open PGSp4WE6Recognition public

record E6RootLineGraphReceipt : Set₁ where
  field
    RootLine : Set
    adjacent : RootLine → RootLine → Set
    vertexCount : Set
    degree15 : Set
    adjacentCommon6 : Set
    nonAdjacentCommon6 : Set

record E6ExteriorSquareBoundary : Set where
  constructor e6-exterior-square-boundary
  field
    e6Mod3QuadraticModelTyped : Bool
    PGSp4WE6SameActionRecognitionTyped : Bool
    rootLineSRG361566ReceiptTyped : Bool
    finiteLocalComputationFound51840MatrixEquality : Bool
    finiteLocalComputationFoundNullOrbit80 : Bool
    finiteLocalComputationFoundRootOrbit72 : Bool
    matrixEqualityKernelProofInThisOwner : Bool
    rawT4PuncturePromotedToNullOrbit : Bool
open E6ExteriorSquareBoundary public

canonicalE6ExteriorSquareBoundary : E6ExteriorSquareBoundary
canonicalE6ExteriorSquareBoundary =
  e6-exterior-square-boundary
    true true true
    true true true
    false false
