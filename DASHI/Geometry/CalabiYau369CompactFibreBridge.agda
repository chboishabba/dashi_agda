module DASHI.Geometry.CalabiYau369CompactFibreBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.CalabiYau as CY
import DASHI.Geometry.ComplexManifold as CM

------------------------------------------------------------------------
-- Dimension reading: 3 extended real dimensions plus a Calabi-Yau threefold's
-- 3 complex = 6 real compact dimensions gives 9 spatial dimensions.
------------------------------------------------------------------------

record Dimension369 : Set where
  constructor dimension369
  field
    extendedRealDimension : Nat
    compactComplexDimension : Nat
    compactRealDimension : Nat
    totalSpatialDimension : Nat
    timeDimension : Nat
    spacetimeDimension : Nat

    extendedRealIsThree : extendedRealDimension ≡ 3
    compactComplexIsThree : compactComplexDimension ≡ 3
    compactRealIsTwiceComplex :
      compactRealDimension
        ≡ compactComplexDimension + compactComplexDimension
    totalSpatialIsBasePlusFibre :
      totalSpatialDimension
        ≡ extendedRealDimension + compactRealDimension
    timeIsOne : timeDimension ≡ 1
    spacetimeIsSpatialPlusTime :
      spacetimeDimension
        ≡ totalSpatialDimension + timeDimension

open Dimension369 public

canonicalDimension369 : Dimension369
canonicalDimension369 =
  dimension369 3 3 6 9 1 10 refl refl refl refl refl refl

------------------------------------------------------------------------
-- Bundle and effective-observable interfaces.  Fibre integration is an explicit
-- supplied operation; it is not manufactured from dimension counting.
------------------------------------------------------------------------

record BaseCompactFibreBundle
    (BasePoint InternalPoint TotalPoint : Set) : Set₁ where
  field
    includeFibre : BasePoint → InternalPoint → TotalPoint
    projectBase : TotalPoint → BasePoint

    projectionReturnsBase :
      ∀ base internal →
      projectBase (includeFibre base internal) ≡ base

    localProductStructure : Set

open BaseCompactFibreBundle public

record EffectiveFibreObservable
    (BasePoint InternalPoint Value : Set) : Set₁ where
  field
    fineField : BasePoint → InternalPoint → Value
    integrateInternalFibre :
      (BasePoint → InternalPoint → Value) →
      BasePoint →
      Value
    effectiveField : BasePoint → Value
    effectiveFieldIsFibreAggregation :
      effectiveField ≡ integrateInternalFibre fineField

open EffectiveFibreObservable public

record CalabiYau369Bridge
    (Point Coordinate RealScalar : Set)
    (Tangent : Point → Set)
    (IntegralCohomology2 TopForm : Set)
    (ExtendedPoint TotalPoint : Set) : Set₁ where
  field
    calabiYauAuthority :
      CY.CalabiYauAuthority
        Point Coordinate RealScalar Tangent IntegralCohomology2 TopForm

    dimensions : Dimension369

    calabiYauComplexDimensionMatchesThreefold :
      CM.complexDimension (CY.complexManifold calabiYauAuthority)
        ≡ compactComplexDimension dimensions

    spatialBundle :
      BaseCompactFibreBundle ExtendedPoint Point TotalPoint

    compactFibreReading : String

open CalabiYau369Bridge public

------------------------------------------------------------------------
-- Cardinality 3/6/9 and dimensional 3+6=9 are separate typed readings.
------------------------------------------------------------------------

data Reading369 : Set where
  finiteCarrierCardinalityReading : Reading369
  spatialDimensionReading : Reading369

record CalabiYau369Boundary : Set where
  constructor calabiYau369Boundary
  field
    additiveDimensionIdentityClosed : Bool
    multiplicativeSixReadingRecorded : Bool
    base369ProvesStringCompactification : Bool
    base369ProvesStringCompactificationIsFalse :
      base369ProvesStringCompactification ≡ false
    dimensionCountingSuppliesPhysicalCompactification : Bool
    dimensionCountingSuppliesPhysicalCompactificationIsFalse :
      dimensionCountingSuppliesPhysicalCompactification ≡ false

canonicalCalabiYau369Boundary : CalabiYau369Boundary
canonicalCalabiYau369Boundary =
  calabiYau369Boundary true true false refl false refl
