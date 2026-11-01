module DASHI.Physics.Optics.AsphericSagSurfaceNormalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Rotationally symmetric aspheric optics are commonly described by a base
-- conic sag plus higher even-order polynomial terms.  This module retains the
-- exact sag law only as a supplied receipt and exposes the derivative/normal
-- seam needed by downstream ray mapping.  It is not a surface-fitting or
-- manufacturing solver.
------------------------------------------------------------------------

asphericSagAuthority : String
asphericSagAuthority =
  "Ruediger Paschotta, RP Photonics Encyclopedia, Aspheric Optics, DOI 10.61835/x7h"

record AsphericSagAlgebra (Scalar : Set) : Set₁ where
  constructor aspheric-sag-algebra
  field
    zero one : Scalar
    add subtract multiply divide : Scalar → Scalar → Scalar
    negate sqrt : Scalar → Scalar
    square fourth sixth eighth : Scalar → Scalar

open AsphericSagAlgebra public

record RotationalAsphereSagReceipt
    {Scalar : Set}
    (algebra : AsphericSagAlgebra Scalar) : Set where
  constructor rotational-asphere-sag-receipt
  field
    radialCoordinate : Scalar
    curvature : Scalar
    conicConstant : Scalar
    fourthOrderCoefficient : Scalar
    sixthOrderCoefficient : Scalar
    eighthOrderCoefficient : Scalar
    sag : Scalar

    baseConicDenominator : Scalar
    denominatorLaw :
      baseConicDenominator
      ≡ add algebra
          (one algebra)
          (sqrt algebra
            (subtract algebra
              (one algebra)
              (multiply algebra
                (add algebra (one algebra) conicConstant)
                (multiply algebra
                  (square algebra curvature)
                  (square algebra radialCoordinate)))))

    sagLaw :
      sag
      ≡ add algebra
          (divide algebra
            (multiply algebra curvature (square algebra radialCoordinate))
            baseConicDenominator)
          (add algebra
            (multiply algebra fourthOrderCoefficient (fourth algebra radialCoordinate))
            (add algebra
              (multiply algebra sixthOrderCoefficient (sixth algebra radialCoordinate))
              (multiply algebra eighthOrderCoefficient (eighth algebra radialCoordinate))))

open RotationalAsphereSagReceipt public

record AsphereNormalReceipt
    {Scalar Normal : Set}
    {algebra : AsphericSagAlgebra Scalar}
    (surface : RotationalAsphereSagReceipt algebra) : Set₁ where
  constructor asphere-normal-receipt
  field
    radialDerivative : Scalar
    derivativeAuthority : String
    normalFromDerivative : Scalar → Normal
    surfaceNormal : Normal
    normalLaw : surfaceNormal ≡ normalFromDerivative radialDerivative

open AsphereNormalReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SagReceiptDeterminesManufacturableSurface : Set where
sagReceiptDoesNotDetermineManufacturableSurface :
  SagReceiptDeterminesManufacturableSurface → ⊥
sagReceiptDoesNotDetermineManufacturableSurface ()

data AsphereNormalDeterminesCaustic : Set where
asphereNormalDoesNotDetermineCaustic : AsphereNormalDeterminesCaustic → ⊥
asphereNormalDoesNotDetermineCaustic ()
