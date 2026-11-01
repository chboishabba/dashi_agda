module DASHI.Physics.QuantumVacuum.CasimirCoefficient720To240CompilerExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COEFFICIENT COMPILER SKELETON
--
-- The analytic theorem must produce the energy coefficient 720 on the SAME
-- renormalised observable.  Once a calculus receipt establishes
--   d(d^-3)/dd = -3 d^-4,
-- the numerical passage 720 -> 240 is arithmetic compiler output.
------------------------------------------------------------------------

threeTimes240Is720 : 3 * 240 ≡ 720
threeTimes240Is720 = refl

record InverseCubeDerivativeReceipt : Set₁ where
  field
    Scalar : Set
    Separation : Set
    energyObservable : Separation → Scalar
    pressureObservable : Separation → Scalar

    Coefficient : Set
    energyCoefficient : Coefficient
    pressureCoefficient : Coefficient

    sameObservableDifferentiated : Set
    inverseCubeDerivativeFactorThree : Set
    coefficientTransport : Set

open InverseCubeDerivativeReceipt public

------------------------------------------------------------------------
-- Firewall: the arithmetic identity alone is not a derivative theorem.
------------------------------------------------------------------------

data Arithmetic720To240IsDerivativePermission : Set where

arithmeticAloneCannotSupplyDerivative :
  Arithmetic720To240IsDerivativePermission → ⊥
arithmeticAloneCannotSupplyDerivative ()

record CoefficientCompilerStatus : Set where
  field
    arithmetic720To240Owned : Bool
    sameObjectDerivativeClosed : Bool
    pressurePhysicalWeldClosed : Bool

    arithmetic720To240OwnedIsTrue : arithmetic720To240Owned ≡ true
    sameObjectDerivativeClosedIsFalse : sameObjectDerivativeClosed ≡ false
    pressurePhysicalWeldClosedIsFalse : pressurePhysicalWeldClosed ≡ false

canonicalCoefficientCompilerStatus : CoefficientCompilerStatus
canonicalCoefficientCompilerStatus = record
  { arithmetic720To240Owned = true
  ; sameObjectDerivativeClosed = false
  ; pressurePhysicalWeldClosed = false
  ; arithmetic720To240OwnedIsTrue = refl
  ; sameObjectDerivativeClosedIsFalse = refl
  ; pressurePhysicalWeldClosedIsFalse = refl
  }
