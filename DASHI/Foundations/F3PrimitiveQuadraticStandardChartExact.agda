module DASHI.Foundations.F3PrimitiveQuadraticStandardChartExact where

------------------------------------------------------------------------
-- EXPLICIT FIVE-COORDINATE CHART FOR THE PRIMITIVE EXTERIOR SQUARE
--
-- DASHI CONTRIBUTION
--
-- Local Python enumeration found the invertible F3-linear coordinate change
-- below.  This owner records the literal forward/inverse formulae and keeps
-- their full kernel proof as an explicit recognition receipt rather than
-- silently treating a computational observation as an Agda theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Add
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Mul
import DASHI.Foundations.F3SymplecticFourExteriorSquareExact as Exterior

infixl 6 _+₃_ _-₃_
infixl 7 _*₃_

_+₃_ : Trit → Trit → Trit
_+₃_ = Add._+3_

_*₃_ : Trit → Trit → Trit
_*₃_ = Mul._*3_

_-₃_ : Trit → Trit → Trit
a -₃ b = a +₃ Add.negate3 b

record Standard5 : Set where
  constructor standard5
  field
    z0 z1 z2 z3 z4 : Trit
open Standard5 public

standardQuadratic : Standard5 → Trit
standardQuadratic z =
  (z0 z *₃ z0 z) +₃
  ((z1 z *₃ z1 z) +₃
   ((z2 z *₃ z2 z) +₃
    ((z3 z *₃ z3 z) +₃ (z4 z *₃ z4 z))))

-- Matrix over F3:
-- [0 0 2 1 0]
-- [0 2 0 0 2]
-- [0 1 1 1 2]
-- [0 1 2 2 2]
-- [1 0 0 0 0]
primitiveToStandard : Exterior.Primitive5 → Standard5
primitiveToStandard p =
  standard5
    (Exterior.q12 p -₃ Exterior.q03 p)
    ((Add.negate3 (Exterior.q02 p)) -₃ Exterior.q13 p)
    (((Exterior.q02 p +₃ Exterior.q03 p) +₃ Exterior.q12 p) -₃ Exterior.q13 p)
    (((Exterior.q02 p -₃ Exterior.q03 p) -₃ Exterior.q12 p) -₃ Exterior.q13 p)
    (Exterior.q01 p)

-- Inverse matrix over F3:
-- [0 0 0 0 1]
-- [0 1 1 1 0]
-- [1 0 1 2 0]
-- [2 0 1 2 0]
-- [0 1 2 2 0]
standardToPrimitive : Standard5 → Exterior.Primitive5
standardToPrimitive z =
  Exterior.primitive5
    (z4 z)
    ((z1 z +₃ z2 z) +₃ z3 z)
    ((z0 z +₃ z2 z) -₃ z3 z)
    ((z2 z -₃ z0 z) -₃ z3 z)
    ((z1 z -₃ z2 z) -₃ z3 z)

record PrimitiveStandardIsometryReceipt : Set where
  field
    primitiveRoundTrip :
      (p : Exterior.Primitive5) →
      standardToPrimitive (primitiveToStandard p) ≡ p
    standardRoundTrip :
      (z : Standard5) →
      primitiveToStandard (standardToPrimitive z) ≡ z
    quadraticCompatibility :
      (p : Exterior.Primitive5) →
      standardQuadratic (primitiveToStandard p)
      ≡ Add.negate3 (Exterior.primitiveQuadratic p)
open PrimitiveStandardIsometryReceipt public

record PrimitiveStandardChartBoundary : Set where
  constructor primitive-standard-chart-boundary
  field
    explicitForwardMatrixRecorded : Bool
    explicitInverseMatrixRecorded : Bool
    determinantNonzeroExternallyChecked : Bool
    roundTripReceiptTyped : Bool
    quadraticCompatibilityReceiptTyped : Bool
    canonicalReceiptInhabitedInThisOwner : Bool
open PrimitiveStandardChartBoundary public

canonicalPrimitiveStandardChartBoundary : PrimitiveStandardChartBoundary
canonicalPrimitiveStandardChartBoundary =
  primitive-standard-chart-boundary
    true true true true true false
