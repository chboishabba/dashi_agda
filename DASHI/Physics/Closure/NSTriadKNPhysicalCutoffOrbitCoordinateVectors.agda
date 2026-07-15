module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitCoordinateVectors where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNFiniteCoordinateAlgebraCore as Finite
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitModeSupport as Support

------------------------------------------------------------------------
-- Concrete orbit-carrier vectors.  The source and target coordinates come
-- from the canonical swap quotient, so off-diagonal input order cannot
-- create a second physical edge occurrence.
------------------------------------------------------------------------

PhysicalCutoffOrbitVector :
  (S : Scalar.ExactOrderedScalar) → (N R : Nat) → Set
PhysicalCutoffOrbitVector S N R =
  Support.physicalCutoffOrbitModeCoordinate N R → Scalar.Scalar S

orbitZeroVector :
  (S : Scalar.ExactOrderedScalar) → (N R : Nat) →
  PhysicalCutoffOrbitVector S N R
orbitZeroVector S N R _ = Scalar.zero S

orbitPointwiseAdd :
  (S : Scalar.ExactOrderedScalar) → {N R : Nat} →
  PhysicalCutoffOrbitVector S N R → PhysicalCutoffOrbitVector S N R →
  PhysicalCutoffOrbitVector S N R
orbitPointwiseAdd S x y i = Scalar._+_ S (x i) (y i)

orbitBasisVector :
  (S : Scalar.ExactOrderedScalar) → {N R : Nat} →
  Support.physicalCutoffOrbitModeCoordinate N R →
  PhysicalCutoffOrbitVector S N R
orbitBasisVector S i j = Finite.coordinateBasis S i j

orbitPairIncidenceVector :
  (S : Scalar.ExactOrderedScalar) → (N R : Nat) →
  Support.OrbitPhysicalCutoffIncidence N R →
  PhysicalCutoffOrbitVector S N R
orbitPairIncidenceVector S N R r i =
  Scalar._+_ S
    (orbitBasisVector S {N = N} {R = R}
      (Support.orbitSourceCoordinate N R r) i)
    (Scalar.neg S
      (orbitBasisVector S {N = N} {R = R}
        (Support.orbitTargetCoordinate N R r) i))
