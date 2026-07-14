module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffCoordinateVectors where

open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNFiniteCoordinateAlgebraCore as Finite
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector

------------------------------------------------------------------------
-- Concrete coordinate vectors on the exact finite cutoff mode carrier.
--
-- The vector carrier is already available from the finite normalized support:
-- it is the function space from its `Fin length` coordinates into the chosen
-- scalar.  No inner-product law is asserted in this module; that requires the
-- additive/multiplicative scalar laws made explicit in the next layer.
------------------------------------------------------------------------

PhysicalCutoffVector :
  (S : Scalar.ExactOrderedScalar) →
  (N R : Nat) → Sector.ExactOutputRetainedSectorLaw N R → Set
PhysicalCutoffVector S N R sector =
  Support.physicalCutoffModeCoordinate N R sector → Scalar.Scalar S

zeroVector :
  (S : Scalar.ExactOrderedScalar) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  PhysicalCutoffVector S N R sector
zeroVector S N R sector _ = Scalar.zero S

pointwiseAdd :
  (S : Scalar.ExactOrderedScalar) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  PhysicalCutoffVector S N R sector →
  PhysicalCutoffVector S N R sector →
  PhysicalCutoffVector S N R sector
pointwiseAdd S x y i = Scalar._+_ S (x i) (y i)

pointwiseNeg :
  (S : Scalar.ExactOrderedScalar) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  PhysicalCutoffVector S N R sector →
  PhysicalCutoffVector S N R sector
pointwiseNeg S x i = Scalar.neg S (x i)

pointwiseDifference :
  (S : Scalar.ExactOrderedScalar) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  PhysicalCutoffVector S N R sector →
  PhysicalCutoffVector S N R sector →
  PhysicalCutoffVector S N R sector
pointwiseDifference S {N} {R} {sector} x y =
  pointwiseAdd S {N} {R} {sector} x
    (pointwiseNeg S {N} {R} {sector} y)

basisVector :
  (S : Scalar.ExactOrderedScalar) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  Support.physicalCutoffModeCoordinate N R sector →
  PhysicalCutoffVector S N R sector
basisVector S i j = Finite.coordinateBasis S i j

-- This is the exact incidence vector fixed by the physical convention:
-- b_r = e_source(r) - e_target(r).  The incidence carries a membership proof
-- in the cutoff list, so both coordinates are total on the shared carrier.
physicalPairIncidenceVector :
  (S : Scalar.ExactOrderedScalar) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  Support.PhysicalCutoffIncidence N R sector →
  PhysicalCutoffVector S N R sector
physicalPairIncidenceVector S N R sector r =
  pointwiseDifference S {N} {R} {sector}
    (basisVector S {N} {R} {sector} (Support.sourceCoordinate N R sector r))
    (basisVector S {N} {R} {sector} (Support.targetCoordinate N R sector r))
