module DASHI.Physics.Closure.NSTriadKNFinitePVProjectorIncrementRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact finite algebra behind the principal-value increment route.
-- A singular-integral kernel with zero spherical/mean mass permits one to
-- subtract the base value before estimating:
--
--   sum_y K_y P_y
--     = sum_y K_y (P_y - P_x)
--
-- whenever sum_y K_y = 0.
--
-- Here P_y is the rank-one vorticity-line projector from Round 37.  The proof
-- is coordinatewise and exact over rationals, with no norm estimate hidden in
-- an authority record.  Combined with
--
--   ||P_y-P_x||_F^2 = 2 Theta(x,y),
--
-- this is the finite skeleton of the surviving HH-good mechanism.  The open
-- A3 theorem is now sharply isolated: prove that the *literal periodic strain
-- kernel* has the required PV cancellation and that its analytic weighted
-- increment integral is controlled on the physical trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact as Projector

record KernelDirectionSample : Set where
  constructor kernel-direction-sample
  field
    weight : ℚ
    direction : Projector.UnitDirection

open KernelDirectionSample public

sumWeights : List KernelDirectionSample → ℚ
sumWeights [] = 0ℚ
sumWeights (sample ∷ rest) = weight sample + sumWeights rest

weightedCoordinate :
  (Matrix.Matrix3 → ℚ) → List KernelDirectionSample → ℚ
weightedCoordinate coordinate [] = 0ℚ
weightedCoordinate coordinate (sample ∷ rest) =
  weight sample * coordinate
    (Projector.rankOneProjector (Projector.vector (direction sample)))
  + weightedCoordinate coordinate rest

weightedIncrementCoordinate :
  (Matrix.Matrix3 → ℚ) →
  Projector.UnitDirection →
  List KernelDirectionSample → ℚ
weightedIncrementCoordinate coordinate base [] = 0ℚ
weightedIncrementCoordinate coordinate base (sample ∷ rest) =
  weight sample
    * (coordinate
        (Projector.rankOneProjector (Projector.vector (direction sample)))
      - coordinate
        (Projector.rankOneProjector (Projector.vector base)))
  + weightedIncrementCoordinate coordinate base rest

weightedIncrementCoordinateIdentity :
  ∀ coordinate base samples →
  weightedIncrementCoordinate coordinate base samples
  ≡ weightedCoordinate coordinate samples
      - coordinate (Projector.rankOneProjector (Projector.vector base))
        * sumWeights samples
weightedIncrementCoordinateIdentity coordinate base [] = solve []
weightedIncrementCoordinateIdentity coordinate base (sample ∷ rest) =
  trans
    (cong
      (λ tail →
        weight sample
          * (coordinate
              (Projector.rankOneProjector
                (Projector.vector (direction sample)))
            - coordinate
              (Projector.rankOneProjector (Projector.vector base)))
        + tail)
      (weightedIncrementCoordinateIdentity coordinate base rest))
    (solve
      ( weight sample
      ∷ coordinate
          (Projector.rankOneProjector
            (Projector.vector (direction sample)))
      ∷ coordinate
          (Projector.rankOneProjector (Projector.vector base))
      ∷ weightedCoordinate coordinate rest
      ∷ sumWeights rest
      ∷ []))

weightedProjectorSum : List KernelDirectionSample → Matrix.Matrix3
weightedProjectorSum samples =
  Matrix.matrix3
    (weightedCoordinate Matrix.m11 samples)
    (weightedCoordinate Matrix.m12 samples)
    (weightedCoordinate Matrix.m13 samples)
    (weightedCoordinate Matrix.m21 samples)
    (weightedCoordinate Matrix.m22 samples)
    (weightedCoordinate Matrix.m23 samples)
    (weightedCoordinate Matrix.m31 samples)
    (weightedCoordinate Matrix.m32 samples)
    (weightedCoordinate Matrix.m33 samples)

weightedProjectorIncrementSum :
  Projector.UnitDirection → List KernelDirectionSample → Matrix.Matrix3
weightedProjectorIncrementSum base samples =
  Matrix.matrix3
    (weightedIncrementCoordinate Matrix.m11 base samples)
    (weightedIncrementCoordinate Matrix.m12 base samples)
    (weightedIncrementCoordinate Matrix.m13 base samples)
    (weightedIncrementCoordinate Matrix.m21 base samples)
    (weightedIncrementCoordinate Matrix.m22 base samples)
    (weightedIncrementCoordinate Matrix.m23 base samples)
    (weightedIncrementCoordinate Matrix.m31 base samples)
    (weightedIncrementCoordinate Matrix.m32 base samples)
    (weightedIncrementCoordinate Matrix.m33 base samples)

record ZeroMassKernel (samples : List KernelDirectionSample) : Set where
  constructor zero-mass-kernel
  field
    totalWeightZero : sumWeights samples ≡ 0ℚ

open ZeroMassKernel public

coordinateZeroMassIncrement :
  ∀ coordinate base samples →
  ZeroMassKernel samples →
  weightedIncrementCoordinate coordinate base samples
  ≡ weightedCoordinate coordinate samples
coordinateZeroMassIncrement coordinate base samples zeroMass =
  trans
    (weightedIncrementCoordinateIdentity coordinate base samples)
    (trans
      (cong
        (λ totalWeight →
          weightedCoordinate coordinate samples
          - coordinate
              (Projector.rankOneProjector (Projector.vector base))
            * totalWeight)
        (totalWeightZero zeroMass))
      (solve
        ( weightedCoordinate coordinate samples
        ∷ coordinate
            (Projector.rankOneProjector (Projector.vector base))
        ∷ [])))

finitePVProjectorIncrementIdentity :
  ∀ base samples →
  ZeroMassKernel samples →
  weightedProjectorSum samples
  ≡ weightedProjectorIncrementSum base samples
finitePVProjectorIncrementIdentity base samples zeroMass =
  Matrix.matrixExt
    (sym (coordinateZeroMassIncrement Matrix.m11 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m12 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m13 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m21 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m22 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m23 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m31 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m32 base samples zeroMass))
    (sym (coordinateZeroMassIncrement Matrix.m33 base samples zeroMass))

finitePVProjectorIncrementAlgebraClosed : Bool
finitePVProjectorIncrementAlgebraClosed = true

literalPeriodicStrainKernelZeroMassConstructed : Bool
literalPeriodicStrainKernelZeroMassConstructed = false

finitePVProjectorIncrementAlgebraClosedIsTrue :
  finitePVProjectorIncrementAlgebraClosed ≡ true
finitePVProjectorIncrementAlgebraClosedIsTrue = refl

literalPeriodicStrainKernelZeroMassConstructedIsFalse :
  literalPeriodicStrainKernelZeroMassConstructed ≡ false
literalPeriodicStrainKernelZeroMassConstructedIsFalse = refl
