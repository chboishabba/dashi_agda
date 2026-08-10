module DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact where

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
-- Round 36 refuted wave-vector principal angle as the HH-good smallness
-- parameter.  The physically relevant geometric object is instead the
-- vorticity *line*.  For a unit direction xi define its rank-one projector
--
--   Pi_xi = xi tensor xi.
--
-- This quotient forgets orientation exactly: Pi_(-xi) = Pi_xi.  For unit
-- directions xi, eta we prove the exact Frobenius identities
--
--   ||Pi_xi - Pi_eta||_F^2
--     = 2 (1 - (xi dot eta)^2),
--
--   ||xi - eta||^2 = 2 (1 - xi dot eta),
--
-- hence
--
--   ||Pi_xi - Pi_eta||_F^2
--     = (1 + xi dot eta) ||xi - eta||^2.
--
-- Thus the line/stabilizer defect is automatically insensitive to xi -> -xi
-- and is quantitatively controlled by the ordinary direction increment.  This
-- is the exact finite geometry needed by the surviving Constantin--Fefferman
-- HH-good route: a later periodic PV theorem should estimate these projector
-- increments in physical space rather than returning to mode-angle smallness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix

two : ℚ
two = Int.+ 2 / 1

rankOneProjector : V.Vector3 → Matrix.Matrix3
rankOneProjector (V.v3 vx vy vz) =
  Matrix.matrix3
    (vx * vx) (vx * vy) (vx * vz)
    (vy * vx) (vy * vy) (vy * vz)
    (vz * vx) (vz * vy) (vz * vz)

matrixSubtract : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
matrixSubtract left right =
  Matrix.matrix3
    (Matrix.m11 left - Matrix.m11 right)
    (Matrix.m12 left - Matrix.m12 right)
    (Matrix.m13 left - Matrix.m13 right)
    (Matrix.m21 left - Matrix.m21 right)
    (Matrix.m22 left - Matrix.m22 right)
    (Matrix.m23 left - Matrix.m23 right)
    (Matrix.m31 left - Matrix.m31 right)
    (Matrix.m32 left - Matrix.m32 right)
    (Matrix.m33 left - Matrix.m33 right)

frobeniusSquared : Matrix.Matrix3 → ℚ
frobeniusSquared matrix =
  Matrix.m11 matrix * Matrix.m11 matrix
  + Matrix.m12 matrix * Matrix.m12 matrix
  + Matrix.m13 matrix * Matrix.m13 matrix
  + Matrix.m21 matrix * Matrix.m21 matrix
  + Matrix.m22 matrix * Matrix.m22 matrix
  + Matrix.m23 matrix * Matrix.m23 matrix
  + Matrix.m31 matrix * Matrix.m31 matrix
  + Matrix.m32 matrix * Matrix.m32 matrix
  + Matrix.m33 matrix * Matrix.m33 matrix

projectorDefectSquared : V.Vector3 → V.Vector3 → ℚ
projectorDefectSquared left right =
  frobeniusSquared
    (matrixSubtract (rankOneProjector left) (rankOneProjector right))

projectorDefectSquaredExpansion : ∀ left right →
  projectorDefectSquared left right
  ≡
  V.normSquared left * V.normSquared left
  + V.normSquared right * V.normSquared right
  - two * (V.dot left right * V.dot left right)
projectorDefectSquaredExpansion
    (V.v3 ax ay az) (V.v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

record UnitDirection : Set where
  constructor unit-direction
  field
    vector : V.Vector3
    unitNorm : V.normSquared vector ≡ 1ℚ

open UnitDirection public

directionPairing : UnitDirection → UnitDirection → ℚ
directionPairing left right = V.dot (vector left) (vector right)

unitProjectorDefectSquared : UnitDirection → UnitDirection → ℚ
unitProjectorDefectSquared left right =
  projectorDefectSquared (vector left) (vector right)

unitProjectorDefectExact : ∀ left right →
  unitProjectorDefectSquared left right
  ≡ two * (1ℚ - directionPairing left right * directionPairing left right)
unitProjectorDefectExact left right =
  trans
    (projectorDefectSquaredExpansion (vector left) (vector right))
    reduceUnits
  where
  reduceUnits :
    V.normSquared (vector left) * V.normSquared (vector left)
    + V.normSquared (vector right) * V.normSquared (vector right)
    - two * (directionPairing left right * directionPairing left right)
    ≡ two * (1ℚ - directionPairing left right * directionPairing left right)
  reduceUnits rewrite unitNorm left | unitNorm right =
    solve (directionPairing left right ∷ [])

directionIncrementSquared : UnitDirection → UnitDirection → ℚ
directionIncrementSquared left right =
  V.normSquared (V.subtract (vector left) (vector right))

directionIncrementSquaredExpansion : ∀ left right →
  V.normSquared (V.subtract left right)
  ≡ V.normSquared left + V.normSquared right - two * V.dot left right
directionIncrementSquaredExpansion
    (V.v3 ax ay az) (V.v3 bx by bz) =
  solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

unitDirectionIncrementExact : ∀ left right →
  directionIncrementSquared left right
  ≡ two * (1ℚ - directionPairing left right)
unitDirectionIncrementExact left right =
  trans
    (directionIncrementSquaredExpansion (vector left) (vector right))
    reduceUnits
  where
  reduceUnits :
    V.normSquared (vector left) + V.normSquared (vector right)
      - two * directionPairing left right
    ≡ two * (1ℚ - directionPairing left right)
  reduceUnits rewrite unitNorm left | unitNorm right =
    solve (directionPairing left right ∷ [])

projectorDefectIncrementFactorization : ∀ left right →
  unitProjectorDefectSquared left right
  ≡ (1ℚ + directionPairing left right)
      * directionIncrementSquared left right
projectorDefectIncrementFactorization left right =
  trans
    (unitProjectorDefectExact left right)
    (trans
      factorAlgebra
      (cong
        ((1ℚ + directionPairing left right) *_)
        (sym (unitDirectionIncrementExact left right))))
  where
  factorAlgebra :
    two * (1ℚ - directionPairing left right * directionPairing left right)
    ≡ (1ℚ + directionPairing left right)
        * (two * (1ℚ - directionPairing left right))
  factorAlgebra = solve (directionPairing left right ∷ [])

negateVector : V.Vector3 → V.Vector3
negateVector (V.v3 vx vy vz) = V.v3 (- vx) (- vy) (- vz)

rankOneProjectorNegationInvariant : ∀ direction →
  rankOneProjector (negateVector direction) ≡ rankOneProjector direction
rankOneProjectorNegationInvariant (V.v3 vx vy vz) =
  Matrix.matrixExt
    (solve (vx ∷ []))
    (solve (vx ∷ vy ∷ []))
    (solve (vx ∷ vz ∷ []))
    (solve (vx ∷ vy ∷ []))
    (solve (vy ∷ []))
    (solve (vy ∷ vz ∷ []))
    (solve (vx ∷ vz ∷ []))
    (solve (vy ∷ vz ∷ []))
    (solve (vz ∷ []))

negateUnitDirection : UnitDirection → UnitDirection
negateUnitDirection direction =
  unit-direction (negateVector (vector direction)) negatedUnit
  where
  negatedUnit :
    V.normSquared (negateVector (vector direction)) ≡ 1ℚ
  negatedUnit with vector direction
  ... | V.v3 vx vy vz =
    trans
      (solve (vx ∷ vy ∷ vz ∷ []))
      (unitNorm direction)

oppositeDirectionSameProjector : ∀ direction →
  rankOneProjector (vector (negateUnitDirection direction))
  ≡ rankOneProjector (vector direction)
oppositeDirectionSameProjector direction =
  rankOneProjectorNegationInvariant (vector direction)

oppositeLineProjectorDefectZero : ∀ direction →
  unitProjectorDefectSquared direction (negateUnitDirection direction) ≡ 0ℚ
oppositeLineProjectorDefectZero direction with vector direction
... | V.v3 vx vy vz =
  solve (vx ∷ vy ∷ vz ∷ [])

lineProjectorStabilizerGeometryClosed : Bool
lineProjectorStabilizerGeometryClosed = true

periodicPVProjectorDefectEstimateConstructed : Bool
periodicPVProjectorDefectEstimateConstructed = false

lineProjectorStabilizerGeometryClosedIsTrue :
  lineProjectorStabilizerGeometryClosed ≡ true
lineProjectorStabilizerGeometryClosedIsTrue = refl

periodicPVProjectorDefectEstimateConstructedIsFalse :
  periodicPVProjectorDefectEstimateConstructed ≡ false
periodicPVProjectorDefectEstimateConstructedIsFalse = refl
