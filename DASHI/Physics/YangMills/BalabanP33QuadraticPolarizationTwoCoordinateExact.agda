module DASHI.Physics.YangMills.BalabanP33QuadraticPolarizationTwoCoordinateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact rational polarization identity needed to turn a literal
-- quadratic Hessian into matrix coefficients.  For
--
--   Q(x,y) = a x^2 + 2 b x y + c y^2
--
-- and its symmetric bilinear form B, we prove
--
--   Q(u+v) - Q(u-v) = 4 B(u,v).
--
-- The coordinate regressions recover both diagonal entries and the off-diagonal
-- entry b from evaluations of Q.  The physical 3072-coordinate theorem must
-- instantiate this algebra with the literal selected-background Hessian and
-- its actual constrained basis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

record Vector2 : Set where
  constructor vector2
  field
    xCoordinate yCoordinate : ℚ

open Vector2 public

addVector : Vector2 → Vector2 → Vector2
addVector u v =
  vector2
    (xCoordinate u + xCoordinate v)
    (yCoordinate u + yCoordinate v)

subtractVector : Vector2 → Vector2 → Vector2
subtractVector u v =
  vector2
    (xCoordinate u - xCoordinate v)
    (yCoordinate u - yCoordinate v)

quadraticForm : ℚ → ℚ → ℚ → Vector2 → ℚ
quadraticForm a b c value =
  a * xCoordinate value * xCoordinate value
  + (+ 2 / 1) * b * xCoordinate value * yCoordinate value
  + c * yCoordinate value * yCoordinate value

bilinearForm : ℚ → ℚ → ℚ → Vector2 → Vector2 → ℚ
bilinearForm a b c u v =
  a * xCoordinate u * xCoordinate v
  + b *
      (xCoordinate u * yCoordinate v
       + yCoordinate u * xCoordinate v)
  + c * yCoordinate u * yCoordinate v

polarizationExact :
  ∀ a b c u v →
  quadraticForm a b c (addVector u v)
    - quadraticForm a b c (subtractVector u v)
  ≡ (+ 4 / 1) * bilinearForm a b c u v
polarizationExact a b c (vector2 ux uy) (vector2 vx vy) =
  solve (a ∷ b ∷ c ∷ ux ∷ uy ∷ vx ∷ vy ∷ [])

basisX basisY : Vector2
basisX = vector2 1ℚ 0ℚ
basisY = vector2 0ℚ 1ℚ

diagonalXRecovered :
  ∀ a b c → quadraticForm a b c basisX ≡ a
diagonalXRecovered a b c = solve (a ∷ b ∷ c ∷ [])

diagonalYRecovered :
  ∀ a b c → quadraticForm a b c basisY ≡ c
diagonalYRecovered a b c = solve (a ∷ b ∷ c ∷ [])

offDiagonalRecoveredByBilinearForm :
  ∀ a b c → bilinearForm a b c basisX basisY ≡ b
offDiagonalRecoveredByBilinearForm a b c =
  solve (a ∷ b ∷ c ∷ [])

offDiagonalRecoveredByQuadraticDifference :
  ∀ a b c →
  (+ 1 / 4) *
    (quadraticForm a b c (addVector basisX basisY)
     - quadraticForm a b c (subtractVector basisX basisY))
  ≡ b
offDiagonalRecoveredByQuadraticDifference a b c =
  solve (a ∷ b ∷ c ∷ [])

record LiteralHessianMatrixInstantiationTarget : Set₁ where
  field
    Coordinate : Set
    Perturbation : Set
    basis : Coordinate → Perturbation
    literalQuadraticHessian : Perturbation → ℚ
    polarizedEntry : Coordinate → Coordinate → ℚ
    polarizationRepresentsEntry :
      (left right : Coordinate) → Set

-- The finite polarization algebra is closed above.  Producing the physical
-- basis and proving equality with the literal Wilson+gauge+constraint second
-- variation remain concrete selected-background tasks.
