module DASHI.Mathematics.AlgebraicGeometry.HodgeP1ProductPrimitiveRulingRegressionExact where

------------------------------------------------------------------------
-- P¹ × P¹ PRIMITIVE REGRESSION ON THE TWO ACTUAL RULING DIRECTIONS
--
-- Existing owner ProjectiveLineProductHodgeExact supplies the two independent
-- (1,1) tensor basis directions:
--
--   basis11Left  = [pt] ⊗ 1
--   basis11Right = 1 ⊗ [pt].
--
-- This file equips their rational span with the standard intersection form
--
--   h₁² = 0,  h₂² = 0,  h₁·h₂ = 1,
--
-- and uses the diagonal polarization h=h₁+h₂. The difference
--
--   δ = h₁-h₂
--
-- is nonzero, primitive (δ·h=0), has δ²=-2, and is anti-invariant under
-- the actual factor-swap on the two ruling directions.
--
-- This is a controlled algebraic regression: BOTH ruling classes are already
-- algebraic on P¹×P¹. It tests primitive decomposition/correspondence behavior;
-- it does NOT address an unknown Hodge class.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineProductHodgeExact as Product

------------------------------------------------------------------------
-- Rational span of the literal two (1,1) ruling basis directions.
------------------------------------------------------------------------

record RulingClass : Set where
  constructor ruling-class
  field
    h₁Coefficient : ℚ
    h₂Coefficient : ℚ

open RulingClass public

h₁ h₂ : RulingClass
h₁ = ruling-class 1 0
h₂ = ruling-class 0 1

add : RulingClass → RulingClass → RulingClass
add (ruling-class a b) (ruling-class c d) =
  ruling-class (a + c) (b + d)

neg : RulingClass → RulingClass
neg (ruling-class a b) =
  ruling-class (- a) (- b)

sub : RulingClass → RulingClass → RulingClass
sub left right = add left (neg right)

diagonalPolarization : RulingClass
diagonalPolarization = add h₁ h₂

primitiveDifference : RulingClass
primitiveDifference = sub h₁ h₂

------------------------------------------------------------------------
-- Standard intersection pairing on the two ruling classes.
------------------------------------------------------------------------

intersection : RulingClass → RulingClass → ℚ
intersection (ruling-class a b) (ruling-class c d) =
  a * d + b * c

h₁SelfIntersectionZero :
  intersection h₁ h₁ ≡ 0
h₁SelfIntersectionZero = refl

h₂SelfIntersectionZero :
  intersection h₂ h₂ ≡ 0
h₂SelfIntersectionZero = refl

rulingsMeetOnce :
  intersection h₁ h₂ ≡ 1
rulingsMeetOnce = refl

primitiveDifferenceOrthogonalToPolarization :
  intersection primitiveDifference diagonalPolarization ≡ 0
primitiveDifferenceOrthogonalToPolarization = ℚRing.solve

primitiveDifferenceSelfIntersection :
  intersection primitiveDifference primitiveDifference ≡ - 2
primitiveDifferenceSelfIntersection = ℚRing.solve

------------------------------------------------------------------------
-- Factor swap is an honest correspondence on this two-ruling regression:
-- it exchanges the two ProductHodgeExact (1,1) basis directions.
------------------------------------------------------------------------

swapRulings : RulingClass → RulingClass
swapRulings (ruling-class a b) =
  ruling-class b a

swapH₁IsH₂ :
  swapRulings h₁ ≡ h₂
swapH₁IsH₂ = refl

swapH₂IsH₁ :
  swapRulings h₂ ≡ h₁
swapH₂IsH₁ = refl

swapPreservesDiagonalPolarization :
  swapRulings diagonalPolarization ≡ diagonalPolarization
swapPreservesDiagonalPolarization = refl

swapNegatesPrimitiveDifference :
  swapRulings primitiveDifference ≡ neg primitiveDifference
swapNegatesPrimitiveDifference = refl

------------------------------------------------------------------------
-- Tie the two abstract coefficients back to the EXISTING Hodge basis labels.
-- These are not newly invented dimensions: ProductHodgeExact proves both
-- selected basis vectors have bidegree (1,1).
------------------------------------------------------------------------

rulingBasisBidegrees :
  Product.productBidegree Product.basis11Left ≡ Product.bidegree 1 1
  ×
  Product.productBidegree Product.basis11Right ≡ Product.bidegree 1 1
rulingBasisBidegrees =
  Product.basis11LeftDegree ,
  Product.basis11RightDegree

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID on P¹×P¹ regression:
--   two independent literal (1,1) directions
--   intersection lattice of the ruling span
--   diagonal-polarization primitive direction
--   nonzero negative self-intersection (-2)
--   factor-swap correspondence: h fixed, δ -> -δ
--
-- OPEN for Clay:
--   genuine Chow-group owner and cycle-class map
--   induced correspondence action on actual singular cohomology
--   migration to varieties with unknown primitive rational Hodge classes
--   universal algebraic lift / strict residual decomposition
------------------------------------------------------------------------
