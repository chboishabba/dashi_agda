{-# OPTIONS --safe #-}
module DASHI.Cognition.CuspCompressionModel where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Control.DynamicalTernarySignal
  using (compareNat; compareNat-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; con; _:=_)

------------------------------------------------------------------------
-- Canonical cusp discriminant.
--
-- For the depressed cubic x^3 - r x - h = 0, the sign of
--
--   4 r^3 - 27 h^2
--
-- is represented without subtraction by comparing the two natural
-- magnitudes.  The balanced trit is therefore a literal topology classifier:
--
-- neg : one-real-equilibrium regime
-- zer : repeated-root / fold boundary
-- pos : three-real-equilibrium regime

square : Nat → Nat
square n =
  n * n

cube : Nat → Nat
cube n =
  n * n * n

discriminantLeft : Nat → Nat
discriminantLeft r =
  4 * cube r

discriminantRight : Nat → Nat
discriminantRight h =
  27 * square h

cuspDiscriminantClass : Nat → Nat → Trit
cuspDiscriminantClass r h =
  compareNat
    (discriminantLeft r)
    (discriminantRight h)

data EquilibriumTopology : Set where
  oneReal criticalFold threeReal : EquilibriumTopology

interpretDiscriminant : Trit → EquilibriumTopology
interpretDiscriminant neg = oneReal
interpretDiscriminant zer = criticalFold
interpretDiscriminant pos = threeReal

------------------------------------------------------------------------
-- Repeated-root parameterisation.
--
-- A repeated root a gives
--
--   r = 3 a^2
--   h = 2 a^3
--
-- (the sign of h depends on which fold branch is selected; h^2 removes that
-- sign in the discriminant).  The semiring solver checks the generic identity.

rAtFold : Nat → Nat
rAtFold a =
  3 * square a

hMagnitudeAtFold : Nat → Nat
hMagnitudeAtFold a =
  2 * cube a

fold-lies-on-discriminant :
  (a : Nat) →
  discriminantLeft (rAtFold a) ≡
  discriminantRight (hMagnitudeAtFold a)
fold-lies-on-discriminant =
  solve 1
    (λ a →
      con 4 :*
        (((con 3 :* (a :* a)) :*
          (con 3 :* (a :* a))) :*
         (con 3 :* (a :* a)))
      :=
      con 27 :*
        ((con 2 :* ((a :* a) :* a)) :*
         (con 2 :* ((a :* a) :* a))))
    refl

compare-equal-is-zero :
  ∀ {left right : Nat} →
  left ≡ right →
  compareNat left right ≡ zer
compare-equal-is-zero {left} refl =
  compareNat-reflexive left

fold-class-is-critical :
  (a : Nat) →
  cuspDiscriminantClass
    (rAtFold a)
    (hMagnitudeAtFold a)
  ≡ zer
fold-class-is-critical a =
  compare-equal-is-zero
    (fold-lies-on-discriminant a)

three-cubed-is-twenty-seven :
  cube 3 ≡ 27
three-cubed-is-twenty-seven = refl

two-squared-is-four :
  square 2 ≡ 4
two-squared-is-four = refl

coefficient-balance-at-unit-fold :
  4 * cube 3 ≡ 27 * square 2
coefficient-balance-at-unit-fold = refl

------------------------------------------------------------------------
-- Exact coefficient form of the scaled potential.
--
-- Instead of fractions, store
--
--   4 V(x) = x^4 - 2 r x^2 - 4 h x.
--
-- Its derivative has magnitudes
--
--   4, 4 r, 4 h,
--
-- with signs +, -, -.  Factoring four recovers x^3 - r x - h.

record ScaledCuspPotential : Set where
  constructor scaled-cusp-potential
  field
    potentialQuartic : Nat
    potentialQuadratic : Nat
    potentialLinear : Nat

open ScaledCuspPotential public

record ScaledCuspDerivative : Set where
  constructor scaled-cusp-derivative
  field
    derivativeCubic : Nat
    derivativeLinear : Nat
    derivativeConstant : Nat

open ScaledCuspDerivative public

scaledPotential : Nat → Nat → ScaledCuspPotential
scaledPotential r h =
  scaled-cusp-potential
    1
    (2 * r)
    (4 * h)

differentiateScaledPotential :
  ScaledCuspPotential →
  ScaledCuspDerivative
differentiateScaledPotential potential =
  scaled-cusp-derivative
    (4 * potentialQuartic potential)
    (2 * potentialQuadratic potential)
    (potentialLinear potential)

double-double :
  (n : Nat) →
  2 * (2 * n) ≡ 4 * n
double-double =
  solve 1
    (λ n →
      con 2 :* (con 2 :* n)
      :=
      con 4 :* n)
    refl

canonical-derivative-cubic :
  (r h : Nat) →
  derivativeCubic
    (differentiateScaledPotential (scaledPotential r h))
  ≡ 4
canonical-derivative-cubic r h = refl

canonical-derivative-linear :
  (r h : Nat) →
  derivativeLinear
    (differentiateScaledPotential (scaledPotential r h))
  ≡ 4 * r
canonical-derivative-linear r h =
  double-double r

canonical-derivative-constant :
  (r h : Nat) →
  derivativeConstant
    (differentiateScaledPotential (scaledPotential r h))
  ≡ 4 * h
canonical-derivative-constant r h = refl

record CuspCompressionReceipt : Set where
  constructor cusp-compression-receipt
  field
    genericFoldIdentityChecked : Bool
    discriminantIsTernaryClassifier : Bool
    twentySevenComesFromThreeCubed : Bool
    numerologyUsedAsProof : Bool
    numerologyUsedAsProofIsFalse :
      numerologyUsedAsProof ≡ false

cuspCompressionReceipt : CuspCompressionReceipt
cuspCompressionReceipt =
  cusp-compression-receipt
    true true true
    false refl
