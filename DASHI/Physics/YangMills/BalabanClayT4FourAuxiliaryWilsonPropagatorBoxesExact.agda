module DASHI.Physics.YangMills.BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact where

-- Four *ACTUAL SOURCE-REPRESENTATIVE* rational interval values for
-- the *free Wilson inverse-hat-momentum-squared* observable, computed
-- by the original Typed.divideInterval with positivity proofs from
-- original 4D source cells and dependency-aware rational sine square.
--
-- These are NOT the four Wilson+ghost+Haar one-loop beta integrals:
-- no mixed-derivative tensor numerator is encoded, no shifted momentum
-- denominators have been admitted, and no analytic box quadrature
-- remainder has been proved. This is an auxiliary physical denominator
-- sanity certificate for later source-correct calculation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 1ℚ; _/_; _*_; _+_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitQuadratureWeightsExact as Weights
import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact as Square

one two three four : Eval.RationalInterval
one = Square.sourceWilsonDenominatorBox Geometry.oneOuterRepresentative
two = Square.sourceWilsonDenominatorBox Geometry.twoOuterRepresentative
three = Square.sourceWilsonDenominatorBox Geometry.threeOuterRepresentative
four = Square.sourceWilsonDenominatorBox Geometry.fourOuterRepresentative

inverseOne inverseTwo inverseThree inverseFour : Eval.RationalInterval
inverseOne = Typed.divideInterval
  (Canonical.singletonInterval 1ℚ) one
  (Square.sourceStrictPositiveAtRegularBox Geometry.oneOuterRepresentative refl)
inverseTwo = Typed.divideInterval
  (Canonical.singletonInterval 1ℚ) two
  (Square.sourceStrictPositiveAtRegularBox Geometry.twoOuterRepresentative refl)
inverseThree = Typed.divideInterval
  (Canonical.singletonInterval 1ℚ) three
  (Square.sourceStrictPositiveAtRegularBox Geometry.threeOuterRepresentative refl)
inverseFour = Typed.divideInterval
  (Canonical.singletonInterval 1ℚ) four
  (Square.sourceStrictPositiveAtRegularBox Geometry.fourOuterRepresentative refl)

oneLower : Eval.lower inverseOne ≡ (+ 1 / 16)
oneLower = refl
oneUpper : Eval.upper inverseOne ≡ (+ 4096 / 7569)
oneUpper = refl

twoLower : Eval.lower inverseTwo ≡ (+ 1 / 16)
twoLower = refl
twoUpper : Eval.upper inverseTwo ≡ (+ 2048 / 7569)
twoUpper = refl

threeLower : Eval.lower inverseThree ≡ (+ 1 / 16)
threeLower = refl
threeUpper : Eval.upper inverseThree ≡ (+ 4096 / 22707)
threeUpper = refl

fourLower : Eval.lower inverseFour ≡ (+ 1 / 16)
fourLower = refl
fourUpper : Eval.upper inverseFour ≡ (+ 1024 / 7569)
fourUpper = refl

-- Exact weighted regular 240-cell interval evaluation of the
-- auxiliary FREE propagator, provided the literal per-cell Bishop
-- sine bounds are materialised. It uses the source 4,6,4,1 volumes.
weightedAuxiliaryLower : ℚ
weightedAuxiliaryLower =
  Weights.oneOuterWeight * Eval.lower inverseOne
  + Weights.twoOuterWeight * Eval.lower inverseTwo
  + Weights.threeOuterWeight * Eval.lower inverseThree
  + Weights.fourOuterWeight * Eval.lower inverseFour

weightedAuxiliaryUpper : ℚ
weightedAuxiliaryUpper =
  Weights.oneOuterWeight * Eval.upper inverseOne
  + Weights.twoOuterWeight * Eval.upper inverseTwo
  + Weights.threeOuterWeight * Eval.upper inverseThree
  + Weights.fourOuterWeight * Eval.upper inverseFour

weightedAuxiliaryLowerExact :
  weightedAuxiliaryLower ≡ (+ 15 / 16)
weightedAuxiliaryLowerExact = refl

weightedAuxiliaryUpperExact :
  weightedAuxiliaryUpper ≡ (+ 105472 / 22707)
weightedAuxiliaryUpperExact = refl

-- Not an estimate of the Yang-Mills one-loop scalar. It is the
-- coarser direct interval enclosure of the original inverse
-- Wilson propagator, conditional on true physical sine membership.
