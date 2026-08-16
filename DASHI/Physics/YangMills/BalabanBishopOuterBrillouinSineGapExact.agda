module DASHI.Physics.YangMills.BalabanBishopOuterBrillouinSineGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Give a fully constructive, deliberately coarse lower bound for the lattice
-- momentum on an OUTER Brillouin coordinate.  If
--
--                 3/4 <= t <= 11/7,
--
-- then the radius-two alternating sine theorem gives
--
--   sin t >= t - t^3/6 >= 87/128.
--
-- The second inequality is proved by the exact factorization
--
--   [t-t^3/6] - [a-a^3/6]
--     = (t-a) [1 - (t^2 + at + a^2)/6],   a=3/4,
--
-- and t<=11/7 makes the bracket at least 1403/4704 > 0.  Consequently
--
--       (2 sin t)^2 >= (87/64)^2 = 7569/4096.
--
-- This is enough to make hat{k}^2 uniformly positive on every regular grid
-- cell once the elementary 3 < pi < 22/7 normalization is connected.  No
-- monotonicity theorem for sine is used.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as Sine
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Polynomial
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

lowerAngle upperAngle lowerSine upperQuadraticSum factorLower : ℚᵘ
lowerAngle = + 3 / 4
upperAngle = + 11 / 7
lowerSine = + 87 / 128
upperQuadraticSum = + 3301 / 784
factorLower = + 1403 / 4704

oneSixth two hatSquareLower : ℚᵘ
oneSixth = + 1 / 6
two = + 2 / 1
hatSquareLower = + 7569 / 4096

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

lowerAngleNonnegative : BishopReal.NonNegative (embed lowerAngle)
lowerAngleNonnegative = Order.embeddedRationalNonnegative lowerAngle nonNeg

upperAngleNonnegative : BishopReal.NonNegative (embed upperAngle)
upperAngleNonnegative = Order.embeddedRationalNonnegative upperAngle nonNeg

oneSixthNonnegative : BishopReal.NonNegative (embed oneSixth)
oneSixthNonnegative = Order.embeddedRationalNonnegative oneSixth nonNeg

twoNonnegative : BishopReal.NonNegative (embed two)
twoNonnegative = Order.embeddedRationalNonnegative two nonNeg

lowerSineNonnegative : BishopReal.NonNegative (embed lowerSine)
lowerSineNonnegative = Order.embeddedRationalNonnegative lowerSine nonNeg

quadraticSum : BishopReal.ℝ → BishopReal.ℝ
quadraticSum value =
  BishopReal._+_
    (BishopReal._*_ value value)
    (BishopReal._+_
      (BishopReal._*_ value (embed lowerAngle))
      (BishopReal._*_ (embed lowerAngle) (embed lowerAngle)))

factor : BishopReal.ℝ → BishopReal.ℝ
factor value =
  BishopReal._-_ BishopReal.1ℝ
    (BishopReal._*_ (embed oneSixth) (quadraticSum value))

squareBelowUpperSquare :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_
    (BishopReal._*_ value value)
    (BishopReal._*_ (embed upperAngle) (embed upperAngle))
squareBelowUpperSquare value valueNN valueBelowUpper =
  BishopProperties.*-mono-≤
    valueNN valueNN valueBelowUpper valueBelowUpper

linearCrossBelowUpper :
  ∀ value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_
    (BishopReal._*_ value (embed lowerAngle))
    (BishopReal._*_ (embed upperAngle) (embed lowerAngle))
linearCrossBelowUpper value valueBelowUpper =
  BishopProperties.*-monoʳ-≤-nonNeg
    valueBelowUpper lowerAngleNonnegative

quadraticSumUpper :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_ (quadraticSum value) (embed upperQuadraticSum)
quadraticSumUpper value valueNN valueBelowUpper =
  let
    raw = BishopProperties.+-mono-≤
      (squareBelowUpperSquare value valueNN valueBelowUpper)
      (BishopProperties.+-mono-≤
        (linearCrossBelowUpper value valueBelowUpper)
        BishopProperties.≤-refl)

    upperIdentity :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_ (embed upperAngle) (embed upperAngle))
          (BishopReal._+_
            (BishopReal._*_ (embed upperAngle) (embed lowerAngle))
            (BishopReal._*_ (embed lowerAngle) (embed lowerAngle))))
        (embed upperQuadraticSum)
    upperIdentity =
      let open BishopProperties.ℝ-Solver
      in solve 0
          ((Κ upperAngle ⊗ Κ upperAngle)
            ⊕ ((Κ upperAngle ⊗ Κ lowerAngle)
              ⊕ (Κ lowerAngle ⊗ Κ lowerAngle))
           ⊜ Κ upperQuadraticSum)
          BishopProperties.≃-refl
  in
  BishopProperties.≤-respʳ-≃ upperIdentity raw

factorLowerIdentity :
  BishopReal._≃_
    (BishopReal._-_ BishopReal.1ℝ
      (BishopReal._*_ (embed oneSixth) (embed upperQuadraticSum)))
    (embed factorLower)
factorLowerIdentity =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ (+ 1 / 1) ⊖ (Κ oneSixth ⊗ Κ upperQuadraticSum)
       ⊜ Κ factorLower)
      BishopProperties.≃-refl

factorAbovePositiveRational :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_ (embed factorLower) (factor value)
factorAbovePositiveRational value valueNN valueBelowUpper =
  let
    scaled = BishopProperties.*-monoˡ-≤-nonNeg
      (quadraticSumUpper value valueNN valueBelowUpper)
      oneSixthNonnegative
    negated = BishopProperties.neg-mono-≤ scaled
    shifted = BishopProperties.+-monoʳ-≤ BishopReal.1ℝ negated
    rightIdentity :
      BishopReal._≃_
        (BishopReal._+_ BishopReal.1ℝ
          (BishopReal.-
            (BishopReal._*_ (embed oneSixth) (quadraticSum value))))
        (factor value)
    rightIdentity =
      let open BishopProperties.ℝ-Solver
      in solve 1
          (λ s → Κ (+ 1 / 1) ⊕ (⊝ (Κ oneSixth ⊗ s))
            ⊜ Κ (+ 1 / 1) ⊖ (Κ oneSixth ⊗ s))
          BishopProperties.≃-refl (quadraticSum value)
  in
  BishopProperties.≤-respˡ-≃ factorLowerIdentity
    (BishopProperties.≤-respʳ-≃ rightIdentity shifted)

factorNonnegative :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal.NonNegative (factor value)
factorNonnegative value valueNN valueBelowUpper =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.≤-trans
      (BishopProperties.nonNegx⇒0≤x
        (Order.embeddedRationalNonnegative factorLower nonNeg))
      (factorAbovePositiveRational value valueNN valueBelowUpper))

cubicGapFactorization : ∀ value →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._-_ value (Polynomial.sineCubicTerm value))
      (embed lowerSine))
    (BishopReal._*_
      (BishopReal._-_ value (embed lowerAngle))
      (factor value))
cubicGapFactorization value =
  let open BishopProperties.ℝ-Solver
  in solve 1
      (λ t →
        (t ⊖ (Κ oneSixth ⊗ ((t ⊗ t) ⊗ t))) ⊖ Κ lowerSine
        ⊜ (t ⊖ Κ lowerAngle)
          ⊗ (Κ (+ 1 / 1)
             ⊖ (Κ oneSixth
                ⊗ ((t ⊗ t)
                   ⊕ ((t ⊗ Κ lowerAngle)
                      ⊕ (Κ lowerAngle ⊗ Κ lowerAngle))))))
      BishopProperties.≃-refl value

cubicPolynomialAboveLowerSine :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≤_ (embed lowerAngle) value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_
    (embed lowerSine)
    (BishopReal._-_ value (Polynomial.sineCubicTerm value))
cubicPolynomialAboveLowerSine value valueNN lowerBound upperBound =
  let
    differenceNN = BishopProperties.0≤x⇒nonNegx
      (Polynomial.orderGivesNonnegativeDifference lowerBound)
    productNN = BishopProperties.nonNegx,y⇒nonNegx*y
      differenceNN (factorNonnegative value valueNN upperBound)
    gapNN = BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm (cubicGapFactorization value))
      (BishopProperties.nonNegx⇒0≤x productNN)
  in
  Order.nonnegativeDifferenceGivesOrder gapNN

sineAboveEightySevenOverOneTwentyEight :
  ∀ {dataSet value} →
  (inputs : Sine.ConcreteTwoBallSineInputs dataSet value) →
  BishopReal._≤_ (embed lowerAngle) value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_ (embed lowerSine) (Elementary.bishopSin dataSet value)
sineAboveEightySevenOverOneTwentyEight inputs lowerBound upperBound =
  BishopProperties.≤-trans
    (cubicPolynomialAboveLowerSine _
      (Sine.valueNonnegative inputs) lowerBound upperBound)
    (Sine.sineCubicLowerTwoBall inputs)

hatComponent :
  ∀ {dataSet} → BishopReal.ℝ → BishopReal.ℝ
hatComponent {dataSet} value =
  BishopReal._*_ (embed two) (Elementary.bishopSin dataSet value)

hatSquare :
  ∀ {dataSet} → BishopReal.ℝ → BishopReal.ℝ
hatSquare {dataSet} value =
  BishopReal._*_ (hatComponent {dataSet} value) (hatComponent {dataSet} value)

hatLowerIdentity :
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_ (embed two) (embed lowerSine))
      (BishopReal._*_ (embed two) (embed lowerSine)))
    (embed hatSquareLower)
hatLowerIdentity =
  let open BishopProperties.ℝ-Solver
  in solve 0
      ((Κ two ⊗ Κ lowerSine) ⊗ (Κ two ⊗ Κ lowerSine)
       ⊜ Κ hatSquareLower)
      BishopProperties.≃-refl

hatComponentSquareAboveFixedGap :
  ∀ {dataSet value} →
  (inputs : Sine.ConcreteTwoBallSineInputs dataSet value) →
  BishopReal._≤_ (embed lowerAngle) value →
  BishopReal._≤_ value (embed upperAngle) →
  BishopReal._≤_ (embed hatSquareLower) (hatSquare {dataSet} value)
hatComponentSquareAboveFixedGap {dataSet} {value} inputs lowerBound upperBound =
  let
    sineBound = sineAboveEightySevenOverOneTwentyEight
      inputs lowerBound upperBound
    scaledBound = BishopProperties.*-monoˡ-≤-nonNeg
      sineBound twoNonnegative
    scaledLowerNN = BishopProperties.nonNegx,y⇒nonNegx*y
      twoNonnegative lowerSineNonnegative
    scaledActualNN = BishopProperties.0≤x⇒nonNegx
      (BishopProperties.≤-trans
        (BishopProperties.nonNegx⇒0≤x scaledLowerNN)
        scaledBound)
    squared = BishopProperties.*-mono-≤
      scaledLowerNN scaledLowerNN scaledBound scaledBound
  in
  BishopProperties.≤-respˡ-≃ hatLowerIdentity squared

outerBrillouinCubicSineLowerLevel : ProofLevel
outerBrillouinCubicSineLowerLevel = machineChecked

outerBrillouinHatMomentumGapLevel : ProofLevel
outerBrillouinHatMomentumGapLevel = machineChecked
