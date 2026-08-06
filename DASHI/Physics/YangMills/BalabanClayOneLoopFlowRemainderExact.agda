module DASHI.Physics.YangMills.BalabanClayOneLoopFlowRemainderExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories", Physical Review
-- Letters 30 (1973), 1343--1346. DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?", Physical Review
-- Letters 30 (1973), 1346--1349. DOI: 10.1103/PhysRevLett.30.1346.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Work with u=g^2 in the ultraviolet-directed convention
--
--   u' = u - b u^2 + r.
--
-- If |r| <= (b/2)u^2 and (3b/2)u <= 1, exact ordered-field algebra proves
--
--   0 <= u' <= u,
--   (b/2)u^2 <= u-u'.
--
-- It also proves the cross-multiplied reciprocal-gain certificate
--
--   (b/2) u u' <= u-u',
--
-- which is the denominator-free form of 1/u' - 1/u >= b/2.  The physical
-- beta-function computation and the O(g^5) remainder estimate remain the
-- analytic producers; their scalar consequences are no longer assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

square : ℚ → ℚ
square value = value * value

record OneLoopStep : Set₁ where
  field
    current next betaCoefficient remainder : ℚ

    currentNonnegative : 0ℚ ≤ current
    betaNonnegative : 0ℚ ≤ betaCoefficient

    stepEquation :
      next ≡ current - betaCoefficient * square current + remainder

    remainderLower :
      - ((+ 1 / 2) * betaCoefficient * square current)
      ≤ remainder
    remainderUpper :
      remainder
      ≤ (+ 1 / 2) * betaCoefficient * square current

    smallCoupling :
      (+ 3 / 2) * betaCoefficient * current ≤ 1ℚ

open OneLoopStep public

betaSquare : OneLoopStep → ℚ
betaSquare dataSet =
  betaCoefficient dataSet * square (current dataSet)

halfBetaSquare : OneLoopStep → ℚ
halfBetaSquare dataSet = (+ 1 / 2) * betaSquare dataSet

squareNonnegative : ∀ value → 0ℚ ≤ square value
squareNonnegative value = ℚP.nonNegative⁻¹ (square value)

betaSquareNonnegative :
  (dataSet : OneLoopStep) → 0ℚ ≤ betaSquare dataSet
betaSquareNonnegative dataSet =
  let
    instance
      betaNN : NonNegative (betaCoefficient dataSet)
      betaNN = ℚ.nonNegative (betaNonnegative dataSet)
      squareNN : NonNegative (square (current dataSet))
      squareNN = ℚ.nonNegative (squareNonnegative (current dataSet))
  in ℚP.nonNegative⁻¹ (betaSquare dataSet)

halfBetaSquareNonnegative :
  (dataSet : OneLoopStep) → 0ℚ ≤ halfBetaSquare dataSet
halfBetaSquareNonnegative dataSet =
  let
    instance
      halfNN : NonNegative (+ 1 / 2)
      halfNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 1 / 2))
      betaSquareNN : NonNegative (betaSquare dataSet)
      betaSquareNN = ℚ.nonNegative (betaSquareNonnegative dataSet)
  in ℚP.nonNegative⁻¹ (halfBetaSquare dataSet)

halfBetaSquareBelowBetaSquare :
  (dataSet : OneLoopStep) →
  halfBetaSquare dataSet ≤ betaSquare dataSet
halfBetaSquareBelowBetaSquare dataSet =
  let
    instance
      halfBetaNN : NonNegative (halfBetaSquare dataSet)
      halfBetaNN = ℚ.nonNegative (halfBetaSquareNonnegative dataSet)
  in
  subst
    (λ upper → halfBetaSquare dataSet ≤ upper)
    (ℚRing.solve-∀ (betaSquare dataSet))
    (ℚP.p≤p+q
      (halfBetaSquare dataSet) (halfBetaSquare dataSet))

subtractNonnegativeBelow : ∀ value loss →
  0ℚ ≤ loss → value - loss ≤ value
subtractNonnegativeBelow value loss lossNonnegative =
  subst
    (λ upper → value + (- loss) ≤ upper)
    (ℚRing.solve-∀ value)
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (subst
        (λ upper → - loss ≤ upper)
        (ℚRing.solve [])
        (ℚP.neg-mono-≤ lossNonnegative)))

stepUpperExpansion :
  (dataSet : OneLoopStep) →
  current dataSet - betaSquare dataSet + halfBetaSquare dataSet
  ≡ current dataSet - halfBetaSquare dataSet
stepUpperExpansion dataSet =
  ℚRing.solve-∀ (current dataSet) (betaSquare dataSet)

stepUpperEnvelope :
  (dataSet : OneLoopStep) →
  current dataSet - betaSquare dataSet + remainder dataSet
  ≤ current dataSet - halfBetaSquare dataSet
stepUpperEnvelope dataSet =
  subst
    (λ upper →
      current dataSet - betaSquare dataSet + remainder dataSet
      ≤ upper)
    (stepUpperExpansion dataSet)
    (ℚP.+-monoʳ-≤
      (current dataSet - betaSquare dataSet)
      (remainderUpper dataSet))

nextBelowCurrent :
  (dataSet : OneLoopStep) → next dataSet ≤ current dataSet
nextBelowCurrent dataSet =
  subst
    (λ left → left ≤ current dataSet)
    (sym (stepEquation dataSet))
    (ℚP.≤-trans
      (stepUpperEnvelope dataSet)
      (subtractNonnegativeBelow
        (current dataSet) (halfBetaSquare dataSet)
        (halfBetaSquareNonnegative dataSet)))

oneMinusThreeHalvesBetaCurrentNonnegative :
  (dataSet : OneLoopStep) →
  0ℚ ≤ 1ℚ
    - (+ 3 / 2) * betaCoefficient dataSet * current dataSet
oneMinusThreeHalvesBetaCurrentNonnegative dataSet =
  ℚP.p≤q⇒0≤q-p (smallCoupling dataSet)

lowerEnvelope : OneLoopStep → ℚ
lowerEnvelope dataSet =
  current dataSet
    * (1ℚ - (+ 3 / 2)
      * betaCoefficient dataSet * current dataSet)

lowerEnvelopeNonnegative :
  (dataSet : OneLoopStep) → 0ℚ ≤ lowerEnvelope dataSet
lowerEnvelopeNonnegative dataSet =
  let
    instance
      currentNN : NonNegative (current dataSet)
      currentNN = ℚ.nonNegative (currentNonnegative dataSet)
      bracketNN : NonNegative
        (1ℚ - (+ 3 / 2)
          * betaCoefficient dataSet * current dataSet)
      bracketNN = ℚ.nonNegative
        (oneMinusThreeHalvesBetaCurrentNonnegative dataSet)
  in ℚP.nonNegative⁻¹ (lowerEnvelope dataSet)

lowerEnvelopeExpansion :
  (dataSet : OneLoopStep) →
  lowerEnvelope dataSet
  ≡ current dataSet - betaSquare dataSet
      + (- halfBetaSquare dataSet)
lowerEnvelopeExpansion dataSet =
  ℚRing.solve-∀
    (current dataSet) (betaCoefficient dataSet)

stepLowerEnvelope :
  (dataSet : OneLoopStep) →
  lowerEnvelope dataSet
  ≤ current dataSet - betaSquare dataSet + remainder dataSet
stepLowerEnvelope dataSet =
  subst
    (λ lower → lower
      ≤ current dataSet - betaSquare dataSet + remainder dataSet)
    (sym (lowerEnvelopeExpansion dataSet))
    (ℚP.+-monoʳ-≤
      (current dataSet - betaSquare dataSet)
      (remainderLower dataSet))

nextNonnegative :
  (dataSet : OneLoopStep) → 0ℚ ≤ next dataSet
nextNonnegative dataSet =
  subst
    (λ right → 0ℚ ≤ right)
    (sym (stepEquation dataSet))
    (ℚP.≤-trans
      (lowerEnvelopeNonnegative dataSet)
      (stepLowerEnvelope dataSet))

betaMinusHalfBetaIsHalfBeta :
  (dataSet : OneLoopStep) →
  betaSquare dataSet + (- halfBetaSquare dataSet)
  ≡ halfBetaSquare dataSet
betaMinusHalfBetaIsHalfBeta dataSet =
  ℚRing.solve-∀ (betaSquare dataSet)

decreaseExpansion :
  (dataSet : OneLoopStep) →
  betaSquare dataSet + (- remainder dataSet)
  ≡ current dataSet
      - (current dataSet - betaSquare dataSet + remainder dataSet)
decreaseExpansion dataSet =
  ℚRing.solve-∀
    (current dataSet) (betaSquare dataSet) (remainder dataSet)

halfOneLoopDecreaseAgainstExpansion :
  (dataSet : OneLoopStep) →
  halfBetaSquare dataSet
  ≤ current dataSet
      - (current dataSet - betaSquare dataSet + remainder dataSet)
halfOneLoopDecreaseAgainstExpansion dataSet =
  let
    shifted :
      betaSquare dataSet + (- halfBetaSquare dataSet)
      ≤ betaSquare dataSet + (- remainder dataSet)
    shifted =
      ℚP.+-monoʳ-≤
        (betaSquare dataSet)
        (ℚP.neg-mono-≤ (remainderUpper dataSet))
  in
  subst
    (λ lower → lower
      ≤ current dataSet
          - (current dataSet - betaSquare dataSet + remainder dataSet))
    (betaMinusHalfBetaIsHalfBeta dataSet)
    (subst
      (λ upper →
        betaSquare dataSet + (- halfBetaSquare dataSet)
        ≤ upper)
      (decreaseExpansion dataSet)
      shifted)

halfOneLoopDecrease :
  (dataSet : OneLoopStep) →
  halfBetaSquare dataSet ≤ current dataSet - next dataSet
halfOneLoopDecrease dataSet =
  subst
    (λ right →
      halfBetaSquare dataSet ≤ current dataSet - right)
    (sym (stepEquation dataSet))
    (halfOneLoopDecreaseAgainstExpansion dataSet)

halfBetaCurrentNonnegative :
  (dataSet : OneLoopStep) →
  0ℚ ≤ (+ 1 / 2) * betaCoefficient dataSet * current dataSet
halfBetaCurrentNonnegative dataSet =
  let
    instance
      halfNN : NonNegative (+ 1 / 2)
      halfNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 1 / 2))
      betaNN : NonNegative (betaCoefficient dataSet)
      betaNN = ℚ.nonNegative (betaNonnegative dataSet)
      currentNN : NonNegative (current dataSet)
      currentNN = ℚ.nonNegative (currentNonnegative dataSet)
  in ℚP.nonNegative⁻¹
      ((+ 1 / 2) * betaCoefficient dataSet * current dataSet)

multiplierTimesCurrentIsHalfBetaSquare :
  (dataSet : OneLoopStep) →
  ((+ 1 / 2) * betaCoefficient dataSet * current dataSet)
    * current dataSet
  ≡ halfBetaSquare dataSet
multiplierTimesCurrentIsHalfBetaSquare dataSet =
  ℚRing.solve-∀
    (betaCoefficient dataSet) (current dataSet)

crossMultipliedReciprocalGain :
  (dataSet : OneLoopStep) →
  (+ 1 / 2) * betaCoefficient dataSet
    * current dataSet * next dataSet
  ≤ current dataSet - next dataSet
crossMultipliedReciprocalGain dataSet =
  let
    multiplier =
      (+ 1 / 2) * betaCoefficient dataSet * current dataSet
    instance
      multiplierNN : NonNegative multiplier
      multiplierNN = ℚ.nonNegative
        (halfBetaCurrentNonnegative dataSet)
    multiplied =
      ℚP.*-monoˡ-≤-nonNeg multiplier
        (nextBelowCurrent dataSet)
    multipliedToHalf :
      multiplier * next dataSet ≤ halfBetaSquare dataSet
    multipliedToHalf =
      subst
        (λ upper → multiplier * next dataSet ≤ upper)
        (multiplierTimesCurrentIsHalfBetaSquare dataSet)
        multiplied
  in
  ℚP.≤-trans multipliedToHalf (halfOneLoopDecrease dataSet)

oneLoopMonotonicityLevel : ProofLevel
oneLoopMonotonicityLevel = machineChecked

oneLoopPositivityLevel : ProofLevel
oneLoopPositivityLevel = machineChecked

oneLoopCrossMultipliedReciprocalGainLevel : ProofLevel
oneLoopCrossMultipliedReciprocalGainLevel = machineChecked

physicalBetaFunctionAndRemainderLevel : ProofLevel
physicalBetaFunctionAndRemainderLevel = conditional
