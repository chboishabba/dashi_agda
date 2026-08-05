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
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_; NonNegative)
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
      (+ 3 / 2) * betaCoefficient * current ≤ (+ 1 / 1)

open OneLoopStep public

squareNonnegative : ∀ value → 0ℚ ≤ square value
squareNonnegative value = ℚP.nonNegative⁻¹ (square value)

betaSquareNonnegative :
  (dataSet : OneLoopStep) →
  0ℚ ≤ betaCoefficient dataSet * square (current dataSet)
betaSquareNonnegative dataSet =
  let
    instance
      betaNN : NonNegative (betaCoefficient dataSet)
      betaNN = ℚ.nonNegative (betaNonnegative dataSet)
      squareNN : NonNegative (square (current dataSet))
      squareNN = ℚ.nonNegative (squareNonnegative (current dataSet))
  in ℚP.nonNegative⁻¹
      (betaCoefficient dataSet * square (current dataSet))

nextBelowCurrent :
  (dataSet : OneLoopStep) → next dataSet ≤ current dataSet
nextBelowCurrent dataSet =
  subst
    (λ left → left ≤ current dataSet)
    (sym (stepEquation dataSet))
    (ℚP.≤-trans
      (ℚP.+-monoˡ-≤
        (current dataSet - betaCoefficient dataSet * square (current dataSet))
        (remainderUpper dataSet))
      (subst
        (λ left → left ≤ current dataSet)
        (ℚRing.solve-∀
          (current dataSet)
          (betaCoefficient dataSet * square (current dataSet)))
        (ℚP.+-monoʳ-≤ (current dataSet)
          (ℚP.neg-mono-≤
            (ℚP.≤-trans
              (ℚP.*-monoˡ-≤-nonNeg (+ 1 / 2)
                (betaSquareNonnegative dataSet))
              (betaSquareNonnegative dataSet))))))

oneMinusThreeHalvesBetaCurrentNonnegative :
  (dataSet : OneLoopStep) →
  0ℚ ≤ (+ 1 / 1)
    - (+ 3 / 2) * betaCoefficient dataSet * current dataSet
oneMinusThreeHalvesBetaCurrentNonnegative dataSet =
  ℚP.p≤q⇒0≤q-p (smallCoupling dataSet)

nextNonnegative :
  (dataSet : OneLoopStep) → 0ℚ ≤ next dataSet
nextNonnegative dataSet =
  subst
    (λ right → 0ℚ ≤ right)
    (stepEquation dataSet)
    (ℚP.≤-trans
      (subst
        (λ left → left
          ≤ current dataSet
            - betaCoefficient dataSet * square (current dataSet)
            + remainder dataSet)
        (ℚRing.solve-∀
          (current dataSet)
          (betaCoefficient dataSet))
        (let
          instance
            currentNN : NonNegative (current dataSet)
            currentNN = ℚ.nonNegative (currentNonnegative dataSet)
            bracketNN : NonNegative
              ((+ 1 / 1)
                - (+ 3 / 2) * betaCoefficient dataSet * current dataSet)
            bracketNN = ℚ.nonNegative
              (oneMinusThreeHalvesBetaCurrentNonnegative dataSet)
         in ℚP.nonNegative⁻¹
              (current dataSet
                * ((+ 1 / 1)
                  - (+ 3 / 2) * betaCoefficient dataSet * current dataSet)))
      (subst
        (λ lower → lower
          ≤ current dataSet
            - betaCoefficient dataSet * square (current dataSet)
            + remainder dataSet)
        (ℚRing.solve-∀
          (current dataSet)
          (betaCoefficient dataSet))
        (ℚP.+-monoˡ-≤
          (current dataSet
            - betaCoefficient dataSet * square (current dataSet))
          (remainderLower dataSet))))

halfOneLoopDecrease :
  (dataSet : OneLoopStep) →
  (+ 1 / 2) * betaCoefficient dataSet * square (current dataSet)
  ≤ current dataSet - next dataSet
halfOneLoopDecrease dataSet =
  subst
    (λ right →
      (+ 1 / 2) * betaCoefficient dataSet * square (current dataSet)
      ≤ current dataSet - right)
    (stepEquation dataSet)
    (subst
      (λ right →
        (+ 1 / 2) * betaCoefficient dataSet * square (current dataSet)
        ≤ right)
      (ℚRing.solve-∀
        (current dataSet)
        (betaCoefficient dataSet * square (current dataSet))
        (remainder dataSet))
      (ℚP.+-monoʳ-≤
        (betaCoefficient dataSet * square (current dataSet))
        (ℚP.neg-mono-≤ (remainderUpper dataSet))))

crossMultipliedReciprocalGain :
  (dataSet : OneLoopStep) →
  (+ 1 / 2) * betaCoefficient dataSet
    * current dataSet * next dataSet
  ≤ current dataSet - next dataSet
crossMultipliedReciprocalGain dataSet =
  ℚP.≤-trans
    (let
      instance
        halfBetaCurrentNN : NonNegative
          ((+ 1 / 2) * betaCoefficient dataSet * current dataSet)
        halfBetaCurrentNN = ℚ.nonNegative
          (let
            instance
              halfNN : NonNegative (+ 1 / 2)
              halfNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 1 / 2))
              betaNN : NonNegative (betaCoefficient dataSet)
              betaNN = ℚ.nonNegative (betaNonnegative dataSet)
              currentNN : NonNegative (current dataSet)
              currentNN = ℚ.nonNegative (currentNonnegative dataSet)
           in ℚP.nonNegative⁻¹
                ((+ 1 / 2) * betaCoefficient dataSet * current dataSet))
     in ℚP.*-monoˡ-≤-nonNeg
          ((+ 1 / 2) * betaCoefficient dataSet * current dataSet)
          (nextBelowCurrent dataSet))
    (subst
      (λ left → left ≤ current dataSet - next dataSet)
      (ℚRing.solve-∀
        (betaCoefficient dataSet) (current dataSet))
      (halfOneLoopDecrease dataSet))

oneLoopMonotonicityLevel : ProofLevel
oneLoopMonotonicityLevel = machineChecked

oneLoopPositivityLevel : ProofLevel
oneLoopPositivityLevel = machineChecked

oneLoopCrossMultipliedReciprocalGainLevel : ProofLevel
oneLoopCrossMultipliedReciprocalGainLevel = machineChecked

physicalBetaFunctionAndRemainderLevel : ProofLevel
physicalBetaFunctionAndRemainderLevel = conditional
