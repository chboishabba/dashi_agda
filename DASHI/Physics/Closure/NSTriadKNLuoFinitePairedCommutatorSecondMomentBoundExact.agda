module DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Prove the ordered second-moment estimate corresponding to the exact paired
-- identity
--
--   L (g_+ - g_-) + R_+ g_+ + R_- g_-.
--
-- Assume the first increments L and g_+-g_- each cost one displacement, while
-- both Taylor remainders cost displacement squared.  Then the whole paired
-- magnitude is bounded by
--
--   w |y|^2
--     (A_1 G_2 + A_2 G_1 + A_2 G_1).
--
-- The duplicated remainder term is retained explicitly.  This proves the
-- legitimate second-moment gain without dropping the derivative-variation
-- term exposed by the preceding identity module.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum

productNonnegative :
  (left right : ℚ) →
  0ℚ ≤ left →
  0ℚ ≤ right →
  0ℚ ≤ left * right
productNonnegative left right leftNonnegative rightNonnegative =
  let
    instance
      leftIsNonnegative = ℚ.nonNegative leftNonnegative
      rightIsNonnegative = ℚ.nonNegative rightNonnegative
      productIsNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚₚ.nonNegative⁻¹ (left * right)

multiplyBounds :
  ∀ {left leftUpper right rightUpper : ℚ} →
  0ℚ ≤ left →
  0ℚ ≤ leftUpper →
  0ℚ ≤ right →
  0ℚ ≤ rightUpper →
  left ≤ leftUpper →
  right ≤ rightUpper →
  left * right ≤ leftUpper * rightUpper
multiplyBounds
  {left} {leftUpper} {right} {rightUpper}
  leftNonnegative leftUpperNonnegative
  rightNonnegative rightUpperNonnegative
  leftBound rightBound =
  let
    first : left * right ≤ leftUpper * right
    first =
      let
        instance
          rightIsNonnegative = ℚ.nonNegative rightNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg right leftBound

    second : leftUpper * right ≤ leftUpper * rightUpper
    second =
      let
        instance
          upperIsNonnegative = ℚ.nonNegative leftUpperNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg leftUpper rightBound
  in
  ℚₚ.≤-trans first second

record PairedSecondMomentSample : Set where
  constructor paired-second-moment-sample
  field
    weight displacement : ℚ
    linearIncrement derivativeDifference : ℚ
    plusRemainder minusRemainder : ℚ
    plusDerivative minusDerivative : ℚ

    weightNonnegative : 0ℚ ≤ weight
    displacementNonnegative : 0ℚ ≤ displacement
    linearIncrementNonnegative : 0ℚ ≤ linearIncrement
    derivativeDifferenceNonnegative : 0ℚ ≤ derivativeDifference
    plusRemainderNonnegative : 0ℚ ≤ plusRemainder
    minusRemainderNonnegative : 0ℚ ≤ minusRemainder
    plusDerivativeNonnegative : 0ℚ ≤ plusDerivative
    minusDerivativeNonnegative : 0ℚ ≤ minusDerivative

open PairedSecondMomentSample public

pairedMagnitude : PairedSecondMomentSample → ℚ
pairedMagnitude sample =
  weight sample
  * ( linearIncrement sample * derivativeDifference sample
    + plusRemainder sample * plusDerivative sample
    + minusRemainder sample * minusDerivative sample
    )

weightedSecondMoment : PairedSecondMomentSample → ℚ
weightedSecondMoment sample =
  weight sample * (displacement sample * displacement sample)

record PairedSecondMomentBudget : Set₁ where
  field
    samples : List PairedSecondMomentSample
    transportGradient derivativeCurvature : ℚ
    transportCurvature derivativeEnvelope : ℚ

    transportGradientNonnegative : 0ℚ ≤ transportGradient
    derivativeCurvatureNonnegative : 0ℚ ≤ derivativeCurvature
    transportCurvatureNonnegative : 0ℚ ≤ transportCurvature
    derivativeEnvelopeNonnegative : 0ℚ ≤ derivativeEnvelope

    linearIncrementBound :
      (sample : PairedSecondMomentSample) →
      linearIncrement sample
      ≤ displacement sample * transportGradient

    derivativeDifferenceBound :
      (sample : PairedSecondMomentSample) →
      derivativeDifference sample
      ≤ displacement sample * derivativeCurvature

    plusRemainderBound :
      (sample : PairedSecondMomentSample) →
      plusRemainder sample
      ≤ displacement sample * displacement sample * transportCurvature

    minusRemainderBound :
      (sample : PairedSecondMomentSample) →
      minusRemainder sample
      ≤ displacement sample * displacement sample * transportCurvature

    plusDerivativeBound :
      (sample : PairedSecondMomentSample) →
      plusDerivative sample ≤ derivativeEnvelope

    minusDerivativeBound :
      (sample : PairedSecondMomentSample) →
      minusDerivative sample ≤ derivativeEnvelope

open PairedSecondMomentBudget public

secondMomentCoefficient : PairedSecondMomentBudget → ℚ
secondMomentCoefficient budget =
  transportGradient budget * derivativeCurvature budget
  + transportCurvature budget * derivativeEnvelope budget
  + transportCurvature budget * derivativeEnvelope budget

pointwisePairedSecondMomentBound :
  (budget : PairedSecondMomentBudget) →
  (sample : PairedSecondMomentSample) →
  pairedMagnitude sample
  ≤ weightedSecondMoment sample * secondMomentCoefficient budget
pointwisePairedSecondMomentBound budget sample =
  let
    displacementSquaredNonnegative :
      0ℚ ≤ displacement sample * displacement sample
    displacementSquaredNonnegative =
      productNonnegative
        (displacement sample)
        (displacement sample)
        (displacementNonnegative sample)
        (displacementNonnegative sample)

    displacementGradientNonnegative :
      0ℚ ≤ displacement sample * transportGradient budget
    displacementGradientNonnegative =
      productNonnegative
        (displacement sample)
        (transportGradient budget)
        (displacementNonnegative sample)
        (transportGradientNonnegative budget)

    displacementDerivativeCurvatureNonnegative :
      0ℚ ≤ displacement sample * derivativeCurvature budget
    displacementDerivativeCurvatureNonnegative =
      productNonnegative
        (displacement sample)
        (derivativeCurvature budget)
        (displacementNonnegative sample)
        (derivativeCurvatureNonnegative budget)

    squaredTransportCurvatureNonnegative :
      0ℚ ≤ displacement sample * displacement sample
        * transportCurvature budget
    squaredTransportCurvatureNonnegative =
      productNonnegative
        (displacement sample * displacement sample)
        (transportCurvature budget)
        displacementSquaredNonnegative
        (transportCurvatureNonnegative budget)

    linearTermBound :
      linearIncrement sample * derivativeDifference sample
      ≤ (displacement sample * displacement sample)
        * (transportGradient budget * derivativeCurvature budget)
    linearTermBound =
      subst
        (λ upper →
          linearIncrement sample * derivativeDifference sample ≤ upper)
        (solve
          ( displacement sample
          ∷ transportGradient budget
          ∷ derivativeCurvature budget
          ∷ []))
        (multiplyBounds
          (linearIncrementNonnegative sample)
          displacementGradientNonnegative
          (derivativeDifferenceNonnegative sample)
          displacementDerivativeCurvatureNonnegative
          (linearIncrementBound budget sample)
          (derivativeDifferenceBound budget sample))

    plusTermBound :
      plusRemainder sample * plusDerivative sample
      ≤ (displacement sample * displacement sample)
        * (transportCurvature budget * derivativeEnvelope budget)
    plusTermBound =
      subst
        (λ upper → plusRemainder sample * plusDerivative sample ≤ upper)
        (solve
          ( displacement sample
          ∷ transportCurvature budget
          ∷ derivativeEnvelope budget
          ∷ []))
        (multiplyBounds
          (plusRemainderNonnegative sample)
          squaredTransportCurvatureNonnegative
          (plusDerivativeNonnegative sample)
          (derivativeEnvelopeNonnegative budget)
          (plusRemainderBound budget sample)
          (plusDerivativeBound budget sample))

    minusTermBound :
      minusRemainder sample * minusDerivative sample
      ≤ (displacement sample * displacement sample)
        * (transportCurvature budget * derivativeEnvelope budget)
    minusTermBound =
      subst
        (λ upper → minusRemainder sample * minusDerivative sample ≤ upper)
        (solve
          ( displacement sample
          ∷ transportCurvature budget
          ∷ derivativeEnvelope budget
          ∷ []))
        (multiplyBounds
          (minusRemainderNonnegative sample)
          squaredTransportCurvatureNonnegative
          (minusDerivativeNonnegative sample)
          (derivativeEnvelopeNonnegative budget)
          (minusRemainderBound budget sample)
          (minusDerivativeBound budget sample))

    innerBound :
      linearIncrement sample * derivativeDifference sample
        + plusRemainder sample * plusDerivative sample
        + minusRemainder sample * minusDerivative sample
      ≤ (displacement sample * displacement sample)
        * secondMomentCoefficient budget
    innerBound =
      subst
        (λ upper →
          linearIncrement sample * derivativeDifference sample
            + plusRemainder sample * plusDerivative sample
            + minusRemainder sample * minusDerivative sample
          ≤ upper)
        (solve
          ( displacement sample
          ∷ transportGradient budget
          ∷ derivativeCurvature budget
          ∷ transportCurvature budget
          ∷ derivativeEnvelope budget
          ∷ []))
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤ linearTermBound plusTermBound)
          minusTermBound)

    weightedBound :
      pairedMagnitude sample
      ≤ weight sample
        * ((displacement sample * displacement sample)
          * secondMomentCoefficient budget)
    weightedBound =
      let
        instance
          weightIsNonnegative = ℚ.nonNegative (weightNonnegative sample)
      in
      ℚₚ.*-monoˡ-≤-nonNeg (weight sample) innerBound

    targetMeaning :
      weight sample
        * ((displacement sample * displacement sample)
          * secondMomentCoefficient budget)
      ≡ weightedSecondMoment sample * secondMomentCoefficient budget
    targetMeaning =
      solve
        ( weight sample
        ∷ displacement sample
        ∷ secondMomentCoefficient budget
        ∷ [])
  in
  subst
    (λ upper → pairedMagnitude sample ≤ upper)
    targetMeaning
    weightedBound

finitePairedSecondMomentBound :
  (budget : PairedSecondMomentBudget) →
  Sum.sumBy (samples budget) pairedMagnitude
  ≤ secondMomentCoefficient budget
      * Sum.sumBy (samples budget) weightedSecondMoment
finitePairedSecondMomentBound budget =
  let
    pointwiseSum :
      Sum.sumBy (samples budget) pairedMagnitude
      ≤ Sum.sumBy (samples budget)
          (λ sample →
            secondMomentCoefficient budget * weightedSecondMoment sample)
    pointwiseSum =
      Sum.sumByMonotone
        (samples budget)
        pairedMagnitude
        (λ sample →
          secondMomentCoefficient budget * weightedSecondMoment sample)
        (λ sample →
          subst
            (λ upper → pairedMagnitude sample ≤ upper)
            (solve
              ( weightedSecondMoment sample
              ∷ secondMomentCoefficient budget
              ∷ []))
            (pointwisePairedSecondMomentBound budget sample))

    factorMeaning :
      Sum.sumBy (samples budget)
        (λ sample →
          secondMomentCoefficient budget * weightedSecondMoment sample)
      ≡ secondMomentCoefficient budget
          * Sum.sumBy (samples budget) weightedSecondMoment
    factorMeaning =
      Sum.sumByScaleLeft
        (secondMomentCoefficient budget)
        (samples budget)
        weightedSecondMoment
  in
  subst
    (λ upper → Sum.sumBy (samples budget) pairedMagnitude ≤ upper)
    factorMeaning
    pointwiseSum
