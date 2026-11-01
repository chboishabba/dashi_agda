module DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact where

------------------------------------------------------------------------
-- PERIODIC B / PREFERRED ONE-SIDED SECOND-MOMENT COMPILER
--
-- The generic Aug-5 paired estimate charges two Taylor remainders:
--
--   A1 G2 + A2 G1 + A2 G1.
--
-- R571's preferred linear model is the literal +shift radial increment, so its
-- + remainder is exactly zero.  On that family the sharp algebraic coefficient
-- is therefore only
--
--   A1 G2 + A2 G1.
--
-- In the intended periodic specialization A1=A2=1, G1=E0 and G2=2E0, hence
-- the coefficient is definitionally/algebraically 3 E0.  This module proves
-- the finite-family inequality; it introduces no physical M2 payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

record PreferredOneSidedSecondMomentBudget : Set₁ where
  field
    samples : List Moment.PairedSecondMomentSample

    transportGradient derivativeCurvature : ℚ
    transportCurvature derivativeEnvelope : ℚ

    transportGradientNonnegative : 0ℚ ≤ transportGradient
    derivativeCurvatureNonnegative : 0ℚ ≤ derivativeCurvature
    transportCurvatureNonnegative : 0ℚ ≤ transportCurvature
    derivativeEnvelopeNonnegative : 0ℚ ≤ derivativeEnvelope

    plusRemainderZero :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.plusRemainder sample ≡ 0ℚ

    linearIncrementBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.linearIncrement sample
      ≤ Moment.displacement sample * transportGradient

    derivativeDifferenceBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.derivativeDifference sample
      ≤ Moment.displacement sample * derivativeCurvature

    minusRemainderBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.minusRemainder sample
      ≤ Moment.displacement sample * Moment.displacement sample
        * transportCurvature

    minusDerivativeBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.minusDerivative sample ≤ derivativeEnvelope

open PreferredOneSidedSecondMomentBudget public

preferredCoefficient : PreferredOneSidedSecondMomentBudget → ℚ
preferredCoefficient budget =
  transportGradient budget * derivativeCurvature budget
  + transportCurvature budget * derivativeEnvelope budget

preferredPointwiseSecondMomentBound :
  (budget : PreferredOneSidedSecondMomentBudget) →
  (sample : Moment.PairedSecondMomentSample) →
  sample ∈ samples budget →
  Moment.pairedMagnitude sample
  ≤ Moment.weightedSecondMoment sample * preferredCoefficient budget
preferredPointwiseSecondMomentBound budget sample member =
  let
    d = Moment.displacement sample
    A1 = transportGradient budget
    G2 = derivativeCurvature budget
    A2 = transportCurvature budget
    G1 = derivativeEnvelope budget

    d2NN : 0ℚ ≤ d * d
    d2NN =
      Moment.productNonnegative d d
        (Moment.displacementNonnegative sample)
        (Moment.displacementNonnegative sample)

    dA1NN : 0ℚ ≤ d * A1
    dA1NN =
      Moment.productNonnegative d A1
        (Moment.displacementNonnegative sample)
        (transportGradientNonnegative budget)

    dG2NN : 0ℚ ≤ d * G2
    dG2NN =
      Moment.productNonnegative d G2
        (Moment.displacementNonnegative sample)
        (derivativeCurvatureNonnegative budget)

    d2A2NN : 0ℚ ≤ d * d * A2
    d2A2NN =
      Moment.productNonnegative (d * d) A2
        d2NN
        (transportCurvatureNonnegative budget)

    linearBound :
      Moment.linearIncrement sample * Moment.derivativeDifference sample
      ≤ (d * d) * (A1 * G2)
    linearBound =
      subst
        (λ upper →
          Moment.linearIncrement sample * Moment.derivativeDifference sample
          ≤ upper)
        (solve (d ∷ A1 ∷ G2 ∷ []))
        (Moment.multiplyBounds
          (Moment.linearIncrementNonnegative sample)
          dA1NN
          (Moment.derivativeDifferenceNonnegative sample)
          dG2NN
          (linearIncrementBound budget sample member)
          (derivativeDifferenceBound budget sample member))

    minusBound :
      Moment.minusRemainder sample * Moment.minusDerivative sample
      ≤ (d * d) * (A2 * G1)
    minusBound =
      subst
        (λ upper →
          Moment.minusRemainder sample * Moment.minusDerivative sample
          ≤ upper)
        (solve (d ∷ A2 ∷ G1 ∷ []))
        (Moment.multiplyBounds
          (Moment.minusRemainderNonnegative sample)
          d2A2NN
          (Moment.minusDerivativeNonnegative sample)
          (derivativeEnvelopeNonnegative budget)
          (minusRemainderBound budget sample member)
          (minusDerivativeBound budget sample member))

    innerBound :
      Moment.linearIncrement sample * Moment.derivativeDifference sample
        + Moment.plusRemainder sample * Moment.plusDerivative sample
        + Moment.minusRemainder sample * Moment.minusDerivative sample
      ≤ (d * d) * preferredCoefficient budget
    innerBound
      rewrite plusRemainderZero budget sample member =
      subst
        (λ upper →
          Moment.linearIncrement sample * Moment.derivativeDifference sample
            + 0ℚ * Moment.plusDerivative sample
            + Moment.minusRemainder sample * Moment.minusDerivative sample
          ≤ upper)
        (solve (d ∷ A1 ∷ G2 ∷ A2 ∷ G1 ∷ []))
        (ℚP.+-mono-≤ linearBound minusBound)

    weightedBound :
      Moment.pairedMagnitude sample
      ≤ Moment.weight sample * ((d * d) * preferredCoefficient budget)
    weightedBound =
      let
        instance weightNN =
          nonNegative (Moment.weightNonnegative sample)
      in
      ℚP.*-monoˡ-≤-nonNeg (Moment.weight sample) innerBound
  in
  subst
    (λ upper → Moment.pairedMagnitude sample ≤ upper)
    (solve
      ( Moment.weight sample
      ∷ d
      ∷ preferredCoefficient budget
      ∷ []))
    weightedBound

preferredSumBoundOn :
  (budget : PreferredOneSidedSecondMomentBudget) →
  (family : List Moment.PairedSecondMomentSample) →
  ((sample : Moment.PairedSecondMomentSample) →
    sample ∈ family → sample ∈ samples budget) →
  Sum.sumBy family Moment.pairedMagnitude
  ≤ preferredCoefficient budget
      * Sum.sumBy family Moment.weightedSecondMoment
preferredSumBoundOn budget [] included =
  subst
    (0ℚ ≤_)
    (sym (solve (preferredCoefficient budget ∷ [])))
    ℚP.≤-refl
preferredSumBoundOn budget (sample ∷ rest) included =
  let
    local :
      Moment.pairedMagnitude sample
      ≤ preferredCoefficient budget * Moment.weightedSecondMoment sample
    local =
      subst
        (λ upper → Moment.pairedMagnitude sample ≤ upper)
        (solve
          ( Moment.weightedSecondMoment sample
          ∷ preferredCoefficient budget
          ∷ []))
        (preferredPointwiseSecondMomentBound
          budget sample (included sample (here refl)))

    tail :
      Sum.sumBy rest Moment.pairedMagnitude
      ≤ preferredCoefficient budget
          * Sum.sumBy rest Moment.weightedSecondMoment
    tail =
      preferredSumBoundOn budget rest
        (λ other membership → included other (there membership))
  in
  subst
    (λ upper →
      Moment.pairedMagnitude sample
        + Sum.sumBy rest Moment.pairedMagnitude
      ≤ upper)
    (solve
      ( preferredCoefficient budget
      ∷ Moment.weightedSecondMoment sample
      ∷ Sum.sumBy rest Moment.weightedSecondMoment
      ∷ []))
    (ℚP.+-mono-≤ local tail)

finitePreferredSecondMomentBound :
  (budget : PreferredOneSidedSecondMomentBudget) →
  Sum.sumBy (samples budget) Moment.pairedMagnitude
  ≤ preferredCoefficient budget
      * Sum.sumBy (samples budget) Moment.weightedSecondMoment
finitePreferredSecondMomentBound budget =
  preferredSumBoundOn budget (samples budget) (λ sample member → member)

------------------------------------------------------------------------
-- Exact 3E0 specialization.
------------------------------------------------------------------------

three : ℚ
three = 1ℚ + 1ℚ + 1ℚ

periodicThreeEnergyCoefficient :
  (energy : ℚ) →
  (1ℚ * (energy + energy))
    + (1ℚ * energy)
  ≡ three * energy
periodicThreeEnergyCoefficient energy =
  solve (energy ∷ [])

preferredPlusRemainderEliminated : Bool
preferredPlusRemainderEliminated = true

genericDuplicateCurvatureChargeRemoved : Bool
genericDuplicateCurvatureChargeRemoved = true

periodicCoefficientThreeEnergyProved : Bool
periodicCoefficientThreeEnergyProved = true

physicalWeightedSecondMomentPaymentClosedHere : Bool
physicalWeightedSecondMomentPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

periodicCoefficientThreeEnergyProvedIsTrue :
  periodicCoefficientThreeEnergyProved ≡ true
periodicCoefficientThreeEnergyProvedIsTrue = refl

physicalWeightedSecondMomentPaymentClosedHereIsFalse :
  physicalWeightedSecondMomentPaymentClosedHere ≡ false
physicalWeightedSecondMomentPaymentClosedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
