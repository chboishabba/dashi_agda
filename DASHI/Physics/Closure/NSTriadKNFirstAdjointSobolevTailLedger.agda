module DASHI.Physics.Closure.NSTriadKNFirstAdjointSobolevTailLedger where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: shell Bernstein/counting, Sobolev shell weights, and paraproduct
-- summation.
-- Relationship: supports the standard analytic ingredients only.
--
-- Authors: DASHI repository contributors.
-- Title: "Cutoff-uniform first-adjoint Sobolev-tail exponent ledger".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; the exact endpoint exponent arithmetic is
-- repository-original.
-- Uses: for j low and J=j+d high,
--
--   2^(3j/2) 2^J 2^(-sJ) 2^(-sJ)
--     = 2^(-(2s-5/2)j) 2^(-(2s-1)d).
--
-- Relationship: proves the numerical margin in the full DASHI range
-- 5/2 < s < 3.  The cutoff-uniform functional estimate still requires the
-- repository shell-count, correlation/Cauchy--Schwarz, and orbit/helicity
-- transport laws to be instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

data FrozenAnalyticLeg : Set where
  outputLeg firstAdjointLeg secondAdjointLeg : FrozenAnalyticLeg

data EstimateMechanism : Set where
  incompressibilityLowDerivative
  highDerivativePaidByTwoSobolevWeights
  derivativeAlreadyOnLowFrozenLeg : EstimateMechanism

mechanism : FrozenAnalyticLeg → EstimateMechanism
mechanism outputLeg = incompressibilityLowDerivative
mechanism firstAdjointLeg = highDerivativePaidByTwoSobolevWeights
mechanism secondAdjointLeg = derivativeAlreadyOnLowFrozenLeg

------------------------------------------------------------------------
-- Exponents are scaled by two.  Every stored magnitude denotes a negative
-- power at the limiting endpoint s=5/2.
------------------------------------------------------------------------

record EndpointDyadicDecay : Set where
  constructor endpoint-decay
  field
    lowShellDecayMagnitudeTimesTwo : Nat
    separationGapDecayMagnitudeTimesTwo : Nat

open EndpointDyadicDecay public

outputEndpointDecay : EndpointDyadicDecay
outputEndpointDecay = endpoint-decay 5 10

firstAdjointEndpointDecay : EndpointDyadicDecay
firstAdjointEndpointDecay = endpoint-decay 5 8

secondAdjointEndpointDecay : EndpointDyadicDecay
secondAdjointEndpointDecay = endpoint-decay 5 10

endpointDecay : FrozenAnalyticLeg → EndpointDyadicDecay
endpointDecay outputLeg = outputEndpointDecay
endpointDecay firstAdjointLeg = firstAdjointEndpointDecay
endpointDecay secondAdjointLeg = secondAdjointEndpointDecay

record SobolevTailEndpointReceipt : Set where
  constructor endpoint-receipt
  field
    outputLowDecay :
      lowShellDecayMagnitudeTimesTwo outputEndpointDecay ≡ 5
    outputGapDecay :
      separationGapDecayMagnitudeTimesTwo outputEndpointDecay ≡ 10
    firstLowDecay :
      lowShellDecayMagnitudeTimesTwo firstAdjointEndpointDecay ≡ 5
    firstGapDecay :
      separationGapDecayMagnitudeTimesTwo firstAdjointEndpointDecay ≡ 8
    secondLowDecay :
      lowShellDecayMagnitudeTimesTwo secondAdjointEndpointDecay ≡ 5
    secondGapDecay :
      separationGapDecayMagnitudeTimesTwo secondAdjointEndpointDecay ≡ 10

    outputMechanism :
      mechanism outputLeg ≡ incompressibilityLowDerivative
    firstMechanism :
      mechanism firstAdjointLeg ≡ highDerivativePaidByTwoSobolevWeights
    secondMechanism :
      mechanism secondAdjointLeg ≡ derivativeAlreadyOnLowFrozenLeg

open SobolevTailEndpointReceipt public

sobolevTailEndpointReceipt : SobolevTailEndpointReceipt
sobolevTailEndpointReceipt =
  endpoint-receipt refl refl refl refl refl refl refl refl refl

record FirstAdjointTailAnalyticCutset : Set₁ where
  field
    shellL2CorrelationCauchySchwarz : Set
    lowOutputShellCardinalityThreeDimensional : Set
    lerayProjectionL2Contraction : Set
    highInputShellsComparable : Set
    derivativeBoundedByHighShell : Set
    twoHighSobolevWeightsInserted : Set

    lowShellFactorIsThreeHalves : Set
    derivativeFactorIsOne : Set
    postSobolevHighPowerIsOneMinusTwoS : Set
    gapDecayAtLowerEndpointIsFour : Set
    lowShellDecayAtLowerEndpointIsFiveHalves : Set

    constantsIndependentOfGalerkinCutoff : Set
    orbitNormalizationConstantIndependentOfCutoff : Set
    helicityLiftConstantIndependentOfCutoff : Set
    estimateTransportedToFirstPartialAdjoint : Set

open FirstAdjointTailAnalyticCutset public

record ThreeLegHighHighTailPackage : Set₁ where
  field
    outputRelocationEstimate : Set
    firstAdjointSobolevTailEstimate : Set
    secondAdjointFrozenDerivativeEstimate : Set

    outputSeriesConverges : Set
    firstAdjointSeriesConverges : Set
    secondAdjointSeriesConverges : Set

    allThreeUniformForFiveHalvesBelowSBelowThree : Set
    allThreeConstantsIndependentOfCutoff : Set

open ThreeLegHighHighTailPackage public

firstAdjointSobolevTailExponentArithmeticClosed : Bool
firstAdjointSobolevTailExponentArithmeticClosed = true

firstAdjointSobolevTailExponentArithmeticClosedIsTrue :
  firstAdjointSobolevTailExponentArithmeticClosed ≡ true
firstAdjointSobolevTailExponentArithmeticClosedIsTrue = refl

firstAdjointCutoffUniformFunctionalEstimateClosed : Bool
firstAdjointCutoffUniformFunctionalEstimateClosed = false

firstAdjointCutoffUniformFunctionalEstimateClosedIsFalse :
  firstAdjointCutoffUniformFunctionalEstimateClosed ≡ false
firstAdjointCutoffUniformFunctionalEstimateClosedIsFalse = refl

allThreeHighHighToLowFunctionalEstimatesClosed : Bool
allThreeHighHighToLowFunctionalEstimatesClosed = false

allThreeHighHighToLowFunctionalEstimatesClosedIsFalse :
  allThreeHighHighToLowFunctionalEstimatesClosed ≡ false
allThreeHighHighToLowFunctionalEstimatesClosedIsFalse = refl
