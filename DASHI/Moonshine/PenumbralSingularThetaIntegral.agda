module DASHI.Moonshine.PenumbralSingularThetaIntegral where

-- Practical analytic shape of a singular theta lift.  The lift is represented
-- by a regularized theta integral, converges away from a singular divisor, and
-- is compared to the logarithmic norm of a Borcherds product.  Constants and
-- branch conventions remain explicit.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.PenumbralVectorValuedForm
open import DASHI.Moonshine.SingularThetaBorcherdsBridge

record RegularizedThetaIntegralCarrier
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier) : Set₁ where
  field
    Scalar : Set
    ModuliPoint : Set
    IntegrationPoint : Set
    Integrand : Set
    RegularizationParameter : Set

    thetaKernel :
      VectorValuedModularCarrier.Vector halfCarrier →
      ModuliPoint → IntegrationPoint → Integrand

    pairWithInput :
      VectorValuedModularCarrier.Vector halfCarrier →
      Integrand → Integrand

    regularizedIntegral :
      RegularizationParameter →
      (IntegrationPoint → Integrand) → Scalar

    evaluateWeightZero :
      WeightZeroModularCarrier.ModularFunction zeroCarrier →
      ModuliPoint → Scalar

record SingularThetaIntegralRealization
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (thetaLift : SingularThetaLift halfCarrier zeroCarrier)
  (integralCarrier :
    RegularizedThetaIntegralCarrier halfCarrier zeroCarrier) : Setω where
  field
    inputForm : VectorValuedModularCarrier.Vector halfCarrier
    weakHolomorphy :
      VectorValuedModularCarrier.weaklyHolomorphic halfCarrier inputForm

    regularization :
      RegularizedThetaIntegralCarrier.RegularizationParameter
        integralCarrier

    SingularDivisor :
      RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier → Set
    AwayFromSingularDivisor :
      RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier → Set

    IntegralConvergesAt :
      RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier → Set

    convergenceAwayFromDivisor :
      (point :
        RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier) →
      AwayFromSingularDivisor point →
      IntegralConvergesAt point

    integralRepresentsLift :
      (point :
        RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier) →
      AwayFromSingularDivisor point →
      RegularizedThetaIntegralCarrier.evaluateWeightZero integralCarrier
        (SingularThetaLift.lift thetaLift inputForm) point
      ≡
      RegularizedThetaIntegralCarrier.regularizedIntegral integralCarrier
        regularization
        (λ integrationPoint →
          RegularizedThetaIntegralCarrier.pairWithInput integralCarrier
            inputForm
            (RegularizedThetaIntegralCarrier.thetaKernel integralCarrier
              inputForm point integrationPoint))

    PrincipalPartDeterminesSingularDivisor : Set
    principalPartDeterminesSingularDivisor :
      PrincipalPartDeterminesSingularDivisor

record BorcherdsLogNormIdentity
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (thetaLift : SingularThetaLift halfCarrier zeroCarrier)
  (borcherds :
    BorcherdsProductRealization halfCarrier zeroCarrier thetaLift)
  (integralCarrier :
    RegularizedThetaIntegralCarrier halfCarrier zeroCarrier)
  (integral :
    SingularThetaIntegralRealization
      halfCarrier zeroCarrier thetaLift integralCarrier) : Setω where
  field
    LogNorm : Set
    logNormOfProduct :
      WeightZeroModularCarrier.ProductExpansion zeroCarrier →
      RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier →
      LogNorm

    integralToLogNorm :
      RegularizedThetaIntegralCarrier.Scalar integralCarrier → LogNorm

    AdditiveConstant : Set
    additiveConstant : AdditiveConstant

    NormalizedEquality :
      RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier → Set

    normalizedEquality :
      (point :
        RegularizedThetaIntegralCarrier.ModuliPoint integralCarrier) →
      SingularThetaIntegralRealization.AwayFromSingularDivisor
        integral point →
      NormalizedEquality point

record SingularThetaIntegralBoundary : Set where
  field
    regularizationParameterRequired : ⊤
    convergenceOnlyClaimedAwayFromSingularDivisor : ⊤
    principalPartControlsDivisorWithProof : ⊤
    logarithmicProductIdentityNeedsNormalization : ⊤
    branchAndAdditiveConstantsNotSuppressed : ⊤
    noPointwiseIdentityAtUnresolvedSingularities : ⊤

penumbralSingularThetaIntegralBoundary :
  SingularThetaIntegralBoundary
penumbralSingularThetaIntegralBoundary = record
  { regularizationParameterRequired = tt
  ; convergenceOnlyClaimedAwayFromSingularDivisor = tt
  ; principalPartControlsDivisorWithProof = tt
  ; logarithmicProductIdentityNeedsNormalization = tt
  ; branchAndAdditiveConstantsNotSuppressed = tt
  ; noPointwiseIdentityAtUnresolvedSingularities = tt
  }
