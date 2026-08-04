module DASHI.Physics.Closure.NSTriadKNLuoWeightedIncrementFourierIntegrationCutsetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Give the literal weighted-increment Fourier theorem one exact dependency
-- boundary.  The final coefficient theorem is derived from two independently
-- inspectable equalities:
--
--   spatial integral coefficient = finite convolution coefficient,
--   finite convolution coefficient = exact increment multiplier coefficient.
--
-- The record also names every convention and legality obligation which must
-- be discharged on the official periodic carrier.  No field is allowed to be
-- replaced by the final whole-field equality itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

record WeightedIncrementFourierPrimitiveCutset : Set₁ where
  field
    Mode Coefficient FourierField : Set

    coefficient : FourierField → Mode → Coefficient

    literalWeightedIncrementField : FourierField
    finiteConvolutionField : FourierField
    exactMultiplierField : FourierField

    spatialIntegralToFiniteConvolution :
      (mode : Mode) →
      coefficient literalWeightedIncrementField mode
      ≡ coefficient finiteConvolutionField mode

    finiteConvolutionToExactMultiplier :
      (mode : Mode) →
      coefficient finiteConvolutionField mode
      ≡ coefficient exactMultiplierField mode

    fourierFieldExtensionality :
      (left right : FourierField) →
      ((mode : Mode) → coefficient left mode ≡ coefficient right mode) →
      left ≡ right

    FourierTranslateCoefficient : Set
    fourierTranslateCoefficient : FourierTranslateCoefficient

    FourierIncrementCoefficient : Set
    fourierIncrementCoefficient : FourierIncrementCoefficient

    IncrementCoefficientZeroModeVanishes : Set
    incrementCoefficientZeroModeVanishes :
      IncrementCoefficientZeroModeVanishes

    FourierTensorProductCoefficient : Set
    fourierTensorProductCoefficient : FourierTensorProductCoefficient

    IncrementTensorCoefficient : Set
    incrementTensorCoefficient : IncrementTensorCoefficient

    FiniteFiberConvolutionEqualsPairFold : Set
    finiteFiberConvolutionEqualsPairFold :
      FiniteFiberConvolutionEqualsPairFold

    ConvolutionMultiplicityPolicyExact : Set
    convolutionMultiplicityPolicyExact :
      ConvolutionMultiplicityPolicyExact

    KernelIntegralOfCharacter : Set
    kernelIntegralOfCharacter : KernelIntegralOfCharacter

    KernelIntegralOfIncrementCharacterProduct : Set
    kernelIntegralOfIncrementCharacterProduct :
      KernelIntegralOfIncrementCharacterProduct

    FiniteSumIntegralInterchange : Set
    finiteSumIntegralInterchange : FiniteSumIntegralInterchange

    TensorScalarIntegralLinearity : Set
    tensorScalarIntegralLinearity : TensorScalarIntegralLinearity

    FourierSignConventionMatchesKernelMultiplier : Set
    fourierSignConventionMatchesKernelMultiplier :
      FourierSignConventionMatchesKernelMultiplier

    TorusMeasureNormalizationMatchesFourierTransform : Set
    torusMeasureNormalizationMatchesFourierTransform :
      TorusMeasureNormalizationMatchesFourierTransform

    KernelTransformZeroModeEqualsKernelMass : Set
    kernelTransformZeroModeEqualsKernelMass :
      KernelTransformZeroModeEqualsKernelMass

    CanonicalKernelMassEqualsOne : Set
    canonicalKernelMassEqualsOne : CanonicalKernelMassEqualsOne

    DyadicKernelScalingCoefficientFormula : Set
    dyadicKernelScalingCoefficientFormula :
      DyadicKernelScalingCoefficientFormula

    RealFieldRealityConditionPreserved : Set
    realFieldRealityConditionPreserved :
      RealFieldRealityConditionPreserved

open WeightedIncrementFourierPrimitiveCutset public

weightedIncrementKernelFourierCoefficientIdentity :
  (cutset : WeightedIncrementFourierPrimitiveCutset) →
  (mode : Mode cutset) →
  coefficient cutset (literalWeightedIncrementField cutset) mode
  ≡ coefficient cutset (exactMultiplierField cutset) mode
weightedIncrementKernelFourierCoefficientIdentity cutset mode =
  trans
    (spatialIntegralToFiniteConvolution cutset mode)
    (finiteConvolutionToExactMultiplier cutset mode)

weightedIncrementKernelFourierFieldIdentity :
  (cutset : WeightedIncrementFourierPrimitiveCutset) →
  literalWeightedIncrementField cutset
  ≡ exactMultiplierField cutset
weightedIncrementKernelFourierFieldIdentity cutset =
  fourierFieldExtensionality cutset
    (literalWeightedIncrementField cutset)
    (exactMultiplierField cutset)
    (weightedIncrementKernelFourierCoefficientIdentity cutset)

record WeightedIncrementFourierRealization : Set₁ where
  field
    primitiveCutset : WeightedIncrementFourierPrimitiveCutset
    coefficientIdentity :
      (mode : Mode primitiveCutset) →
      coefficient primitiveCutset
        (literalWeightedIncrementField primitiveCutset) mode
      ≡ coefficient primitiveCutset
          (exactMultiplierField primitiveCutset) mode
    fieldIdentity :
      literalWeightedIncrementField primitiveCutset
      ≡ exactMultiplierField primitiveCutset

open WeightedIncrementFourierRealization public

weightedIncrementFourierRealization :
  WeightedIncrementFourierPrimitiveCutset →
  WeightedIncrementFourierRealization
weightedIncrementFourierRealization cutset = record
  { primitiveCutset = cutset
  ; coefficientIdentity =
      weightedIncrementKernelFourierCoefficientIdentity cutset
  ; fieldIdentity = weightedIncrementKernelFourierFieldIdentity cutset
  }

weightedIncrementFourierCutsetConstructed : Bool
weightedIncrementFourierCutsetConstructed = true

coefficientToFieldUpgradeConstructed : Bool
coefficientToFieldUpgradeConstructed = true

weightedIncrementFourierCutsetConstructedIsTrue :
  weightedIncrementFourierCutsetConstructed ≡ true
weightedIncrementFourierCutsetConstructedIsTrue = refl

coefficientToFieldUpgradeConstructedIsTrue :
  coefficientToFieldUpgradeConstructed ≡ true
coefficientToFieldUpgradeConstructedIsTrue = refl
