module DASHI.Moonshine.PenumbralBorcherdsExponentLedger where

-- Arithmetic ownership of a Borcherds product.  Product exponents are tied
-- coefficient-by-coefficient to the input half-weight form, while convergence,
-- Weyl-vector normalization, and divisor multiplicities remain explicit.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.PenumbralVectorValuedForm
open import DASHI.Moonshine.SingularThetaBorcherdsBridge

record BorcherdsExponentCarrier
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier) : Set₁ where
  field
    ProductIndex : Set
    DivisorIndex : Set
    Exponent : Set

    inputResidue : ProductIndex → Nat
    inputExponent :
      ProductIndex → VectorValuedModularCarrier.FormalExponent halfCarrier

    productExponent :
      WeightZeroModularCarrier.ProductExpansion zeroCarrier →
      ProductIndex → Exponent

    divisorMultiplicity :
      WeightZeroModularCarrier.DivisorDatum zeroCarrier →
      DivisorIndex → Exponent

    coefficientToExponent :
      VectorValuedModularCarrier.Scalar halfCarrier → Exponent

record BorcherdsExponentLedger
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (thetaLift : SingularThetaLift halfCarrier zeroCarrier)
  (borcherds :
    BorcherdsProductRealization halfCarrier zeroCarrier thetaLift)
  (exponents : BorcherdsExponentCarrier halfCarrier zeroCarrier)
  : Setω where
  field
    inputForm : VectorValuedModularCarrier.Vector halfCarrier

    exponentAgreement :
      (index : BorcherdsExponentCarrier.ProductIndex exponents) →
      BorcherdsExponentCarrier.productExponent exponents
        (BorcherdsProductRealization.productExpansion borcherds inputForm)
        index
      ≡
      BorcherdsExponentCarrier.coefficientToExponent exponents
        (VectorValuedModularCarrier.coefficient halfCarrier inputForm
          (BorcherdsExponentCarrier.inputResidue exponents index)
          (BorcherdsExponentCarrier.inputExponent exponents index))

    IntegralExponent : BorcherdsExponentCarrier.Exponent exponents → Set
    integralProductExponents :
      (index : BorcherdsExponentCarrier.ProductIndex exponents) →
      IntegralExponent
        (BorcherdsExponentCarrier.productExponent exponents
          (BorcherdsProductRealization.productExpansion borcherds inputForm)
          index)

    NegativeSupportFinite : Set
    negativeSupportFinite : NegativeSupportFinite

    WeylVector : Set
    weylVector : WeylVector
    WeylVectorNormalized : WeylVector → Set
    weylVectorNormalized : WeylVectorNormalized weylVector

    ProductConvergesOnDomain : Set
    productConvergesOnDomain : ProductConvergesOnDomain

    DivisorMultiplicityAgreement : Set
    divisorMultiplicityAgreement : DivisorMultiplicityAgreement

record TwinedBorcherdsExponentLedger
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (thetaLift : SingularThetaLift halfCarrier zeroCarrier)
  (borcherds :
    BorcherdsProductRealization halfCarrier zeroCarrier thetaLift)
  (exponents : BorcherdsExponentCarrier halfCarrier zeroCarrier)
  : Setω where
  field
    G : Set
    twinedInput : G → VectorValuedModularCarrier.Vector halfCarrier
    twinedLedger :
      (g : G) →
      BorcherdsExponentLedger
        halfCarrier zeroCarrier thetaLift borcherds exponents

    CharacterExponentCompatibility : G → Set
    characterExponentCompatibility :
      (g : G) → CharacterExponentCompatibility g

record BorcherdsExponentBoundary : Set where
  field
    exponentsComeFromInputCoefficients : ⊤
    integralityDoesNotImplyConvergence : ⊤
    negativeSupportFinitenessRequired : ⊤
    weylVectorNormalizationRequired : ⊤
    divisorMultiplicityNeedsSeparateProof : ⊤
    noProductIdentityFromFiniteCoefficientCheck : ⊤

penumbralBorcherdsExponentBoundary : BorcherdsExponentBoundary
penumbralBorcherdsExponentBoundary = record
  { exponentsComeFromInputCoefficients = tt
  ; integralityDoesNotImplyConvergence = tt
  ; negativeSupportFinitenessRequired = tt
  ; weylVectorNormalizationRequired = tt
  ; divisorMultiplicityNeedsSeparateProof = tt
  ; noProductIdentityFromFiniteCoefficientCheck = tt
  }
