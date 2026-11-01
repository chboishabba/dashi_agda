module DASHI.Moonshine.PenumbralThetaComponentBridge where

-- Scalar/vector-valued dictionary for half-integral weight moonshine.
-- Residue components modulo 2m are transported to a scalar plus-space form.
-- The inverse is asserted only on the supported image, not on arbitrary scalar
-- q-series.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.PenumbralLambency
open import DASHI.Moonshine.PenumbralVectorValuedForm

record ScalarHalfIntegralFormCarrier : Set₁ where
  field
    Scalar : Set
    FormalExponent : Set
    ScalarForm : Set

    coefficient : ScalarForm → FormalExponent → Scalar
    weaklyHolomorphic : ScalarForm → Set
    weightOneHalf : ScalarForm → Set
    plusSpace : Nat → ScalarForm → Set
    modularAtLevelFourTimes : Nat → ScalarForm → Set

record ThetaComponentDictionary
  (vectorCarrier : VectorValuedModularCarrier)
  (scalarCarrier : ScalarHalfIntegralFormCarrier)
  (arithmetic : LambencyArithmetic)
  {Discriminant : Set}
  (lambda : PenumbralLambdency arithmetic Discriminant)
  (support : PenumbralSupport vectorCarrier arithmetic lambda) : Setω where
  field
    vectorToScalar :
      VectorValuedModularCarrier.Vector vectorCarrier →
      ScalarHalfIntegralFormCarrier.ScalarForm scalarCarrier

    scalarToVector :
      ScalarHalfIntegralFormCarrier.ScalarForm scalarCarrier →
      VectorValuedModularCarrier.Vector vectorCarrier

    SupportedScalarForm :
      ScalarHalfIntegralFormCarrier.ScalarForm scalarCarrier → Set

    vectorImageSupported :
      (form : VectorValuedModularCarrier.Vector vectorCarrier) →
      SupportedScalarForm (vectorToScalar form)

    scalarImageHasPlusSpace :
      (form : VectorValuedModularCarrier.Vector vectorCarrier) →
      ScalarHalfIntegralFormCarrier.plusSpace scalarCarrier
        (Lambency.level (PenumbralLambdency.lambency lambda))
        (vectorToScalar form)

    scalarImageHasLevelFourM :
      (form : VectorValuedModularCarrier.Vector vectorCarrier) →
      ScalarHalfIntegralFormCarrier.modularAtLevelFourTimes scalarCarrier
        (Lambency.level (PenumbralLambdency.lambency lambda))
        (vectorToScalar form)

    ComponentCoefficientAgreement :
      VectorValuedModularCarrier.Vector vectorCarrier →
      PenumbralSupport.DiscriminantIndex support → Set

    componentCoefficientAgreement :
      (form : VectorValuedModularCarrier.Vector vectorCarrier) →
      (index : PenumbralSupport.DiscriminantIndex support) →
      ComponentCoefficientAgreement form index

    vectorRoundTrip :
      (form : VectorValuedModularCarrier.Vector vectorCarrier) →
      scalarToVector (vectorToScalar form) ≡ form

    scalarRoundTripOnSupportedImage :
      (form : ScalarHalfIntegralFormCarrier.ScalarForm scalarCarrier) →
      SupportedScalarForm form →
      vectorToScalar (scalarToVector form) ≡ form

record TwinedThetaComponentDictionary
  (vectorCarrier : VectorValuedModularCarrier)
  (scalarCarrier : ScalarHalfIntegralFormCarrier)
  (arithmetic : LambencyArithmetic)
  {Discriminant : Set}
  (lambda : PenumbralLambdency arithmetic Discriminant)
  (support : PenumbralSupport vectorCarrier arithmetic lambda)
  (dictionary :
    ThetaComponentDictionary
      vectorCarrier scalarCarrier arithmetic lambda support) : Setω where
  field
    G : Set
    vectorTwining :
      G → VectorValuedModularCarrier.Vector vectorCarrier
    scalarTwining :
      G → ScalarHalfIntegralFormCarrier.ScalarForm scalarCarrier

    twiningTransport :
      (g : G) →
      scalarTwining g ≡
      ThetaComponentDictionary.vectorToScalar dictionary
        (vectorTwining g)

record ThetaComponentBoundary : Set where
  field
    residueSupportModuloTwiceLevelRequired : ⊤
    scalarPlusSpaceIsPartOfTheImageCondition : ⊤
    coefficientAgreementMustTrackNormalization : ⊤
    inverseOnlyClaimedOnSupportedImage : ⊤
    noArbitraryScalarSeriesToVectorFormPromotion : ⊤

penumbralThetaComponentBoundary : ThetaComponentBoundary
penumbralThetaComponentBoundary = record
  { residueSupportModuloTwiceLevelRequired = tt
  ; scalarPlusSpaceIsPartOfTheImageCondition = tt
  ; coefficientAgreementMustTrackNormalization = tt
  ; inverseOnlyClaimedOnSupportedImage = tt
  ; noArbitraryScalarSeriesToVectorFormPromotion = tt
  }
