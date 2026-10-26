module DASHI.Foundations.Base369T4SymplecticExteriorSquareE6BridgeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369T4SymplecticExteriorSquareE6BridgeExact as Bridge

pairCountPinned : Bridge.orderedIsotropicIndependentPairCount ≡ 1920
pairCountPinned = refl

orientedLagCountPinned : Bridge.orientedLagrangianBivectorCount ≡ 80
orientedLagCountPinned = refl

projectiveLagCountPinned : Bridge.projectiveLagrangianLineCount ≡ 40
projectiveLagCountPinned = refl

nullCountPinned : Bridge.standardNonzeroNullCount ≡ 80
nullCountPinned = refl

projectiveNullCountPinned : Bridge.projectiveNullPointCount ≡ 40
projectiveNullCountPinned = refl

symplecticPrimitiveOwnerPaid :
  Bridge.T4ExteriorSquareE6BridgeBoundary.symplecticPrimitiveIdentityKernelPaid
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ true
symplecticPrimitiveOwnerPaid = refl

recognitionInterfacesPresent :
  Bridge.T4ExteriorSquareE6BridgeBoundary.sameActionRecognitionInterfaceDefined
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ true
recognitionInterfacesPresent = refl

finiteCertificatePresent :
  Bridge.T4ExteriorSquareE6BridgeBoundary.exhaustiveFiniteCertificateScriptPresent
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ true
finiteCertificatePresent = refl

countStillComputationalNotKernel :
  Bridge.T4ExteriorSquareE6BridgeBoundary.orientedBivectorCount80KernelPaidHere
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ false
countStillComputationalNotKernel = refl

matrixImageStillComputationalNotKernel :
  Bridge.T4ExteriorSquareE6BridgeBoundary.pgsp4EqualsWeylE6MatrixImageKernelPaidHere
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ false
matrixImageStillComputationalNotKernel = refl

rawT4PromotionRejected :
  Bridge.T4ExteriorSquareE6BridgeBoundary.rawPuncturedT4IdentifiedWithDerivedLag80
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ false
rawT4PromotionRejected = refl

cardinalityPromotionRejected :
  Bridge.T4ExteriorSquareE6BridgeBoundary.cardinalityAlonePromotesRecognition
    Bridge.canonicalT4ExteriorSquareE6BridgeBoundary
  ≡ false
cardinalityPromotionRejected = refl
