module DASHI.Wikimedia.IbrahimMonster3BRecognizedLinearZetaSameObjectValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BRecognizedLinearZetaSameObjectExact as P

paidInterfaceRegression :
  P.RecognizedLinearZetaBoundary.recognitionInterfaceAvailable
    P.currentRecognizedLinearZetaBoundary
  ≡ true
  × P.RecognizedLinearZetaBoundary.linearZetaInterfaceAvailable
    P.currentRecognizedLinearZetaBoundary
  ≡ true
  × P.RecognizedLinearZetaBoundary.sameSelectedProducerEqualityRequired
    P.currentRecognizedLinearZetaBoundary
  ≡ true
  × P.RecognizedLinearZetaBoundary.sameLiteralZetaCarrierEqualityRequired
    P.currentRecognizedLinearZetaBoundary
  ≡ true
paidInterfaceRegression = refl , refl , refl , refl

unpaidWitnessRegression :
  P.RecognizedLinearZetaBoundary.recognitionInhabitantPaid
    P.currentRecognizedLinearZetaBoundary
  ≡ false
  × P.RecognizedLinearZetaBoundary.recognizedLinearSameObjectInhabitantPaid
    P.currentRecognizedLinearZetaBoundary
  ≡ false
  × P.RecognizedLinearZetaBoundary.selectedNormalizerMonsterActionWeldPaid
    P.currentRecognizedLinearZetaBoundary
  ≡ false
  × P.RecognizedLinearZetaBoundary.oeisHasRecognitionAuthority
    P.currentRecognizedLinearZetaBoundary
  ≡ false
unpaidWitnessRegression = refl , refl , refl , refl
