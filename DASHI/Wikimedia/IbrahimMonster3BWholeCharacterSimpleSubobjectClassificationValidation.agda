module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterSimpleSubobjectClassificationValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BWholeCharacterSimpleSubobjectClassificationExact as P

sourceRegression :
  P.SimpleSubobjectClassificationBoundary.leanSourceWritten
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ true
  × P.SimpleSubobjectClassificationBoundary.classifiesOnlySimpleSourcesWithNonzeroHom
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ true
  × P.SimpleSubobjectClassificationBoundary.semisimpleAssemblyWritten
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
sourceRegression = refl , refl , refl

certificationRegression :
  P.SimpleSubobjectClassificationBoundary.leanKernelReceiptObserved
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
  × P.SimpleSubobjectClassificationBoundary.agdaTransportObserved
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
  × P.SimpleSubobjectClassificationBoundary.actualMonsterSameObjectRecognitionPaid
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
certificationRegression = refl , refl , refl

consumerBoundaryRegression :
  P.SimpleSubobjectClassificationBoundary.literalConstituentEnumerationLogicallyMandatoryAfterClassifier
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
  × P.SimpleSubobjectClassificationBoundary.multiplicityNinetyPaid
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
  × P.SimpleSubobjectClassificationBoundary.concreteWeylBasisActionRecognitionPaid
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
consumerBoundaryRegression = refl , refl , refl
