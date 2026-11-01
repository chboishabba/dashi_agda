module DASHI.Wikimedia.IbrahimMonster3BSimpleSubobjectClassificationLeanReceiptValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BSimpleSubobjectClassificationLeanReceiptExact as P

sourceRegression :
  P.SimpleSubobjectClassificationBoundary.sourceWritten
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ true
  × P.SimpleSubobjectClassificationBoundary.nonzeroSimpleSourceClassificationWritten
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ true
sourceRegression = refl , refl

nonPromotionRegression :
  P.SimpleSubobjectClassificationBoundary.leanKernelReceiptObserved
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
  × P.SimpleSubobjectClassificationBoundary.isotypicAssemblyPaid
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
  × P.SimpleSubobjectClassificationBoundary.oeisCreatesClassification
    P.canonicalSimpleSubobjectClassificationBoundary
  ≡ false
nonPromotionRegression = refl , refl , refl
