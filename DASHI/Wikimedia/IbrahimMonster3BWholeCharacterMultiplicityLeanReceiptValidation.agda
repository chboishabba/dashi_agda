module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterMultiplicityLeanReceiptValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BWholeCharacterMultiplicityLeanReceiptExact as P

sourceRegression :
  P.WholeCharacterMultiplicityLeanBoundary.sourceWritten
    P.canonicalWholeCharacterMultiplicityLeanBoundary
  ≡ true
  × P.WholeCharacterMultiplicityLeanBoundary.targetMultiplicityLemmaWritten
    P.canonicalWholeCharacterMultiplicityLeanBoundary
  ≡ true
  × P.WholeCharacterMultiplicityLeanBoundary.otherSimpleMultiplicityZeroLemmaWritten
    P.canonicalWholeCharacterMultiplicityLeanBoundary
  ≡ true
sourceRegression = refl , refl , refl

nonPromotionRegression :
  P.WholeCharacterMultiplicityLeanBoundary.wholeCharacterIsotypicTheoremPaid
    P.canonicalWholeCharacterMultiplicityLeanBoundary
  ≡ false
  × P.WholeCharacterMultiplicityLeanBoundary.leanKernelReceiptObserved
    P.canonicalWholeCharacterMultiplicityLeanBoundary
  ≡ false
  × P.WholeCharacterMultiplicityLeanBoundary.oeisCreatesMultiplicityTheorem
    P.canonicalWholeCharacterMultiplicityLeanBoundary
  ≡ false
nonPromotionRegression = refl , refl , refl
