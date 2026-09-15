module DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentBypassFrontierValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as P

bypassFrontierRegression :
  P.ConstituentAttachmentFrontier.wholeCharacterIsotypicBypassSpecified
    P.currentConstituentAttachmentFrontier
  ≡ true
  × P.ConstituentAttachmentFrontier.literalConstituentRouteStillAvailable
    P.currentConstituentAttachmentFrontier
  ≡ true
  × P.ConstituentAttachmentFrontier.literalConstituentAttachmentMandatory
    P.currentConstituentAttachmentFrontier
  ≡ false
  × P.ConstituentAttachmentFrontier.wholeCharacterBypassKernelReceiptObserved
    P.currentConstituentAttachmentFrontier
  ≡ false
bypassFrontierRegression = refl , refl , refl , refl

recognitionStillUnpaidRegression :
  P.ConstituentAttachmentFrontier.sameObjectConstituentAttachmentExists
    P.currentConstituentAttachmentFrontier
  ≡ false
  × P.ConstituentAttachmentFrontier.actualZetaRecognitionUnlocked
    P.currentConstituentAttachmentFrontier
  ≡ false
  × P.ConstituentAttachmentExternalCoordinates.oeisCreatesConstituentDecomposition
    P.canonicalConstituentAttachmentExternalCoordinates
  ≡ false
recognitionStillUnpaidRegression = refl , refl , refl
