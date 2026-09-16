module DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentLeanSourceReceiptValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as P

sourceFrontierRegression :
  P.ConstituentAttachmentFrontier.equalIrreducibleCharacterProducerLocated
    P.currentConstituentAttachmentFrontier
  ≡ true
  × P.ConstituentAttachmentFrontier.equalIrreducibleCharacterSourceMerged
    P.currentConstituentAttachmentFrontier
  ≡ true
  × P.ConstituentAttachmentFrontier.leanEqualCharacterKernelReceiptObserved
    P.currentConstituentAttachmentFrontier
  ≡ false
sourceFrontierRegression = refl , refl , refl

oeisFirewallRegression :
  P.ConstituentAttachmentExternalCoordinates.oeisCreatesConstituentDecomposition
    P.canonicalConstituentAttachmentExternalCoordinates
  ≡ false
  × P.ConstituentAttachmentFrontier.sameObjectConstituentAttachmentExists
    P.currentConstituentAttachmentFrontier
  ≡ false
  × P.ConstituentAttachmentFrontier.actualZetaRecognitionUnlocked
    P.currentConstituentAttachmentFrontier
  ≡ false
oeisFirewallRegression = refl , refl , refl
