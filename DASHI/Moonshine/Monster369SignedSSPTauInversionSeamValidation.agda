module DASHI.Moonshine.Monster369SignedSSPTauInversionSeamValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster369SignedSSPTauInversionSeamExact as P

boundaryRegression :
  P.Monster369SignedSSPTauInversionBoundary.signedNegationInvolutive
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ true
  × P.Monster369SignedSSPTauInversionBoundary.frickeInvolutionRetained
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ true
  × P.Monster369SignedSSPTauInversionBoundary.productInversionConstructed
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ true
  × P.Monster369SignedSSPTauInversionBoundary.coarseTritNegationCompatible
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ true
boundaryRegression = refl , refl , refl , refl

firewallRegression :
  P.Monster369SignedSSPTauInversionBoundary.signedSSPIsLiteralFrickeAction
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ false
  × P.Monster369SignedSSPTauInversionBoundary.sameTauCarrierFor6BReplicabilityPaid
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ false
  × P.Monster369SignedSSPTauInversionBoundary.literalMonsterActionWeldPaid
    P.canonicalMonster369SignedSSPTauInversionBoundary
  ≡ false
firewallRegression = refl , refl , refl
