module DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationLeanMergeReceiptValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationMathlibProducerSnowballExact as P

sourceReceiptRegression :
  P.EqualCharacterIsoCorollaryRoute.leanWrapperSourceWritten
    P.currentEqualCharacterIsoCorollaryRoute
  ≡ true
  × P.LeanWrapperRepositoryReceipt.sourceMergedToMain
    P.canonicalLeanWrapperRepositoryReceipt
  ≡ true
  × P.LeanWrapperRepositoryReceipt.workflowRunObservedAtMerge
    P.canonicalLeanWrapperRepositoryReceipt
  ≡ false
sourceReceiptRegression = refl , refl , refl

certificationFirewallRegression :
  P.EqualCharacterIsoCorollaryRoute.leanKernelReceiptObserved
    P.currentEqualCharacterIsoCorollaryRoute
  ≡ false
  × P.EqualCharacterIsoCorollaryRoute.agdaTransportReceiptObserved
    P.currentEqualCharacterIsoCorollaryRoute
  ≡ false
  × P.MathlibCharacterDeterminationSnowballFrontier.equalCharacterLeanCorollaryKernelPaid
    P.currentMathlibCharacterDeterminationSnowballFrontier
  ≡ false
  × P.MathlibCharacterDeterminationSnowballFrontier.oeisCorrectlyMarkedNonAuthoritative
    P.currentMathlibCharacterDeterminationSnowballFrontier
  ≡ true
certificationFirewallRegression = refl , refl , refl , refl
