{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBMaxCutRound493Validation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.YangMills.BalabanClayCanonicalBMaxCutRound493Exact as R493

preferredPolicyIsMaxCut :
  R493.preferredBSearchPolicyIsConsumerExposureMaxCut ≡ true
preferredPolicyIsMaxCut =
  R493.preferredBSearchPolicyIsConsumerExposureMaxCutIsTrue

historicalSelectedJMinCutIsNotMandatory :
  R493.historicalSelectedJMinCutMandatory ≡ false
historicalSelectedJMinCutIsNotMandatory =
  R493.historicalSelectedJMinCutMandatoryIsFalse

parallelPhysicalCutIsPreserved :
  R493.maxCutPreservesIndependentWEXTAndHamiltonianPayments ≡ true
parallelPhysicalCutIsPreserved =
  R493.maxCutPreservesIndependentWEXTAndHamiltonianPaymentsIsTrue

maxCutDoesNotManufactureClosure :
  R493.maxCutAutomaticallyProvesEitherPhysicalLeaf ≡ false
maxCutDoesNotManufactureClosure =
  R493.maxCutAutomaticallyProvesEitherPhysicalLeafIsFalse

printedJMisidentificationRemainsBlocked :
  R493.maxCutMayPromotePrintedJObservableIdentification ≡ false
printedJMisidentificationRemainsBlocked =
  R493.maxCutMayPromotePrintedJObservableIdentificationIsFalse

sameHamiltonianPaymentCannotBeDropped :
  R493.maxCutMayDropSameHamiltonianAttachment ≡ false
sameHamiltonianPaymentCannotBeDropped =
  R493.maxCutMayDropSameHamiltonianAttachmentIsFalse

wilsonExtensionPaymentCannotBeDropped :
  R493.maxCutMayDropWilsonExtensionPayment ≡ false
wilsonExtensionPaymentCannotBeDropped =
  R493.maxCutMayDropWilsonExtensionPaymentIsFalse
