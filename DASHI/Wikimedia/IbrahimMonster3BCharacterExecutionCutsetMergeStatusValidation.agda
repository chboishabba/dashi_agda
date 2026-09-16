module DASHI.Wikimedia.IbrahimMonster3BCharacterExecutionCutsetMergeStatusValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BCharacterExecutionCutsetSnowballExact as P

mergeStatusRegression :
  P.LeanCharacterExecutionReceipt.sourceWritten
    P.currentLeanCharacterExecutionReceipt
  ≡ true
  × P.LeanCharacterExecutionReceipt.sourceImportedByDefaultTarget
    P.currentLeanCharacterExecutionReceipt
  ≡ true
  × P.LeanCharacterExecutionReceipt.pullRequestOpen
    P.currentLeanCharacterExecutionReceipt
  ≡ false
  × P.LeanCharacterExecutionReceipt.sourceMergedToMain
    P.currentLeanCharacterExecutionReceipt
  ≡ true
  × P.LeanCharacterExecutionReceipt.workflowRunObservedForHead
    P.currentLeanCharacterExecutionReceipt
  ≡ false
  × P.LeanCharacterExecutionReceipt.kernelSuccessObserved
    P.currentLeanCharacterExecutionReceipt
  ≡ false
mergeStatusRegression = refl , refl , refl , refl , refl , refl

oeisExecutionFirewallRegression :
  P.CutsetAttributionCoordinates.oeisPaysCharacterIso
    P.canonicalCutsetAttributionCoordinates
  ≡ false
  × P.CutsetAttributionCoordinates.oeisPaysActualAction
    P.canonicalCutsetAttributionCoordinates
  ≡ false
oeisExecutionFirewallRegression = refl , refl
