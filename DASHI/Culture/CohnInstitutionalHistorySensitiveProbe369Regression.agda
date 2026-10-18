module DASHI.Culture.CohnInstitutionalHistorySensitiveProbe369Regression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalHistorySensitiveProbe369Exact as Bridge

currentStatementDoesNotFixNextProbe :
  Bridge.currentInstitutionalStatementDeterminesNextProbe
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ false
currentStatementDoesNotFixNextProbe = refl

statementPlusConsumerStillDoesNotFixNextProbe :
  Bridge.statementPlusFixedConsumerDeterminesNextProbe
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ false
statementPlusConsumerStillDoesNotFixNextProbe = refl

retainedHistoryMayChangeProbe :
  Bridge.retainedInquiryHistoryMayChangeNextProbe
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ true
retainedHistoryMayChangeProbe = refl

consumerMayIndependentlyChangeProbePath :
  Bridge.declaredConsumerMayChangeProbePath
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ true
consumerMayIndependentlyChangeProbePath = refl

probePolicyDoesNotRewriteEvidence :
  Bridge.probePolicyChangeRewritesCurrentInstitutionalSurface
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ false
probePolicyDoesNotRewriteEvidence = refl

laterConsumerDemandAddsObligation :
  Bridge.laterConsumerDemandCreatesNewObligation
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ true
laterConsumerDemandAddsObligation = refl

laterConsumerDemandDoesNotRefuteEarlierIndexedAnswer :
  Bridge.laterConsumerDemandMakesEarlierIndexedAnswerFalse
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ false
laterConsumerDemandDoesNotRefuteEarlierIndexedAnswer = refl

existing369AndPortfolioOwnersAreReused :
  Bridge.existingSearchOwnersReused ≡ true
existing369AndPortfolioOwnersAreReused = refl
