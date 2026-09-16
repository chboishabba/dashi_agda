module DASHI.Culture.CohnInstitutionalHistorySensitiveProbe369Regression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalHistorySensitiveProbe369Exact as Bridge

currentStatementDoesNotFixNextProbe :
  Bridge.currentInstitutionalStatementDeterminesNextProbe
    Bridge.canonicalHistorySensitiveProbeBoundary ≡ false
currentStatementDoesNotFixNextProbe = refl

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

existing369AndPortfolioOwnersAreReused :
  Bridge.existingSearchOwnersReused ≡ true
existing369AndPortfolioOwnersAreReused = refl
