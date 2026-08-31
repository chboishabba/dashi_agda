module DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

import DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationExact as Receipt
import DASHI.Cognition.PNF.SensibLawGWBv01PostCertificationRoadmapExact as Roadmap

------------------------------------------------------------------------
-- Focused validation root for the current SensibLaw runtime state.
------------------------------------------------------------------------

parityFailureCountIsZero :
  Receipt.parityFailed Receipt.gwbV01Parity ≡ zero
parityFailureCountIsZero = refl

parityCoversAllGwbSentences :
  Receipt.parityChecked Receipt.gwbV01Parity
  ≡ Receipt.sentenceCount Receipt.gwbV01Corpus
parityCoversAllGwbSentences = refl

publicationCountIsZero :
  Receipt.publishedGenerations Receipt.gwbV01CertifiedRun ≡ zero
publicationCountIsZero = refl

fullGateIsRecordedPassed :
  Receipt.fullGatePassed Receipt.gwbV01CertifiedRun ≡ true
fullGateIsRecordedPassed = refl

measuredTierIsOnePointTwo :
  Receipt.measuredTier Receipt.gwbV01Timing ≡ Receipt.production1_2x
measuredTierIsOnePointTwo = refl

currentFrontierAwaitsCutoverDecision :
  Roadmap.currentStage Roadmap.currentSensibLawPostGWBFrontier
  ≡ Roadmap.productionCutoverDecision
currentFrontierAwaitsCutoverDecision = refl

universalCutoverStillFalse :
  Roadmap.productionCutoverUniversallyAuthorized
    Roadmap.currentSensibLawPostGWBFrontier
  ≡ false
universalCutoverStillFalse = refl
