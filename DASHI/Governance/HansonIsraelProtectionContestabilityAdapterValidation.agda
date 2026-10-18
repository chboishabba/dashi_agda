module DASHI.Governance.HansonIsraelProtectionContestabilityAdapterValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ProtectionVocabularyUniversalContestabilityNoncollapseExact as Protection
import DASHI.Governance.HansonIsraelProtectionContestabilityAdapterExact as H

genericProtectionWordsDoNotDetermineRouting :
  INF.FactorsThrough
    Protection.protectionVocabularyObserver
    Protection.protectionRoutingOutcome → ⊥
genericProtectionWordsDoNotDetermineRouting =
  Protection.protectionVocabularyCannotDetermineUniversalRouting

genericSecurityWordsDoNotDetermineContestability :
  INF.FactorsThrough
    Protection.securityVocabularyObserver
    Protection.contestabilityOutcome → ⊥
genericSecurityWordsDoNotDetermineContestability =
  Protection.securityVocabularyCannotDetermineContestability

genericSafetyWordsDoNotDetermineCorrection :
  INF.FactorsThrough
    Protection.safetyVocabularyObserver
    Protection.correctionOutcome → ⊥
genericSafetyWordsDoNotDetermineCorrection =
  Protection.safetyVocabularyCannotDetermineCorrection

hansonCommunityProtectionNotUniversalism :
  INF.FactorsThrough
    H.hansonProtectionObserver
    H.hansonProtectionOutcome → ⊥
hansonCommunityProtectionNotUniversalism =
  H.hansonCommunitySafetyDoesNotDetermineUniversalism

palantirSecurityNotContestability :
  INF.FactorsThrough
    H.palantirSecurityObserver
    H.palantirContestabilityOutcome → ⊥
palantirSecurityNotContestability =
  H.palantirSecurityCapabilityDoesNotDetermineContestability

vocabularyUniversalismFlagFalse :
  H.vocabularyCreatesUniversalism
    H.canonicalProtectionContestabilityAdapterBoundary
    ≡ false
vocabularyUniversalismFlagFalse =
  H.vocabularyCreatesUniversalismIsFalse
    H.canonicalProtectionContestabilityAdapterBoundary

securityContestabilityFlagFalse :
  H.securityCapabilityCreatesContestability
    H.canonicalProtectionContestabilityAdapterBoundary
    ≡ false
securityContestabilityFlagFalse =
  H.securityCapabilityCreatesContestabilityIsFalse
    H.canonicalProtectionContestabilityAdapterBoundary
