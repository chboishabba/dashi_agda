module DASHI.Culture.WittgensteinUsePracticeSourceBridgeExact where

------------------------------------------------------------------------
-- WITTGENSTEIN USE / PRACTICE / FORM-OF-LIFE SOURCE BRIDGE
--
-- Source-attribution rule:
--
--   Wittgenstein proposition
--   != later interpreter's proposition
--   != DASHI formalisation pattern
--   != finite DASHI non-factorability theorem.
--
-- Primary work reference:
--   Ludwig Wittgenstein, Philosophical Investigations, especially §§23, 43,
--   241–242.  The bounded source roles represented here are:
--
--   * §43: for a large class of cases (not all), meaning is investigated
--     through use in language;
--   * §23: speaking language is represented as part of an activity / form
--     of life;
--   * §§241–242: agreement relevant to language is not reduced to explicit
--     definitions alone.
--
-- Recovery calibration used for this repository tranche:
--   Stanford Encyclopedia of Philosophy, "Ludwig Wittgenstein",
--   sections on meaning as use, language-games, rule-following and form of
--   life.  This is a secondary recovery aid, not a replacement primary text.
--
-- The exact finite collision theorems below are DASHI constructions.  They
-- are NOT attributed to Wittgenstein.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact as WitchUse
import DASHI.Culture.WitchRelationalAttributionDialogueBidiExact as Dialogue
import DASHI.Culture.HistoricalSocialTotalityBidiExact as Totality

------------------------------------------------------------------------
-- 1. Source roles and bounded propositions.
------------------------------------------------------------------------

data PhilosophySourceRole : Set where
  primaryWorkReference
  secondaryRecoveryAid
  repositoryInterpretiveBridge
  repositoryFiniteTheorem
  : PhilosophySourceRole

data WittgensteinTopic : Set where
  meaningUseTopic
  languageGameTopic
  activityFormOfLifeTopic
  ruleFollowingTopic
  agreementPracticeTopic
  : WittgensteinTopic

record WittgensteinSourceProposition : Set where
  constructor wittgenstein-source-proposition
  field
    topic : WittgensteinTopic
    sourceRole : PhilosophySourceRole
    sourceLocation : String
    boundedParaphrase : String
    universalised : Bool
    repositoryTheoremAttributedToSource : Bool

open WittgensteinSourceProposition public

meaningUse43 : WittgensteinSourceProposition
meaningUse43 = wittgenstein-source-proposition
  meaningUseTopic primaryWorkReference "Philosophical Investigations §43"
  "for a large class of cases, meaning is investigated through use in language; the qualification is retained"
  false false

languageGame23 : WittgensteinSourceProposition
languageGame23 = wittgenstein-source-proposition
  activityFormOfLifeTopic primaryWorkReference "Philosophical Investigations §23"
  "speaking language is treated as part of activity and a form of life"
  false false

agreement241242 : WittgensteinSourceProposition
agreement241242 = wittgenstein-source-proposition
  agreementPracticeTopic primaryWorkReference "Philosophical Investigations §§241–242"
  "linguistic practice is not reduced to agreement in explicit definitions alone"
  false false

secondaryRecovery : WittgensteinSourceProposition
secondaryRecovery = wittgenstein-source-proposition
  languageGameTopic secondaryRecoveryAid
  "Stanford Encyclopedia of Philosophy: Ludwig Wittgenstein, later-Wittgenstein sections"
  "secondary recovery of the meaning/use, language-game, rule-following and form-of-life source locations"
  false false

------------------------------------------------------------------------
-- 2. Same sentence surface does not generically recover use/practice.
--
-- This is a DASHI finite theorem, not a theorem of Wittgenstein.
------------------------------------------------------------------------

data UtteranceState : Set where
  devotionalUse
  historicalReportUse
  politicalReclamationUse
  hostileAccusationUse
  : UtteranceState

data UtteranceSurface : Set where sameWords : UtteranceSurface

data PracticeUseCode : Set where
  devotionalCode
  historicalReportCode
  reclamationCode
  accusationCode
  : PracticeUseCode

utteranceSurface : UtteranceState → UtteranceSurface
utteranceSurface devotionalUse = sameWords
utteranceSurface historicalReportUse = sameWords
utteranceSurface politicalReclamationUse = sameWords
utteranceSurface hostileAccusationUse = sameWords

practiceUse : UtteranceState → PracticeUseCode
practiceUse devotionalUse = devotionalCode
practiceUse historicalReportUse = historicalReportCode
practiceUse politicalReclamationUse = reclamationCode
practiceUse hostileAccusationUse = accusationCode

devotionalAndHistoricalDiffer :
  practiceUse devotionalUse ≡ practiceUse historicalReportUse → ⊥
devotionalAndHistoricalDiffer ()

sameWordsCannotRecoverPracticeUse :
  INF.FactorsThrough utteranceSurface practiceUse → ⊥
sameWordsCannotRecoverPracticeUse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      devotionalUse
      historicalReportUse
      refl
      devotionalAndHistoricalDiffer)

------------------------------------------------------------------------
-- 3. Same vocabulary/use code does not recover whole historical totality.
--
-- Use/practice is one coordinate of situated social life; it is not a
-- decoder for institution, authority, material relation or history.
------------------------------------------------------------------------

data SituatedPracticeState : Set where
  localVoluntaryPractice
  stateBackedPractice
  diasporicMinorityPractice
  reclaimedCounterPractice
  : SituatedPracticeState

data SharedPracticeSurface : Set where sharedRitualVocabulary : SharedPracticeSurface

data HistoricalPositionCode : Set where
  localVoluntaryCode
  stateBackedCode
  diasporicMinorityCode
  counterPracticeCode
  : HistoricalPositionCode

sharedPractice : SituatedPracticeState → SharedPracticeSurface
sharedPractice localVoluntaryPractice = sharedRitualVocabulary
sharedPractice stateBackedPractice = sharedRitualVocabulary
sharedPractice diasporicMinorityPractice = sharedRitualVocabulary
sharedPractice reclaimedCounterPractice = sharedRitualVocabulary

historicalPosition : SituatedPracticeState → HistoricalPositionCode
historicalPosition localVoluntaryPractice = localVoluntaryCode
historicalPosition stateBackedPractice = stateBackedCode
historicalPosition diasporicMinorityPractice = diasporicMinorityCode
historicalPosition reclaimedCounterPractice = counterPracticeCode

localAndStateBackedDiffer :
  historicalPosition localVoluntaryPractice ≡ historicalPosition stateBackedPractice → ⊥
localAndStateBackedDiffer ()

samePracticeCannotRecoverHistoricalPosition :
  INF.FactorsThrough sharedPractice historicalPosition → ⊥
samePracticeCannotRecoverHistoricalPosition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      localVoluntaryPractice
      stateBackedPractice
      refl
      localAndStateBackedDiffer)

------------------------------------------------------------------------
-- 4. Source / interpretation / theorem layers are constructor-distinct.
------------------------------------------------------------------------

data AttributionLayer : Set where
  sourceTextLayer
  secondaryInterpretationLayer
  repositoryBridgeLayer
  finiteTheoremLayer
  : AttributionLayer

sourceNotFiniteTheorem : sourceTextLayer ≡ finiteTheoremLayer → ⊥
sourceNotFiniteTheorem ()

secondaryNotSource : secondaryInterpretationLayer ≡ sourceTextLayer → ⊥
secondaryNotSource ()

bridgeNotSource : repositoryBridgeLayer ≡ sourceTextLayer → ⊥
bridgeNotSource ()

------------------------------------------------------------------------
-- 5. Cross-pollination receipt.
--
-- We consume existing DASHI theorem surfaces as theorem surfaces only.
-- Their structural affinity with later-Wittgenstein themes does not transfer
-- authorship of those theorems to Wittgenstein.
------------------------------------------------------------------------

record WittgensteinUsePracticeCrossPollinationReceipt : Set where
  constructor wittgenstein-use-practice-cross-pollination-receipt
  field
    witchPredicateUseBoundary : WitchUse.WitchSelfIdentificationBoundary
    relationalDialogueBoundary : Dialogue.WitchRelationalAttributionBoundary
    historicalTotalityBoundary : Totality.HistoricalSocialTotalityBoundary
    sameWordsPracticeNonfactorability : INF.FactorsThrough utteranceSurface practiceUse → ⊥
    samePracticeHistoryNonfactorability : INF.FactorsThrough sharedPractice historicalPosition → ⊥
    sourceSectionsRecovered : Bool
    secondaryRecoveryKeptSeparate : Bool
    finiteTheoremsAreDASHIConstructions : Bool
    noEmpiricalPopulationClaimInherited : Bool

canonicalWittgensteinUsePracticeCrossPollinationReceipt :
  WittgensteinUsePracticeCrossPollinationReceipt
canonicalWittgensteinUsePracticeCrossPollinationReceipt =
  wittgenstein-use-practice-cross-pollination-receipt
    WitchUse.canonicalWitchSelfIdentificationBoundary
    Dialogue.canonicalWitchRelationalAttributionBoundary
    Totality.canonicalHistoricalSocialTotalityBoundary
    sameWordsCannotRecoverPracticeUse
    samePracticeCannotRecoverHistoricalPosition
    true true true true

------------------------------------------------------------------------
-- 6. No-promotion gates.
------------------------------------------------------------------------

data MeaningUsePromotesLexicalRelativism : Set where
data LanguageGamePromotesWholeSocialTotality : Set where
data FormOfLifePromotesCivilisationalEssence : Set where
data SharedUsePromotesSharedPrivateBelief : Set where
data SharedPracticePromotesSharedAutonomy : Set where
data WittgensteinPromotesDASHINonfactorability : Set where
\meaningUseDoesNotPromoteLexicalRelativism : MeaningUsePromotesLexicalRelativism → ⊥
meaningUseDoesNotPromoteLexicalRelativism ()

languageGameDoesNotPromoteWholeSocialTotality : LanguageGamePromotesWholeSocialTotality → ⊥
languageGameDoesNotPromoteWholeSocialTotality ()

formOfLifeDoesNotPromoteCivilisationalEssence : FormOfLifePromotesCivilisationalEssence → ⊥
formOfLifeDoesNotPromoteCivilisationalEssence ()

sharedUseDoesNotPromoteSharedPrivateBelief : SharedUsePromotesSharedPrivateBelief → ⊥
sharedUseDoesNotPromoteSharedPrivateBelief ()

sharedPracticeDoesNotPromoteSharedAutonomy : SharedPracticePromotesSharedAutonomy → ⊥
sharedPracticeDoesNotPromoteSharedAutonomy ()

wittgensteinDoesNotPromoteDASHINonfactorability : WittgensteinPromotesDASHINonfactorability → ⊥
wittgensteinDoesNotPromoteDASHINonfactorability ()

------------------------------------------------------------------------
-- 7. Canonical boundary.
------------------------------------------------------------------------

record WittgensteinUsePracticeBoundary : Set where
  constructor wittgenstein-use-practice-boundary
  field
    meaningUseClaimIsQualified : Bool
    sameSentenceDeterminesSameUse : Bool
    sameVocabularyDeterminesHistoricalPosition : Bool
    languageGameEqualsWholeHistoricalTotality : Bool
    formOfLifeEqualsCivilisationalEssence : Bool
    sharedUseDeterminesPrivateBelief : Bool
    sharedPracticeDeterminesAutonomy : Bool
    secondaryInterpretationEqualsPrimarySource : Bool
    sourcePropositionEqualsDASHITheorem : Bool
    sourceAttributionSurvivesCrossPollination : Bool

canonicalWittgensteinUsePracticeBoundary : WittgensteinUsePracticeBoundary
canonicalWittgensteinUsePracticeBoundary =
  wittgenstein-use-practice-boundary
    true false false false false false false false false true
