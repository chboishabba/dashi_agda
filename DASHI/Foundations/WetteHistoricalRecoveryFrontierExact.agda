module DASHI.Foundations.WetteHistoricalRecoveryFrontierExact where

------------------------------------------------------------------------
-- WETTE HISTORICAL RECOVERY FRONTIER
--
-- The generic architecture is now mostly present.  The remaining high-value
-- work is source extraction: identify the exact historical objects needed to
-- instantiate the existing formal interfaces rather than inventing replacements.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.WetteHistoricalSourceAtlasExact as Source

------------------------------------------------------------------------
-- What must be recovered from the historical corpus.
------------------------------------------------------------------------

data RecoveryObject : Set where
  formulaGrammar : RecoveryObject
  generatorVocabulary : RecoveryObject
  admissibilityOrLegality : RecoveryObject
  axiomOrBaseState : RecoveryObject
  codingConvention : RecoveryObject
  relativeCompletenessMeaning : RecoveryObject
  consistencySentence : RecoveryObject
  contradictionSentence : RecoveryObject
  consistencyToContradictionReduction : RecoveryObject
  comparisonArithmetic : RecoveryObject
  comparisonTranslation : RecoveryObject
  contradictionPreservation : RecoveryObject
  semanticOrReflectionBridge : RecoveryObject

record RecoveryTarget : Set where
  constructor recoveryTarget
  field
    object : RecoveryObject
    preferredSource : Source.WetteSource
    recovered : Bool
    recoveryIsSourceExact : Bool

open RecoveryTarget public

------------------------------------------------------------------------
-- Priority targets.
--
-- 1969 is the main construction source.  The 1970 retrospective is valuable
-- for Wette's own programmatic description.  The 1974 contradiction paper is
-- the best currently verified target for the consistency deduction, while the
-- reported 1974 canonical-system and 1976 simplification abstracts are marked
-- as pending primary verification in the source atlas.
------------------------------------------------------------------------

grammarTarget : RecoveryTarget
grammarTarget =
  recoveryTarget
    formulaGrammar
    Source.wette1969ConstructiveArithmetic
    false false

generatorTarget : RecoveryTarget
generatorTarget =
  recoveryTarget
    generatorVocabulary
    Source.wette1969ConstructiveArithmetic
    false false

admissibilityTarget : RecoveryTarget
admissibilityTarget =
  recoveryTarget
    admissibilityOrLegality
    Source.wette1969ConstructiveArithmetic
    false false

baseStateTarget : RecoveryTarget
baseStateTarget =
  recoveryTarget
    axiomOrBaseState
    Source.wette1969ConstructiveArithmetic
    false false

codingTarget : RecoveryTarget
codingTarget =
  recoveryTarget
    codingConvention
    Source.wette1969ConstructiveArithmetic
    false false

relativeCompletenessTarget : RecoveryTarget
relativeCompletenessTarget =
  recoveryTarget
    relativeCompletenessMeaning
    Source.wette1969ConstructiveArithmetic
    false false

consistencySentenceTarget : RecoveryTarget
consistencySentenceTarget =
  recoveryTarget
    consistencySentence
    Source.wette1974Contradiction
    false false

contradictionSentenceTarget : RecoveryTarget
contradictionSentenceTarget =
  recoveryTarget
    contradictionSentence
    Source.wette1974Contradiction
    false false

reductionTarget : RecoveryTarget
reductionTarget =
  recoveryTarget
    consistencyToContradictionReduction
    Source.wette1974Contradiction
    false false

comparisonArithmeticTarget : RecoveryTarget
comparisonArithmeticTarget =
  recoveryTarget
    comparisonArithmetic
    Source.wette1974CanonicalSystemAbstract
    false false

comparisonTranslationTarget : RecoveryTarget
comparisonTranslationTarget =
  recoveryTarget
    comparisonTranslation
    Source.wette1974CanonicalSystemAbstract
    false false

contradictionPreservationTarget : RecoveryTarget
contradictionPreservationTarget =
  recoveryTarget
    contradictionPreservation
    Source.wette1974CanonicalSystemAbstract
    false false

semanticBridgeTarget : RecoveryTarget
semanticBridgeTarget =
  recoveryTarget
    semanticOrReflectionBridge
    Source.bernays1971Commentary
    false false

------------------------------------------------------------------------
-- Recovery sequencing is dependency-aware rather than vocabulary-driven.
------------------------------------------------------------------------

record WetteHistoricalRecoveryBoundary : Set where
  constructor wetteHistoricalRecoveryBoundary
  field
    genericArchitectureAlreadyAvailable : Bool
    genericArchitectureAlreadyAvailableIsTrue :
      genericArchitectureAlreadyAvailable ≡ true

    exactHistoricalGrammarRecovered : Bool
    exactHistoricalGrammarRecoveredIsFalse :
      exactHistoricalGrammarRecovered ≡ false

    exactHistoricalConsistencyReductionRecovered : Bool
    exactHistoricalConsistencyReductionRecoveredIsFalse :
      exactHistoricalConsistencyReductionRecovered ≡ false

    exactHistoricalComparisonTranslationRecovered : Bool
    exactHistoricalComparisonTranslationRecoveredIsFalse :
      exactHistoricalComparisonTranslationRecovered ≡ false

    relativeCompletenessShouldBeDefinedBeforeSourceRecovery : Bool
    relativeCompletenessShouldBeDefinedBeforeSourceRecoveryIsFalse :
      relativeCompletenessShouldBeDefinedBeforeSourceRecovery ≡ false

    sourceExtractionPrecedesTheoremDischarge : Bool
    sourceExtractionPrecedesTheoremDischargeIsTrue :
      sourceExtractionPrecedesTheoremDischarge ≡ true

canonicalWetteHistoricalRecoveryBoundary : WetteHistoricalRecoveryBoundary
canonicalWetteHistoricalRecoveryBoundary =
  wetteHistoricalRecoveryBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
