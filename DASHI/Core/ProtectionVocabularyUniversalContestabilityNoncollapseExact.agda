module DASHI.Core.ProtectionVocabularyUniversalContestabilityNoncollapseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- PROTECTION VOCABULARY != UNIVERSAL / CONTESTABLE PROTECTION GRAMMAR
--
-- Generic DASHI theorem owner.
--
-- A public claim framed in the vocabulary of safety, security, solidarity,
-- minority protection, anti-hatred, public order, counter-extremism, national
-- resilience or community defence does not, by its lexical form alone,
-- determine:
--
--   * who is protected;
--   * who bears the burden;
--   * whether protection is symmetric or selective;
--   * whether the protected/observed subject can inspect/correct/appeal;
--   * whether provenance survives;
--   * whether independent correction remains open;
--   * whether surveillance/observation has legitimate intervention authority.
--
-- This owner is source-neutral. Political/legal/technical applications need
-- separate source receipts and must not infer motive, ideology or legality from
-- the finite witnesses below.
------------------------------------------------------------------------

data ProtectionVocabularyKind : Set where
  communitySafetyVocabulary : ProtectionVocabularyKind
  antisemitismProtectionVocabulary : ProtectionVocabularyKind
  antiRacismProtectionVocabulary : ProtectionVocabularyKind
  publicOrderVocabulary : ProtectionVocabularyKind
  nationalSecurityVocabulary : ProtectionVocabularyKind
  antiExtremismVocabulary : ProtectionVocabularyKind
  protestSafetyVocabulary : ProtectionVocabularyKind
  dataSecurityVocabulary : ProtectionVocabularyKind
  fraudPreventionVocabulary : ProtectionVocabularyKind
  solidarityVocabulary : ProtectionVocabularyKind

data ProtectionGrammarKind : Set where
  universalEqualStandingProtection : ProtectionGrammarKind
  selectiveInsiderProtection : ProtectionGrammarKind
  symmetricRightsBurden : ProtectionGrammarKind
  asymmetricSecurityBurden : ProtectionGrammarKind
  contestableObservationGrammar : ProtectionGrammarKind
  noncontestableObservationGrammar : ProtectionGrammarKind
  provenancePreservingProtection : ProtectionGrammarKind
  provenanceCollapsingProtection : ProtectionGrammarKind
  correctionOpenProtection : ProtectionGrammarKind
  correctionClosedProtection : ProtectionGrammarKind

record ProtectionClaimSurface : Set where
  constructor protection-claim-surface
  field
    vocabulary : ProtectionVocabularyKind
    publicLabel : String
    sourceReference : String
    sourceOwnsVocabulary : Bool

open ProtectionClaimSurface public

------------------------------------------------------------------------
-- Same protection words, different routing.
------------------------------------------------------------------------

data ProtectionRoutingState : Set where
  universalRoutingState : ProtectionRoutingState
  selectiveRoutingState : ProtectionRoutingState

data ProtectionWords : Set where
  sameProtectionWords : ProtectionWords

data ProtectionRoutingOutcome : Set where
  universalRouting : ProtectionRoutingOutcome
  selectiveRouting : ProtectionRoutingOutcome

protectionVocabularyObserver : ProtectionRoutingState → ProtectionWords
protectionVocabularyObserver universalRoutingState = sameProtectionWords
protectionVocabularyObserver selectiveRoutingState = sameProtectionWords

protectionRoutingOutcome :
  ProtectionRoutingState → ProtectionRoutingOutcome
protectionRoutingOutcome universalRoutingState = universalRouting
protectionRoutingOutcome selectiveRoutingState = selectiveRouting

routingDiffers :
  protectionRoutingOutcome universalRoutingState
  ≡ protectionRoutingOutcome selectiveRoutingState → ⊥
routingDiffers ()

protectionVocabularyCannotDetermineUniversalRouting :
  INF.FactorsThrough protectionVocabularyObserver protectionRoutingOutcome → ⊥
protectionVocabularyCannotDetermineUniversalRouting =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      universalRoutingState selectiveRoutingState refl routingDiffers)

------------------------------------------------------------------------
-- Same security words, different contestability.
------------------------------------------------------------------------

data ContestabilityState : Set where
  inspectCorrectAppealState : ContestabilityState
  observedWithoutSubjectContestabilityState : ContestabilityState

data SecurityWords : Set where
  sameSecurityWords : SecurityWords

data ContestabilityOutcome : Set where
  subjectContestabilityInstalled : ContestabilityOutcome
  subjectContestabilityMissing : ContestabilityOutcome

securityVocabularyObserver : ContestabilityState → SecurityWords
securityVocabularyObserver inspectCorrectAppealState = sameSecurityWords
securityVocabularyObserver observedWithoutSubjectContestabilityState =
  sameSecurityWords

contestabilityOutcome : ContestabilityState → ContestabilityOutcome
contestabilityOutcome inspectCorrectAppealState =
  subjectContestabilityInstalled
contestabilityOutcome observedWithoutSubjectContestabilityState =
  subjectContestabilityMissing

contestabilityDiffers :
  contestabilityOutcome inspectCorrectAppealState
  ≡ contestabilityOutcome observedWithoutSubjectContestabilityState → ⊥
contestabilityDiffers ()

securityVocabularyCannotDetermineContestability :
  INF.FactorsThrough securityVocabularyObserver contestabilityOutcome → ⊥
securityVocabularyCannotDetermineContestability =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      inspectCorrectAppealState
      observedWithoutSubjectContestabilityState
      refl
      contestabilityDiffers)

------------------------------------------------------------------------
-- Same safety words, different correction channel.
------------------------------------------------------------------------

data CorrectionState : Set where
  correctionOpenState : CorrectionState
  correctionClosedState : CorrectionState

data SafetyWords : Set where
  sameSafetyWords : SafetyWords

data CorrectionOutcome : Set where
  independentCorrectionOpen : CorrectionOutcome
  correctionChannelClosed : CorrectionOutcome

safetyVocabularyObserver : CorrectionState → SafetyWords
safetyVocabularyObserver correctionOpenState = sameSafetyWords
safetyVocabularyObserver correctionClosedState = sameSafetyWords

correctionOutcome : CorrectionState → CorrectionOutcome
correctionOutcome correctionOpenState = independentCorrectionOpen
correctionOutcome correctionClosedState = correctionChannelClosed

correctionDiffers :
  correctionOutcome correctionOpenState
  ≡ correctionOutcome correctionClosedState → ⊥
correctionDiffers ()

safetyVocabularyCannotDetermineCorrection :
  INF.FactorsThrough safetyVocabularyObserver correctionOutcome → ⊥
safetyVocabularyCannotDetermineCorrection =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      correctionOpenState correctionClosedState refl correctionDiffers)

------------------------------------------------------------------------
-- Positive repair: add routing / contestability / provenance residuals.
------------------------------------------------------------------------

data ProtectionResidual : Set where
  protectedPopulationResidual : ProtectionResidual
  burdenPopulationResidual : ProtectionResidual
  routingSymmetryResidual : ProtectionResidual
  inspectionResidual : ProtectionResidual
  correctionResidual : ProtectionResidual
  appealResidual : ProtectionResidual
  provenanceResidual : ProtectionResidual
  independentReviewResidual : ProtectionResidual

record ProtectionResidualRepair
    {Situated Surface : Set}
    (observe : Situated → Surface) : Set₁ where
  constructor protection-residual-repair
  field
    residual : Situated → ProtectionResidual
    left right : Situated
    oldCollision : observe left ≡ observe right
    residualSeparates : residual left ≡ residual right → ⊥

open ProtectionResidualRepair public

protectionRepairStrictlyRefinesVocabularyObserver :
  ∀ {Situated Surface : Set}
    {observe : Situated → Surface} →
  (repair : ProtectionResidualRepair observe) →
  Observer.StrictRefinement
    observe
    (Observer.pairObserver observe (residual repair))
protectionRepairStrictlyRefinesVocabularyObserver {observe = observe} repair =
  Observer.strictPairRefinement
    observe
    (residual repair)
    (left repair)
    (right repair)
    (oldCollision repair)
    (residualSeparates repair)

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ProtectionWordsGuaranteeUniversalRouting : Set where
data SecurityWordsGuaranteeContestability : Set where
data SafetyWordsGuaranteeCorrection : Set where
data SurveillanceVisibilityCreatesAuthority : Set where
data ProtectionIntentCreatesLegalAuthority : Set where
data MinorityProtectionForOneGroupProvesUniversalism : Set where

protectionWordsDoNotGuaranteeUniversalRouting :
  ProtectionWordsGuaranteeUniversalRouting → ⊥
protectionWordsDoNotGuaranteeUniversalRouting ()

securityWordsDoNotGuaranteeContestability :
  SecurityWordsGuaranteeContestability → ⊥
securityWordsDoNotGuaranteeContestability ()

safetyWordsDoNotGuaranteeCorrection :
  SafetyWordsGuaranteeCorrection → ⊥
safetyWordsDoNotGuaranteeCorrection ()

visibilityDoesNotCreateAuthority :
  SurveillanceVisibilityCreatesAuthority → ⊥
visibilityDoesNotCreateAuthority ()

protectiveIntentDoesNotCreateLegalAuthority :
  ProtectionIntentCreatesLegalAuthority → ⊥
protectiveIntentDoesNotCreateLegalAuthority ()

oneGroupProtectionDoesNotProveUniversalism :
  MinorityProtectionForOneGroupProvesUniversalism → ⊥
oneGroupProtectionDoesNotProveUniversalism ()

record ProtectionVocabularyBoundary : Set where
  constructor protection-vocabulary-boundary
  field
    vocabularyRoutingSeparated : Bool
    vocabularyRoutingSeparatedIsTrue :
      vocabularyRoutingSeparated ≡ true
    vocabularyContestabilitySeparated : Bool
    vocabularyContestabilitySeparatedIsTrue :
      vocabularyContestabilitySeparated ≡ true
    vocabularyCorrectionSeparated : Bool
    vocabularyCorrectionSeparatedIsTrue :
      vocabularyCorrectionSeparated ≡ true
    protectionResidualsRequired : Bool
    protectionResidualsRequiredIsTrue :
      protectionResidualsRequired ≡ true
    observationCreatesAuthority : Bool
    observationCreatesAuthorityIsFalse :
      observationCreatesAuthority ≡ false
    protectiveIntentCreatesLegalAuthority : Bool
    protectiveIntentCreatesLegalAuthorityIsFalse :
      protectiveIntentCreatesLegalAuthority ≡ false
    oneProtectedGroupProvesUniversalProtection : Bool
    oneProtectedGroupProvesUniversalProtectionIsFalse :
      oneProtectedGroupProvesUniversalProtection ≡ false

canonicalProtectionVocabularyBoundary : ProtectionVocabularyBoundary
canonicalProtectionVocabularyBoundary =
  protection-vocabulary-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
