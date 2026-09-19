module DASHI.Core.EmancipatoryVocabularyRelationalGrammarNoncollapseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- EMANCIPATORY VOCABULARY != EMANCIPATORY RELATIONAL GRAMMAR
--
-- Generic DASHI theorem owner.
--
-- Motivation: political actors and institutions can use lexical resources
-- associated with emancipation -- feminism, class, anti-elite critique,
-- anti-racism, anti-colonialism, worker protection, plural identity, security,
-- rights, solidarity -- without thereby inhabiting the relational grammar of
-- the source tradition from which those words are recognisable.
--
-- This module is source-neutral. It does not classify any actor, ideology,
-- party, protest, movement or institution. Applications must supply their own
-- source receipts and must keep vocabulary, grammar, realised routing and
-- political/legal evaluation separately typed.
------------------------------------------------------------------------

data EmancipatoryVocabularyKind : Set where
  feministVocabulary : EmancipatoryVocabularyKind
  classVocabulary : EmancipatoryVocabularyKind
  antiCapitalVocabulary : EmancipatoryVocabularyKind
  antiEliteVocabulary : EmancipatoryVocabularyKind
  antiRacistVocabulary : EmancipatoryVocabularyKind
  antiColonialVocabulary : EmancipatoryVocabularyKind
  intersectionalVocabulary : EmancipatoryVocabularyKind
  workerProtectionVocabulary : EmancipatoryVocabularyKind
  rightsVocabulary : EmancipatoryVocabularyKind
  securityVocabulary : EmancipatoryVocabularyKind
  solidarityVocabulary : EmancipatoryVocabularyKind

data RelationalGrammarKind : Set where
  originatingSubjectAuthorityGrammar : RelationalGrammarKind
  reciprocalNonSovereignGrammar : RelationalGrammarKind
  classRelationGrammar : RelationalGrammarKind
  intersectionalNonfactorabilityGrammar : RelationalGrammarKind
  antiTerminalisationGrammar : RelationalGrammarKind
  reopenableCorrectionGrammar : RelationalGrammarKind
  universalEqualStandingGrammar : RelationalGrammarKind
  provenancePreservingGrammar : RelationalGrammarKind
  insiderOutsiderAllocationGrammar : RelationalGrammarKind
  oneCentredRepresentationGrammar : RelationalGrammarKind

record VocabularyUse : Set where
  constructor vocabulary-use
  field
    vocabularyKind : EmancipatoryVocabularyKind
    publicLabel : String
    sourceReference : String
    sourceOwnsLexicalUse : Bool
    dashiOwnsRelationalInterpretation : Bool

open VocabularyUse public

record GrammarAudit : Set where
  constructor grammar-audit
  field
    grammarKind : RelationalGrammarKind
    relationReading : String
    originatingSubjectAuthorityRetained : Bool
    reciprocalAuthorityRetained : Bool
    classPowerRelationRetained : Bool
    intersectingAxesRetained : Bool
    correctionChannelRetained : Bool
    provenanceRetained : Bool
    insiderOutsiderBoundaryIntroduced : Bool
    oneCentrePrivileged : Bool

open GrammarAudit public

------------------------------------------------------------------------
-- Same vocabulary can inhabit different grammars.
------------------------------------------------------------------------

data VocabularyGrammarState : Set where
  sameWordsDifferentGrammarA : VocabularyGrammarState
  sameWordsDifferentGrammarB : VocabularyGrammarState

data VocabularySurface : Set where
  sameEmancipatoryLexicon : VocabularySurface

data GrammarOutcome : Set where
  relationallyExpanded : GrammarOutcome
  relationallyCompressed : GrammarOutcome

vocabularyObserver : VocabularyGrammarState → VocabularySurface
vocabularyObserver sameWordsDifferentGrammarA = sameEmancipatoryLexicon
vocabularyObserver sameWordsDifferentGrammarB = sameEmancipatoryLexicon

grammarOutcome : VocabularyGrammarState → GrammarOutcome
grammarOutcome sameWordsDifferentGrammarA = relationallyExpanded
grammarOutcome sameWordsDifferentGrammarB = relationallyCompressed

grammarOutcomeDiffers :
  grammarOutcome sameWordsDifferentGrammarA
  ≡ grammarOutcome sameWordsDifferentGrammarB → ⊥
grammarOutcomeDiffers ()

sameVocabularyDifferentGrammarWitness :
  INF.NonFactorabilityWitness vocabularyObserver grammarOutcome
sameVocabularyDifferentGrammarWitness =
  INF.nonFactorabilityWitness
    sameWordsDifferentGrammarA
    sameWordsDifferentGrammarB
    refl
    grammarOutcomeDiffers

emancipatoryVocabularyCannotDetermineRelationalGrammar :
  INF.FactorsThrough vocabularyObserver grammarOutcome → ⊥
emancipatoryVocabularyCannotDetermineRelationalGrammar =
  INF.witnessRulesOutEveryFlatFactorisation
    sameVocabularyDifferentGrammarWitness

------------------------------------------------------------------------
-- Multi-axis language != intersectionality.
------------------------------------------------------------------------

data MultiAxisSurface : Set where
  classGenderRaceNationMentioned : MultiAxisSurface

data AxisRelationOutcome : Set where
  axesRetainedRelationally : AxisRelationOutcome
  axesCollapsedIntoAuthenticPeople : AxisRelationOutcome

data MultiAxisState : Set where
  intersectionalState : MultiAxisState
  compositeIdentityState : MultiAxisState

multiAxisObserver : MultiAxisState → MultiAxisSurface
multiAxisObserver intersectionalState = classGenderRaceNationMentioned
multiAxisObserver compositeIdentityState = classGenderRaceNationMentioned

axisRelationOutcome : MultiAxisState → AxisRelationOutcome
axisRelationOutcome intersectionalState = axesRetainedRelationally
axisRelationOutcome compositeIdentityState = axesCollapsedIntoAuthenticPeople

axisRelationDiffers :
  axisRelationOutcome intersectionalState
  ≡ axisRelationOutcome compositeIdentityState → ⊥
axisRelationDiffers ()

multiAxisLanguageDoesNotDetermineIntersectionalGrammar :
  INF.FactorsThrough multiAxisObserver axisRelationOutcome → ⊥
multiAxisLanguageDoesNotDetermineIntersectionalGrammar =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      intersectionalState compositeIdentityState refl axisRelationDiffers)

------------------------------------------------------------------------
-- Anti-elite language != class-relational analysis.
------------------------------------------------------------------------

data AntiEliteSurface : Set where
  ordinaryPeopleVersusElites : AntiEliteSurface

data PowerRelationOutcome : Set where
  ownershipClassRelationRetained : PowerRelationOutcome
  eliteOutsiderPeopleTriad : PowerRelationOutcome

data AntiEliteState : Set where
  classRelationalAntiElite : AntiEliteState
  produceristAntiElite : AntiEliteState

antiEliteObserver : AntiEliteState → AntiEliteSurface
antiEliteObserver classRelationalAntiElite = ordinaryPeopleVersusElites
antiEliteObserver produceristAntiElite = ordinaryPeopleVersusElites

powerRelationOutcome : AntiEliteState → PowerRelationOutcome
powerRelationOutcome classRelationalAntiElite = ownershipClassRelationRetained
powerRelationOutcome produceristAntiElite = eliteOutsiderPeopleTriad

powerRelationDiffers :
  powerRelationOutcome classRelationalAntiElite
  ≡ powerRelationOutcome produceristAntiElite → ⊥
powerRelationDiffers ()

antiEliteVocabularyDoesNotDetermineClassGrammar :
  INF.FactorsThrough antiEliteObserver powerRelationOutcome → ⊥
antiEliteVocabularyDoesNotDetermineClassGrammar =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      classRelationalAntiElite produceristAntiElite refl powerRelationDiffers)

------------------------------------------------------------------------
-- Rights/security language can also route differently.
------------------------------------------------------------------------

data RightsSecuritySurface : Set where
  rightsAndSafetyClaim : RightsSecuritySurface

data RoutingOutcome : Set where
  universalRightsRoute : RoutingOutcome
  asymmetricProtectedTargetRoute : RoutingOutcome

data RightsSecurityState : Set where
  universalRightsState : RightsSecurityState
  asymmetricSecurityState : RightsSecurityState

rightsSecurityObserver : RightsSecurityState → RightsSecuritySurface
rightsSecurityObserver universalRightsState = rightsAndSafetyClaim
rightsSecurityObserver asymmetricSecurityState = rightsAndSafetyClaim

routingOutcome : RightsSecurityState → RoutingOutcome
routingOutcome universalRightsState = universalRightsRoute
routingOutcome asymmetricSecurityState = asymmetricProtectedTargetRoute

routingOutcomeDiffers :
  routingOutcome universalRightsState
  ≡ routingOutcome asymmetricSecurityState → ⊥
routingOutcomeDiffers ()

rightsLanguageDoesNotDetermineUniversalRouting :
  INF.FactorsThrough rightsSecurityObserver routingOutcome → ⊥
rightsLanguageDoesNotDetermineUniversalRouting =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      universalRightsState asymmetricSecurityState refl routingOutcomeDiffers)

------------------------------------------------------------------------
-- Positive repair must add grammar-relevant information.
------------------------------------------------------------------------

data GrammarResidual : Set where
  subjectAuthorityResidual : GrammarResidual
  classRelationResidual : GrammarResidual
  intersectionalRelationResidual : GrammarResidual
  correctionChannelResidual : GrammarResidual
  provenanceResidual : GrammarResidual
  routingSymmetryResidual : GrammarResidual

record GrammarResidualRepair
    {Situated Surface : Set}
    (observe : Situated → Surface) : Set₁ where
  constructor grammar-residual-repair
  field
    residual : Situated → GrammarResidual
    left right : Situated
    oldCollision : observe left ≡ observe right
    residualSeparates : residual left ≡ residual right → ⊥

open GrammarResidualRepair public

grammarRepairStrictlyRefinesVocabularyObserver :
  ∀ {Situated Surface : Set}
    {observe : Situated → Surface} →
  (repair : GrammarResidualRepair observe) →
  Observer.StrictRefinement
    observe
    (Observer.pairObserver observe (residual repair))
grammarRepairStrictlyRefinesVocabularyObserver {observe = observe} repair =
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

data FeministWordsGuaranteeSubjectAuthority : Set where
data ClassWordsGuaranteeClassAnalysis : Set where
data MultiAxisWordsGuaranteeIntersectionality : Set where
data AntiEliteWordsGuaranteeAntiCapitalism : Set where
data RightsWordsGuaranteeUniversalRightsRouting : Set where
data SecurityWordsGuaranteeSymmetricProtection : Set where
data EmancipatoryLexiconGuaranteesEmancipatoryOutcome : Set where

feministWordsDoNotGuaranteeSubjectAuthority :
  FeministWordsGuaranteeSubjectAuthority → ⊥
feministWordsDoNotGuaranteeSubjectAuthority ()

classWordsDoNotGuaranteeClassAnalysis :
  ClassWordsGuaranteeClassAnalysis → ⊥
classWordsDoNotGuaranteeClassAnalysis ()

multiAxisWordsDoNotGuaranteeIntersectionality :
  MultiAxisWordsGuaranteeIntersectionality → ⊥
multiAxisWordsDoNotGuaranteeIntersectionality ()

antiEliteWordsDoNotGuaranteeAntiCapitalism :
  AntiEliteWordsGuaranteeAntiCapitalism → ⊥
antiEliteWordsDoNotGuaranteeAntiCapitalism ()

rightsWordsDoNotGuaranteeUniversalRouting :
  RightsWordsGuaranteeUniversalRightsRouting → ⊥
rightsWordsDoNotGuaranteeUniversalRightsRouting ()

securityWordsDoNotGuaranteeSymmetricProtection :
  SecurityWordsGuaranteeSymmetricProtection → ⊥
securityWordsDoNotGuaranteeSymmetricProtection ()

emancipatoryLexiconDoesNotGuaranteeEmancipatoryOutcome :
  EmancipatoryLexiconGuaranteesEmancipatoryOutcome → ⊥
emancipatoryLexiconDoesNotGuaranteeEmancipatoryOutcome ()

record EmancipatoryVocabularyBoundary : Set where
  constructor emancipatory-vocabulary-boundary
  field
    vocabularyAndGrammarSeparated : Bool
    vocabularyAndGrammarSeparatedIsTrue :
      vocabularyAndGrammarSeparated ≡ true
    multiAxisAndIntersectionalSeparated : Bool
    multiAxisAndIntersectionalSeparatedIsTrue :
      multiAxisAndIntersectionalSeparated ≡ true
    antiEliteAndClassAnalysisSeparated : Bool
    antiEliteAndClassAnalysisSeparatedIsTrue :
      antiEliteAndClassAnalysisSeparated ≡ true
    rightsAndRoutingSeparated : Bool
    rightsAndRoutingSeparatedIsTrue :
      rightsAndRoutingSeparated ≡ true
    grammarRepairNeedsAdditionalInformation : Bool
    grammarRepairNeedsAdditionalInformationIsTrue :
      grammarRepairNeedsAdditionalInformation ≡ true
    lexicalSimilarityProvesHistoricalLineage : Bool
    lexicalSimilarityProvesHistoricalLineageIsFalse :
      lexicalSimilarityProvesHistoricalLineage ≡ false
    sharedFormalPatternProvesSamePolitics : Bool
    sharedFormalPatternProvesSamePoliticsIsFalse :
      sharedFormalPatternProvesSamePolitics ≡ false

canonicalEmancipatoryVocabularyBoundary :
  EmancipatoryVocabularyBoundary
canonicalEmancipatoryVocabularyBoundary =
  emancipatory-vocabulary-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
