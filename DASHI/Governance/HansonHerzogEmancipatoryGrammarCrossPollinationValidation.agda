module DASHI.Governance.HansonHerzogEmancipatoryGrammarCrossPollinationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.EmancipatoryVocabularyRelationalGrammarNoncollapseExact as V
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonHerzogEmancipatoryGrammarCrossPollinationExact as H

genericVocabularyDoesNotDetermineGrammar :
  INF.FactorsThrough V.vocabularyObserver V.grammarOutcome → ⊥
genericVocabularyDoesNotDetermineGrammar =
  V.emancipatoryVocabularyCannotDetermineRelationalGrammar

multiAxisDoesNotDetermineIntersectionality :
  INF.FactorsThrough V.multiAxisObserver V.axisRelationOutcome → ⊥
multiAxisDoesNotDetermineIntersectionality =
  V.multiAxisLanguageDoesNotDetermineIntersectionalGrammar

antiEliteDoesNotDetermineClassGrammar :
  INF.FactorsThrough V.antiEliteObserver V.powerRelationOutcome → ⊥
antiEliteDoesNotDetermineClassGrammar =
  V.antiEliteVocabularyDoesNotDetermineClassGrammar

rightsSecurityDoesNotDetermineRouting :
  INF.FactorsThrough V.rightsSecurityObserver V.routingOutcome → ⊥
rightsSecurityDoesNotDetermineRouting =
  V.rightsLanguageDoesNotDetermineUniversalRouting

hansonFeministVocabularyNotSufficient :
  V.FeministWordsGuaranteeSubjectAuthority → ⊥
hansonFeministVocabularyNotSufficient =
  H.hansonFeministWordsDoNotPaySubjectAuthority

hansonClassVocabularyNotSufficient :
  V.ClassWordsGuaranteeClassAnalysis → ⊥
hansonClassVocabularyNotSufficient =
  H.hansonClassWordsDoNotPayClassAnalysis

hansonIntersectionalVocabularyNotSufficient :
  V.MultiAxisWordsGuaranteeIntersectionality → ⊥
hansonIntersectionalVocabularyNotSufficient =
  H.hansonMultiAxisWordsDoNotPayIntersectionality

protectiveLanguageDoesNotDetermineRouting :
  INF.FactorsThrough H.protectiveLanguageObserver H.protectionRouting → ⊥
protectiveLanguageDoesNotDetermineRouting =
  H.protectiveVocabularyCannotDetermineRouting

makaluRemainsOpen :
  H.currentMakaluStatus ≡ H.independentInvestigationOpen
makaluRemainsOpen = refl

domainsRemainDistinct :
  H.hansonHerzogPoliticalIdentityClaimed
    H.canonicalHansonHerzogVocabularyBoundary
    ≡ false
domainsRemainDistinct =
  H.hansonHerzogPoliticalIdentityClaimedIsFalse
    H.canonicalHansonHerzogVocabularyBoundary

vocabularyStillDoesNotDetermineGrammar :
  H.vocabularyAloneDeterminesGrammar
    H.canonicalHansonHerzogVocabularyBoundary
    ≡ false
vocabularyStillDoesNotDetermineGrammar =
  H.vocabularyAloneDeterminesGrammarIsFalse
    H.canonicalHansonHerzogVocabularyBoundary

protectiveWordsStillDoNotDetermineRouting :
  H.protectiveLanguageAloneDeterminesRouting
    H.canonicalHansonHerzogVocabularyBoundary
    ≡ false
protectiveWordsStillDoNotDetermineRouting =
  H.protectiveLanguageAloneDeterminesRoutingIsFalse
    H.canonicalHansonHerzogVocabularyBoundary

openOversightIsNotFinalAdjudication :
  H.openOversightEqualsFinalAdjudication
    H.canonicalHansonHerzogVocabularyBoundary
    ≡ false
openOversightIsNotFinalAdjudication =
  H.openOversightEqualsFinalAdjudicationIsFalse
    H.canonicalHansonHerzogVocabularyBoundary
