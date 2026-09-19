module DASHI.Governance.HansonHerzogEmancipatoryGrammarCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.EmancipatoryVocabularyRelationalGrammarNoncollapseExact as Vocabulary
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonBurqaIslamophobiaFeministRelationalExact as Burqa
import DASHI.Governance.HansonStuntLacanIrigarayGrammarExact as HansonGrammar
import DASHI.Governance.HansonOneNationPoliticalEcologyExact as HansonEcology
import DASHI.Law.HerzogRallyPoliceConductSourceAuditExact as HerzogPolice
import DASHI.Law.HerzogPoliceCountryColonialityCrossPollinationExact as HerzogCountry
import DASHI.Law.HerzogAmalekAttributedSourceAtlasExact as HerzogSources
import DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact as HerzogFascism

------------------------------------------------------------------------
-- HANSON / HERZOG EMANCIPATORY-GRAMMAR CROSS-POLLINATION
--
-- This module does NOT identify the politics, histories, actors or moral/legal
-- positions of the Hanson and Herzog lanes.
--
-- The shared theorem-pattern is only:
--
--   recognisable emancipatory/protective vocabulary
--       !=
--   the relational grammar or realised routing that a consumer may care about.
--
-- Hanson application:
--   women / workers / ordinary people / anti-elite / anti-corporate /
--   multi-axis grievance can be lexically present while subject-authority,
--   class relation, intersectional nonfactorability or reciprocal grammar
--   remain separate questions.
--
-- Herzog/Australia application:
--   solidarity / community safety / antisemitism protection / public order /
--   protest rights / Palestinian solidarity / anti-war / anti-fascist language
--   may all be publicly present while actual policing, correction channels,
--   source provenance and protection burdens remain separate empirical/legal
--   questions.
--
-- No shared vocabulary licenses a shared political verdict.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- HANSON APPLICATIONS
------------------------------------------------------------------------

data HansonVocabularyCase : Set where
  womenRightsCase : HansonVocabularyCase
  workerBattlerCase : HansonVocabularyCase
  antiEliteCase : HansonVocabularyCase
  multiAxisPeopleCase : HansonVocabularyCase
  antiCorporateNationalCase : HansonVocabularyCase

hansonVocabularyKind :
  HansonVocabularyCase → Vocabulary.EmancipatoryVocabularyKind
hansonVocabularyKind womenRightsCase = Vocabulary.feministVocabulary
hansonVocabularyKind workerBattlerCase = Vocabulary.classVocabulary
hansonVocabularyKind antiEliteCase = Vocabulary.antiEliteVocabulary
hansonVocabularyKind multiAxisPeopleCase = Vocabulary.intersectionalVocabulary
hansonVocabularyKind antiCorporateNationalCase = Vocabulary.antiCapitalVocabulary

data HansonGrammarResidual : Set where
  subjectAuthorityResidual : HansonGrammarResidual
  classRelationResidual : HansonGrammarResidual
  intersectionalRelationResidual : HansonGrammarResidual
  elitePowerConsistencyResidual : HansonGrammarResidual
  reciprocalGrammarResidual : HansonGrammarResidual

record HansonVocabularyGrammarAudit : Set where
  constructor hanson-vocabulary-grammar-audit
  field
    case : HansonVocabularyCase
    sourceReference : String
    lexicalSurfacePresent : Bool
    requiredResidual : HansonGrammarResidual
    residualAutomaticallyPaidByVocabulary : Bool
    residualAutomaticallyPaidByVocabularyIsFalse :
      residualAutomaticallyPaidByVocabulary ≡ false
    verdictAutomaticallyIssued : Bool
    verdictAutomaticallyIssuedIsFalse :
      verdictAutomaticallyIssued ≡ false

open HansonVocabularyGrammarAudit public

hansonWomenRightsAudit : HansonVocabularyGrammarAudit
hansonWomenRightsAudit =
  hanson-vocabulary-grammar-audit
    womenRightsCase
    "ABC 2017/2025 Hanson burqa reporting; HansonBurqaIslamophobiaFeministRelationalExact"
    true
    subjectAuthorityResidual
    false refl
    false refl

hansonWorkerBattlerAudit : HansonVocabularyGrammarAudit
hansonWorkerBattlerAudit =
  hanson-vocabulary-grammar-audit
    workerBattlerCase
    "Dyrenfurth/Williams 2026; HansonOneNationPoliticalEcologyExact"
    true
    classRelationResidual
    false refl
    false refl

hansonAntiEliteAudit : HansonVocabularyGrammarAudit
hansonAntiEliteAudit =
  hanson-vocabulary-grammar-audit
    antiEliteCase
    "One Nation public rhetoric and current political-ecology source atlas"
    true
    elitePowerConsistencyResidual
    false refl
    false refl

hansonMultiAxisAudit : HansonVocabularyGrammarAudit
hansonMultiAxisAudit =
  hanson-vocabulary-grammar-audit
    multiAxisPeopleCase
    "DASHI synthesis over class/status/region/gender/nation/culture coordinates"
    true
    intersectionalRelationResidual
    false refl
    false refl

hansonIrigarayAudit : HansonVocabularyGrammarAudit
hansonIrigarayAudit =
  hanson-vocabulary-grammar-audit
    womenRightsCase
    "HansonStuntLacanIrigarayGrammarExact"
    true
    reciprocalGrammarResidual
    false refl
    false refl

------------------------------------------------------------------------
-- Exact Hanson noncollapse adapters to generic owner.
------------------------------------------------------------------------

hansonFeministWordsDoNotPaySubjectAuthority :
  Vocabulary.FeministWordsGuaranteeSubjectAuthority → ⊥
hansonFeministWordsDoNotPaySubjectAuthority =
  Vocabulary.feministWordsDoNotGuaranteeSubjectAuthority

hansonClassWordsDoNotPayClassAnalysis :
  Vocabulary.ClassWordsGuaranteeClassAnalysis → ⊥
hansonClassWordsDoNotPayClassAnalysis =
  Vocabulary.classWordsDoNotGuaranteeClassAnalysis

hansonMultiAxisWordsDoNotPayIntersectionality :
  Vocabulary.MultiAxisWordsGuaranteeIntersectionality → ⊥
hansonMultiAxisWordsDoNotPayIntersectionality =
  Vocabulary.multiAxisWordsDoNotGuaranteeIntersectionality

hansonAntiEliteWordsDoNotPayAntiCapitalism :
  Vocabulary.AntiEliteWordsGuaranteeAntiCapitalism → ⊥
hansonAntiEliteWordsDoNotPayAntiCapitalism =
  Vocabulary.antiEliteWordsDoNotGuaranteeAntiCapitalism

------------------------------------------------------------------------
-- HERZOG / AUSTRALIA APPLICATION
--
-- Current source/state:
--   * 9 February 2026 Sydney anti-Herzog rally
--   * ABC confirms pepper spray and arrests; NSW Police publicly described
--     crowd aggression/assaults; legal observers alleged broader force and
--     direction failures.
--   * LECC Operation Makalu is the independent oversight process.
--   * body-worn footage published September 2026 supplies bounded recorded-
--     utterance evidence, not a final institutional finding.
--
-- These are already source-separated by the imported Law owners.
------------------------------------------------------------------------

data HerzogVocabularyCase : Set where
  jewishCommunitySolidarityCase : HerzogVocabularyCase
  antisemitismProtectionCase : HerzogVocabularyCase
  publicOrderSecurityCase : HerzogVocabularyCase
  protestRightsCase : HerzogVocabularyCase
  palestinianSolidarityCase : HerzogVocabularyCase
  antiWarCase : HerzogVocabularyCase
  antiFascistInterruptionCase : HerzogVocabularyCase

data HerzogRoutingResidual : Set where
  protectionBurdenResidual : HerzogRoutingResidual
  protestFreedomResidual : HerzogRoutingResidual
  policeForceLawfulnessResidual : HerzogRoutingResidual
  correctionChannelResidual : HerzogRoutingResidual
  sourceProvenanceResidual : HerzogRoutingResidual
  civilianDistinctionResidual : HerzogRoutingResidual
  institutionalIntentResidual : HerzogRoutingResidual

record HerzogVocabularyRoutingAudit : Set where
  constructor herzog-vocabulary-routing-audit
  field
    case : HerzogVocabularyCase
    publicVocabulary : String
    sourceReference : String
    requiredResidual : HerzogRoutingResidual
    vocabularyDeterminesRouting : Bool
    vocabularyDeterminesRoutingIsFalse :
      vocabularyDeterminesRouting ≡ false
    finalLegalFindingClaimed : Bool
    finalLegalFindingClaimedIsFalse :
      finalLegalFindingClaimed ≡ false

open HerzogVocabularyRoutingAudit public

herzogCommunitySolidarityAudit : HerzogVocabularyRoutingAudit
herzogCommunitySolidarityAudit =
  herzog-vocabulary-routing-audit
    jewishCommunitySolidarityCase
    "solidarity/support for Australian Jewish community after Bondi attack"
    "public government/Herzog visit framing; separate from police-operation lawfulness"
    protectionBurdenResidual
    false refl
    false refl

herzogPublicOrderAudit : HerzogVocabularyRoutingAudit
herzogPublicOrderAudit =
  herzog-vocabulary-routing-audit
    publicOrderSecurityCase
    "public order / officer safety / crowd volatility"
    "HerzogRallyPoliceConductSourceAuditExact policeOfficialAccount receipts"
    policeForceLawfulnessResidual
    false refl
    false refl

herzogProtestRightsAudit : HerzogVocabularyRoutingAudit
herzogProtestRightsAudit =
  herzog-vocabulary-routing-audit
    protestRightsCase
    "political protest / assembly / march"
    "anti-Herzog protest and associated legal/oversight source owners"
    protestFreedomResidual
    false refl
    false refl

herzogAntiFascistAudit : HerzogVocabularyRoutingAudit
herzogAntiFascistAudit =
  herzog-vocabulary-routing-audit
    antiFascistInterruptionCase
    "anti-fascist interruption / preserve distinctions and correction"
    "HerzogFascismAntifascistAmalekCrossPollinationExact"
    correctionChannelResidual
    false refl
    false refl

herzogProvenanceAudit : HerzogVocabularyRoutingAudit
herzogProvenanceAudit =
  herzog-vocabulary-routing-audit
    publicOrderSecurityCase
    "security/public-order account"
    "HerzogAmalekAttributedSourceAtlasExact; media-hosted leak distinct from original police custody"
    sourceProvenanceResidual
    false refl
    false refl

------------------------------------------------------------------------
-- Current oversight state is deliberately OPEN.
------------------------------------------------------------------------

data MakaluStatus : Set where
  independentInvestigationOpen : MakaluStatus
  finalPublicFindingAvailable : MakaluStatus

currentMakaluStatus : MakaluStatus
currentMakaluStatus = independentInvestigationOpen

currentMakaluSourceReference : String
currentMakaluSourceReference =
  "Law Enforcement Conduct Commission, Operation Makalu investigation progress update, 15 September 2026: investigation continuing; public examinations not held in September due to procedural issues"

bodycamCurrentSourceReference : String
bodycamCurrentSourceReference =
  "ABC News, 1 September 2026: leaked/body-worn vision shows officers discussing striking a protester; LECC investigation remains the independent closure route"

data OpenInvestigationEqualsFinalFinding : Set where

makaluOpenDoesNotEqualFinalFinding :
  OpenInvestigationEqualsFinalFinding → ⊥
makaluOpenDoesNotEqualFinalFinding ()

------------------------------------------------------------------------
-- Shared comparator theorem: same protective vocabulary can hide different
-- routing. This is structural only; it does not say Hanson == Herzog or that
-- either application instantiates the synthetic states below.
------------------------------------------------------------------------

data ProtectiveLanguageState : Set where
  protectionRoutedUniversally : ProtectiveLanguageState
  protectionRoutedAsymmetrically : ProtectiveLanguageState

data SameProtectiveLanguage : Set where
  safetyRightsSolidarity : SameProtectiveLanguage

data ProtectionRouting : Set where
  symmetricProtection : ProtectionRouting
  asymmetricProtection : ProtectionRouting

protectiveLanguageObserver :
  ProtectiveLanguageState → SameProtectiveLanguage
protectiveLanguageObserver protectionRoutedUniversally = safetyRightsSolidarity
protectiveLanguageObserver protectionRoutedAsymmetrically = safetyRightsSolidarity

protectionRouting : ProtectiveLanguageState → ProtectionRouting
protectionRouting protectionRoutedUniversally = symmetricProtection
protectionRouting protectionRoutedAsymmetrically = asymmetricProtection

protectionRoutingDiffers :
  protectionRouting protectionRoutedUniversally
  ≡ protectionRouting protectionRoutedAsymmetrically → ⊥
protectionRoutingDiffers ()

protectiveVocabularyCannotDetermineRouting :
  INF.FactorsThrough protectiveLanguageObserver protectionRouting → ⊥
protectiveVocabularyCannotDetermineRouting =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      protectionRoutedUniversally
      protectionRoutedAsymmetrically
      refl
      protectionRoutingDiffers)

------------------------------------------------------------------------
-- NO CROSS-DOMAIN IDENTITY
------------------------------------------------------------------------

data HansonEqualsHerzogPolitics : Set where
data HansonStuntEqualsHerzogPoliceOperation : Set where
data SharedVocabularyFailureMeansSameIdeology : Set where
data ProtesterVocabularyAutomaticallyProvesConduct : Set where
data GovernmentSecurityVocabularyAutomaticallyProvesLawfulness : Set where

hansonDoesNotEqualHerzogPolitics :
  HansonEqualsHerzogPolitics → ⊥
hansonDoesNotEqualHerzogPolitics ()

stuntDoesNotEqualPoliceOperation :
  HansonStuntEqualsHerzogPoliceOperation → ⊥
stuntDoesNotEqualPoliceOperation ()

sharedPatternDoesNotMakeSameIdeology :
  SharedVocabularyFailureMeansSameIdeology → ⊥
sharedPatternDoesNotMakeSameIdeology ()

protesterWordsDoNotAutomaticallyProveConduct :
  ProtesterVocabularyAutomaticallyProvesConduct → ⊥
protesterWordsDoNotAutomaticallyProveConduct ()

securityWordsDoNotAutomaticallyProveLawfulness :
  GovernmentSecurityVocabularyAutomaticallyProvesLawfulness → ⊥
securityWordsDoNotAutomaticallyProveLawfulness ()

------------------------------------------------------------------------
-- ENDPOINT
------------------------------------------------------------------------

record HansonHerzogVocabularyBoundary : Set where
  constructor hanson-herzog-vocabulary-boundary
  field
    genericVocabularyGrammarTheoremReused : Bool
    hansonApplicationsSourceBounded : Bool
    herzogApplicationsSourceBounded : Bool
    currentMakaluInvestigationOpen : Bool
    currentMakaluInvestigationOpenIsTrue :
      currentMakaluInvestigationOpen ≡ true
    hansonHerzogPoliticalIdentityClaimed : Bool
    hansonHerzogPoliticalIdentityClaimedIsFalse :
      hansonHerzogPoliticalIdentityClaimed ≡ false
    vocabularyAloneDeterminesGrammar : Bool
    vocabularyAloneDeterminesGrammarIsFalse :
      vocabularyAloneDeterminesGrammar ≡ false
    protectiveLanguageAloneDeterminesRouting : Bool
    protectiveLanguageAloneDeterminesRoutingIsFalse :
      protectiveLanguageAloneDeterminesRouting ≡ false
    openOversightEqualsFinalAdjudication : Bool
    openOversightEqualsFinalAdjudicationIsFalse :
      openOversightEqualsFinalAdjudication ≡ false

open HansonHerzogVocabularyBoundary public

canonicalHansonHerzogVocabularyBoundary :
  HansonHerzogVocabularyBoundary
canonicalHansonHerzogVocabularyBoundary =
  hanson-herzog-vocabulary-boundary
    true
    true
    true
    true refl
    false refl
    false refl
    false refl
    false refl
