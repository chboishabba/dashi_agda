module DASHI.Wikimedia.IbrahimSnowballQiHexagramWitchDivinationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballRitualMythCommunityInstitutionExact as Ritual
import DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact as Witch
import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing
import DASHI.Biology.DASHIYijingRelationalOperatorsExact as YijingRelational
import DASHI.Biology.PsychogeographicHexagramObservationExact as Psychogeographic

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
-- qi / Yijing / hexagram / divination / witch-self-description
--      <-> symbolic systems / ritual / interpretation / cultural practice
--      <-> knowledge / prediction / empirical evaluation.
--
-- A symbol, traditional term, cast, self-description, interpretation and
-- empirical proposition are distinct source/consumer roles.  External QIDs
-- pay identity/navigation only; they do not import received semantics,
-- metaphysical truth, predictive validity, community membership or authority.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim qi/hexagram/witch/divination BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; no interpretation, metaphysics, prediction, affiliation or authority promotion")

qiQid : Identity.ExternalIdentityDemand
qiQid = mkQid "qi (Chinese philosophical/cultural concept)" "Q202742"

yijingQid : Identity.ExternalIdentityDemand
yijingQid = mkQid "I Ching / Yijing" "Q181937"

hexagramQid : Identity.ExternalIdentityDemand
hexagramQid = mkQid "I Ching hexagram" "Q1572403"

eightTrigramsQid : Identity.ExternalIdentityDemand
eightTrigramsQid = mkQid "eight trigrams / bagua" "Q340846"

yinYangQid : Identity.ExternalIdentityDemand
yinYangQid = mkQid "yin and yang" "Q62744"

divinationQid : Identity.ExternalIdentityDemand
divinationQid = mkQid "divination" "Q1043197"

witchcraftQid : Identity.ExternalIdentityDemand
witchcraftQid = mkQid "witchcraft" "Q259745"

wiccaQid : Identity.ExternalIdentityDemand
wiccaQid = mkQid "Wicca" "Q59774"

witchPersonQid : Identity.ExternalIdentityDemand
witchPersonQid = Identity.mkOptionalIdentityDemand
  "Ibrahim qi/hexagram/witch/divination BIDI"
  "external person/category identity"
  "witch (person/self-identification category)"
  Identity.wikidataQid
  (Identity.unresolved "no exact person/self-identification concept QID safely promoted in this pass; witchcraft, Wicca, accused-witch history and present self-description remain separate")

------------------------------------------------------------------------
-- Attributed scholarship.  Historical/interpretive scholarship pays only
-- bounded claims about traditions, textual layers and use.
------------------------------------------------------------------------

adlerYijingSource : Attribution.AttributedSource
adlerYijingSource = Attribution.mkDOISource
  "Joseph A. Adler"
  "The Yijing: A Guide"
  "Oxford University Press"
  "2022"
  "10.1093/oso/9780190072452.001.0001"
  "https://doi.org/10.1093/oso/9780190072452.001.0001"
  Attribution.academicBookSource
  "historical and religious-studies guide to the Yijing, its textual layers, divination and interpretive traditions; not empirical proof of external prediction"
  Attribution.publicAttribution

adlerDivinationChapterSource : Attribution.AttributedSource
adlerDivinationChapterSource = Attribution.mkDOISource
  "Joseph A. Adler"
  "Yijing Divination"
  "The Yijing: A Guide, chapter 3"
  "2022"
  "10.1093/oso/9780190072452.003.0003"
  "https://doi.org/10.1093/oso/9780190072452.003.0003"
  Attribution.academicChapterSource
  "source-bounded history of Yijing consultation methods and religious practice; does not establish predictive validity"
  Attribution.publicAttribution

adlerInterpretationChapterSource : Attribution.AttributedSource
adlerInterpretationChapterSource = Attribution.mkDOISource
  "Joseph A. Adler"
  "The Early History of Yijing Interpretation"
  "The Yijing: A Guide, chapter 4"
  "2022"
  "10.1093/oso/9780190072452.003.0004"
  "https://doi.org/10.1093/oso/9780190072452.003.0004"
  Attribution.academicChapterSource
  "documents multiple historical interpretive schools and techniques; supports interpretation-provenance plurality rather than one timeless reading"
  Attribution.publicAttribution

liQiSource : Attribution.AttributedSource
liQiSource = Attribution.mkDOISource
  "Li Cunshan"
  "A differentiation of the meaning of qi on several levels"
  "Frontiers of Philosophy in China 3(2):194-212"
  "2008"
  "10.1007/s11466-008-0013-y"
  "https://doi.org/10.1007/s11466-008-0013-y"
  Attribution.academicArticleSource
  "source-bounded philosophical analysis distinguishing multiple historical/semantic levels of qi; not a bridge from traditional qi vocabulary to a modern physical measurement"
  Attribution.publicAttribution

zeitlynDivinationSource : Attribution.AttributedSource
zeitlynDivinationSource = Attribution.mkDOISource
  "David Zeitlyn"
  "Finding Meaning in the Text: The Process of Interpretation in Text-Based Divination"
  "Journal of the Royal Anthropological Institute 7(2):225-240"
  "2001"
  "10.1111/1467-9655.00060"
  "https://doi.org/10.1111/1467-9655.00060"
  Attribution.academicArticleSource
  "anthropological analysis of text-based divination as situated interpretive practice; does not establish supernatural or predictive truth"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: a hexagram token does not determine its situated reading.
------------------------------------------------------------------------

data HexagramCase : Set where
  sameHexagramReadingA sameHexagramReadingB : HexagramCase

data HexagramSurface : Set where sameHexagramToken : HexagramSurface
data HexagramReadingRole : Set where historicalCommentaryReading situatedConsultationReading : HexagramReadingRole

hexagramSurface : HexagramCase → HexagramSurface
hexagramSurface _ = sameHexagramToken

hexagramReadingRole : HexagramCase → HexagramReadingRole
hexagramReadingRole sameHexagramReadingA = historicalCommentaryReading
hexagramReadingRole sameHexagramReadingB = situatedConsultationReading

hexagramReadingDefect : INF.NonFactorabilityWitness hexagramSurface hexagramReadingRole
hexagramReadingDefect = INF.nonFactorabilityWitness sameHexagramReadingA sameHexagramReadingB refl (λ ())

hexagramTokenCannotFactorSituatedInterpretation :
  INF.FactorsThrough hexagramSurface hexagramReadingRole → ⊥
hexagramTokenCannotFactorSituatedInterpretation =
  INF.witnessRulesOutEveryFlatFactorisation hexagramReadingDefect

------------------------------------------------------------------------
-- Regression 2: one qi token cannot recover semantic/evidentiary role.
------------------------------------------------------------------------

data QiCase : Set where
  sameQiClassicalPhilosophical sameQiModernEmpiricalClaim : QiCase

data QiSurface : Set where sameQiToken : QiSurface
data QiRole : Set where classicalPhilosophicalRole modernEmpiricalClaimRole : QiRole

qiSurface : QiCase → QiSurface
qiSurface _ = sameQiToken

qiRole : QiCase → QiRole
qiRole sameQiClassicalPhilosophical = classicalPhilosophicalRole
qiRole sameQiModernEmpiricalClaim = modernEmpiricalClaimRole

qiRoleDefect : INF.NonFactorabilityWitness qiSurface qiRole
qiRoleDefect = INF.nonFactorabilityWitness sameQiClassicalPhilosophical sameQiModernEmpiricalClaim refl (λ ())

qiTokenCannotFactorSemanticEvidenceRole : INF.FactorsThrough qiSurface qiRole → ⊥
qiTokenCannotFactorSemanticEvidenceRole = INF.witnessRulesOutEveryFlatFactorisation qiRoleDefect

------------------------------------------------------------------------
-- Regression 3: structural/associative divination reading does not determine
-- external predictive validation.
------------------------------------------------------------------------

data DivinationCase : Set where
  sameAssociativeReadingPredictionPaid sameAssociativeReadingPredictionUnpaid : DivinationCase

data DivinationSurface : Set where sameAssociativeDivinationSurface : DivinationSurface
data PredictionAudit : Set where predictiveEvidencePaid predictiveEvidenceOpen : PredictionAudit

divinationSurface : DivinationCase → DivinationSurface
divinationSurface _ = sameAssociativeDivinationSurface

predictionAudit : DivinationCase → PredictionAudit
predictionAudit sameAssociativeReadingPredictionPaid = predictiveEvidencePaid
predictionAudit sameAssociativeReadingPredictionUnpaid = predictiveEvidenceOpen

divinationPredictionDefect : INF.NonFactorabilityWitness divinationSurface predictionAudit
divinationPredictionDefect = INF.nonFactorabilityWitness
  sameAssociativeReadingPredictionPaid sameAssociativeReadingPredictionUnpaid refl (λ ())

divinationPracticeCannotFactorPredictiveValidity :
  INF.FactorsThrough divinationSurface predictionAudit → ⊥
divinationPracticeCannotFactorPredictiveValidity =
  INF.witnessRulesOutEveryFlatFactorisation divinationPredictionDefect

------------------------------------------------------------------------
-- Existing repo owners are inherited rather than duplicated.
------------------------------------------------------------------------

witchUseBoundary : INF.FactorsThrough Witch.witchSentence Witch.witchUse → ⊥
witchUseBoundary = Witch.sameSentenceCannotRecoverUse

yijingBoundary : Yijing.TernaryDivinationBoundary
yijingBoundary = Yijing.canonicalTernaryDivinationBoundary

yijingRelationalBoundary : YijingRelational.YijingRelationalBoundary
yijingRelationalBoundary = YijingRelational.canonicalYijingRelationalBoundary

psychogeographicBoundary : Psychogeographic.PsychogeographicHexagramBoundary
psychogeographicBoundary = Psychogeographic.canonicalPsychogeographicHexagramBoundary

ritualBoundary : Ritual.RitualMythCommunityInstitutionBoundary
ritualBoundary = Ritual.canonicalRitualMythCommunityInstitutionBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints into broader Ibrahim nodes.
------------------------------------------------------------------------

record SymbolicPracticeReverseConstraint : Set where
  constructor symbolic-practice-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SymbolicPracticeReverseConstraint public

religionConstraint : SymbolicPracticeReverseConstraint
religionConstraint = symbolic-practice-reverse-constraint
  "Religion / ritual"
  "text, cast, ritual procedure, self-description, affiliation, metaphysical commitment, community membership and authority remain distinct"
  false

knowledgeConstraint : SymbolicPracticeReverseConstraint
knowledgeConstraint = symbolic-practice-reverse-constraint
  "Knowledge / prediction"
  "symbolic association, historical interpretation, introspective prompt and externally testable prediction remain different evidence roles"
  false

anthropologyConstraint : SymbolicPracticeReverseConstraint
anthropologyConstraint = symbolic-practice-reverse-constraint
  "Anthropology / culture"
  "emic interpretation, observer description, translation, commentary lineage, practice and community authority remain separately attributable"
  false

historyConstraint : SymbolicPracticeReverseConstraint
historyConstraint = symbolic-practice-reverse-constraint
  "History / reception"
  "received text, later commentary, modern translation, modern reuse and present self-identification must retain temporal/source provenance"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data QiQidCreatesPhysicalMechanism : Set where
data YijingQidCreatesPrediction : Set where
data HexagramCreatesOneTimelessMeaning : Set where
data DivinationPracticeCreatesPredictiveValidity : Set where
data WitchcraftQidCreatesWiccanAffiliation : Set where
data WiccaQidCreatesWitchSelfIdentification : Set where
data TraditionalVocabularyCreatesModernScientificEquivalence : Set where

qiQidDoesNotCreatePhysicalMechanism : QiQidCreatesPhysicalMechanism → ⊥
qiQidDoesNotCreatePhysicalMechanism ()

yijingQidDoesNotCreatePrediction : YijingQidCreatesPrediction → ⊥
yijingQidDoesNotCreatePrediction ()

hexagramDoesNotCreateOneTimelessMeaning : HexagramCreatesOneTimelessMeaning → ⊥
hexagramDoesNotCreateOneTimelessMeaning ()

divinationPracticeDoesNotCreatePredictiveValidity : DivinationPracticeCreatesPredictiveValidity → ⊥
divinationPracticeDoesNotCreatePredictiveValidity ()

witchcraftQidDoesNotCreateWiccanAffiliation : WitchcraftQidCreatesWiccanAffiliation → ⊥
witchcraftQidDoesNotCreateWiccanAffiliation ()

wiccaQidDoesNotCreateWitchSelfIdentification : WiccaQidCreatesWitchSelfIdentification → ⊥
wiccaQidDoesNotCreateWitchSelfIdentification ()

traditionalVocabularyDoesNotCreateModernScientificEquivalence : TraditionalVocabularyCreatesModernScientificEquivalence → ⊥
traditionalVocabularyDoesNotCreateModernScientificEquivalence ()

record QiHexagramWitchDivinationBoundary : Set where
  constructor qi-hexagram-witch-divination-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedWitchPersonIdentityRetained : Bool
    qiSemanticRoleRemainsSourceIndexed : Bool
    hexagramInterpretationRemainsContextIndexed : Bool
    symbolicReadingDoesNotCreatePredictiveValidity : Bool
    witchSelfDescriptionDoesNotDetermineAffiliation : Bool
    wiccaWitchcraftAndWitchSelfDescriptionSeparated : Bool
    receivedYijingAndDashiTernaryExtensionSeparated : Bool
    attributionAndTranslationHistoryRetained : Bool
    twoEyedEmicEticComparisonRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open QiHexagramWitchDivinationBoundary public

canonicalQiHexagramWitchDivinationBoundary : QiHexagramWitchDivinationBoundary
canonicalQiHexagramWitchDivinationBoundary =
  qi-hexagram-witch-divination-boundary true true true true true true true true true true true false
