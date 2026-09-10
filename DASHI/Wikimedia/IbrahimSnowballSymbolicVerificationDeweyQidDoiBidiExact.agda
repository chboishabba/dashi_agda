module DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballQiHexagramWitchDivinationBidiExact as Symbolic
import DASHI.Wikimedia.IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact as Verification

------------------------------------------------------------------------
-- IBRAHIM / DEWEY / DOI / QID / SNOWBALL BIDI WELD
--
-- Symbolic, ritual and divinatory objects can be culturally/historically
-- meaningful without thereby paying an empirical prediction consumer.
-- Verification can test empirical propositions without thereby adjudicating
-- the cultural or ritual meaning of the symbolic practice.
--
-- Dewey is retained as an external library-classification/navigation
-- coordinate.  DOI is source identity/provenance.  QID is entity/concept
-- identity/navigation.  None of the three creates semantic truth or authority.
------------------------------------------------------------------------

data DeweyResolution : Set where
  deweyVerified : String → String → DeweyResolution
  deweyUnresolved : String → DeweyResolution
  deweyNotApplicable : String → DeweyResolution

record DeweyCoordinate : Set where
  constructor dewey-coordinate
  field
    subjectLabel : String
    resolution : DeweyResolution
    sourceLabel : String
    classificationCreatesSemanticParent : Bool
    classificationCreatesTruth : Bool
open DeweyCoordinate public

mkVerifiedDewey : String → String → String → DeweyCoordinate
mkVerifiedDewey subject number source =
  dewey-coordinate subject (deweyVerified number source) source false false

mkUnresolvedDewey : String → String → DeweyCoordinate
mkUnresolvedDewey subject reason =
  dewey-coordinate subject (deweyUnresolved reason) reason false false

-- Externally inspected DDC coordinates.  These are navigation/classification
-- observations, not claims that the classifications form the correct DASHI
-- dependency graph.

divinationDewey : DeweyCoordinate
divinationDewey = mkVerifiedDewey
  "divination"
  "133.3"
  "Wikidata Q1043197 DDC statement inspected 2026-09-11"

witchcraftDewey : DeweyCoordinate
witchcraftDewey = mkVerifiedDewey
  "witchcraft / magic neighbourhood"
  "133.43"
  "Wikidata witchcraft/magic DDC statement inspected 2026-09-11"

modernPaganismDewey : DeweyCoordinate
modernPaganismDewey = mkVerifiedDewey
  "modern paganism"
  "299.94"
  "Wikidata Q189753 DDC statement inspected 2026-09-11"

informationLiteracyDewey : DeweyCoordinate
informationLiteracyDewey = mkVerifiedDewey
  "information literacy"
  "028.7"
  "Wikidata Q679789 DDC statement inspected 2026-09-11"

yijingDewey : DeweyCoordinate
yijingDewey = mkUnresolvedDewey
  "I Ching / Yijing"
  "no exact inspected DDC value promoted in this pass"

qiDewey : DeweyCoordinate
qiDewey = mkUnresolvedDewey
  "qi"
  "no exact inspected DDC value promoted in this pass"

factCheckingDewey : DeweyCoordinate
factCheckingDewey = mkUnresolvedDewey
  "fact-checking"
  "no exact inspected DDC value promoted in this pass"

sourceCriticismDewey : DeweyCoordinate
sourceCriticismDewey = mkUnresolvedDewey
  "source criticism"
  "no exact inspected DDC value promoted in this pass"

mediaLiteracyDewey : DeweyCoordinate
mediaLiteracyDewey = mkUnresolvedDewey
  "media literacy"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- QID continuation.  Reuse existing paid identities and add information
-- literacy, which is useful for the verification branch.
------------------------------------------------------------------------

qiQid : Identity.ExternalIdentityDemand
qiQid = Symbolic.qiQid

yijingQid : Identity.ExternalIdentityDemand
yijingQid = Symbolic.yijingQid

hexagramQid : Identity.ExternalIdentityDemand
hexagramQid = Symbolic.hexagramQid

divinationQid : Identity.ExternalIdentityDemand
divinationQid = Symbolic.divinationQid

witchcraftQid : Identity.ExternalIdentityDemand
witchcraftQid = Symbolic.witchcraftQid

wiccaQid : Identity.ExternalIdentityDemand
wiccaQid = Symbolic.wiccaQid

factCheckingQid : Identity.ExternalIdentityDemand
factCheckingQid = Verification.factCheckingQid

verificationQid : Identity.ExternalIdentityDemand
verificationQid = Verification.verificationQid

sourceCriticismQid : Identity.ExternalIdentityDemand
sourceCriticismQid = Verification.sourceCriticismQid

mediaLiteracyQid : Identity.ExternalIdentityDemand
mediaLiteracyQid = Verification.mediaLiteracyQid

informationLiteracyQid : Identity.ExternalIdentityDemand
informationLiteracyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim symbolic/verification Dewey-QID-DOI BIDI"
  "verified external identity only"
  "information literacy"
  Identity.wikidataQid
  (Identity.verified "Q679789"
    "Wikidata identity inspected 2026-09-11; identity does not create discernment, truth or authority")

------------------------------------------------------------------------
-- Additional attributed scholarship paying the anthropology/verification seam.
------------------------------------------------------------------------

espiritoSantoDivinationSource : Attribution.AttributedSource
espiritoSantoDivinationSource = Attribution.mkDOISource
  "Diana Espirito Santo"
  "Divination"
  "Open Encyclopedia of Anthropology"
  "2019/2023"
  "10.29164/19divination"
  "https://doi.org/10.29164/19divination"
  Attribution.academicArticleSource
  "anthropological overview of divination as varied cultural practice and interpretive technique; does not establish supernatural or predictive validity"
  Attribution.publicAttribution

niehausWitchcraftSource : Attribution.AttributedSource
niehausWitchcraftSource = Attribution.mkDOISource
  "Isak Niehaus"
  "Magic and Witchcraft: Changing Anthropological Interpretations"
  "The Oxford Handbook of the Anthropology of Religion"
  "2026"
  "10.1093/9780191822285.003.0021"
  "https://doi.org/10.1093/9780191822285.003.0021"
  Attribution.academicChapterSource
  "history of anthropological approaches to magic and witchcraft across symbolic, psychological, social, political and economic interpretations; not an empirical proof of supernatural causation"
  Attribution.publicAttribution

porterWoodCorrectionSource : Attribution.AttributedSource
porterWoodCorrectionSource = Attribution.mkDOISource
  "Ethan Porter; Thomas J. Wood"
  "Factual corrections: Concerns and current evidence"
  "Current Opinion in Psychology 55, 101715"
  "2024"
  "10.1016/j.copsyc.2023.101715"
  "https://doi.org/10.1016/j.copsyc.2023.101715"
  Attribution.academicArticleSource
  "review finding factual corrections generally improve belief accuracy while downstream attitude and behaviour effects are more limited; correction is not equivalent to complete belief or policy revision"
  Attribution.publicAttribution

factCheckingLiteracySource : Attribution.AttributedSource
factCheckingLiteracySource = Attribution.mkDOISource
  "authors as published"
  "Debunking fake news on social media: Immediate and short-term effects of fact-checking and media literacy interventions"
  "Journal of Public Economics 245, 105345"
  "2025"
  "10.1016/j.jpubeco.2025.105345"
  "https://doi.org/10.1016/j.jpubeco.2025.105345"
  Attribution.academicArticleSource
  "randomized survey experiment distinguishing item-specific fact-checking effects from more general media-literacy skill effects; does not guarantee correct judgment for every item"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: Dewey classification cannot recover semantic/evidentiary role.
------------------------------------------------------------------------

data ClassifiedCase : Set where
  sameDeweyCulturalPractice sameDeweyEmpiricalPredictionClaim : ClassifiedCase

data DeweySurface : Set where sameDeweyNeighbourhood : DeweySurface
data ConsumerRole : Set where culturalInterpretiveRole empiricalPredictionRole : ConsumerRole

deweySurface : ClassifiedCase → DeweySurface
deweySurface _ = sameDeweyNeighbourhood

consumerRole : ClassifiedCase → ConsumerRole
consumerRole sameDeweyCulturalPractice = culturalInterpretiveRole
consumerRole sameDeweyEmpiricalPredictionClaim = empiricalPredictionRole

deweyRoleDefect : INF.NonFactorabilityWitness deweySurface consumerRole
deweyRoleDefect = INF.nonFactorabilityWitness
  sameDeweyCulturalPractice sameDeweyEmpiricalPredictionClaim refl (λ ())

deweyClassificationCannotFactorConsumerRole :
  INF.FactorsThrough deweySurface consumerRole → ⊥
deweyClassificationCannotFactorConsumerRole =
  INF.witnessRulesOutEveryFlatFactorisation deweyRoleDefect

------------------------------------------------------------------------
-- Regression 2: cultural/symbolic meaning cannot factor empirical validity.
------------------------------------------------------------------------

data MeaningCase : Set where
  sameMeaningPredictionSupported sameMeaningPredictionUnsupported : MeaningCase

data MeaningSurface : Set where sameSituatedMeaning : MeaningSurface
data EmpiricalStatus : Set where empiricalSupportPaid empiricalSupportOpen : EmpiricalStatus

meaningSurface : MeaningCase → MeaningSurface
meaningSurface _ = sameSituatedMeaning

empiricalStatus : MeaningCase → EmpiricalStatus
empiricalStatus sameMeaningPredictionSupported = empiricalSupportPaid
empiricalStatus sameMeaningPredictionUnsupported = empiricalSupportOpen

meaningEmpiricalDefect : INF.NonFactorabilityWitness meaningSurface empiricalStatus
meaningEmpiricalDefect = INF.nonFactorabilityWitness
  sameMeaningPredictionSupported sameMeaningPredictionUnsupported refl (λ ())

symbolicMeaningCannotFactorEmpiricalValidity :
  INF.FactorsThrough meaningSurface empiricalStatus → ⊥
symbolicMeaningCannotFactorEmpiricalValidity =
  INF.witnessRulesOutEveryFlatFactorisation meaningEmpiricalDefect

------------------------------------------------------------------------
-- Regression 3: empirical verification status cannot recover cultural meaning.
------------------------------------------------------------------------

data VerificationCase : Set where
  sameVerificationStatusMeaningA sameVerificationStatusMeaningB : VerificationCase

data VerificationSurface : Set where sameEmpiricalVerificationStatus : VerificationSurface
data CulturalMeaning : Set where ritualMeaningA ritualMeaningB : CulturalMeaning

verificationSurface : VerificationCase → VerificationSurface
verificationSurface _ = sameEmpiricalVerificationStatus

culturalMeaning : VerificationCase → CulturalMeaning
culturalMeaning sameVerificationStatusMeaningA = ritualMeaningA
culturalMeaning sameVerificationStatusMeaningB = ritualMeaningB

verificationMeaningDefect : INF.NonFactorabilityWitness verificationSurface culturalMeaning
verificationMeaningDefect = INF.nonFactorabilityWitness
  sameVerificationStatusMeaningA sameVerificationStatusMeaningB refl (λ ())

verificationCannotFactorCulturalMeaning :
  INF.FactorsThrough verificationSurface culturalMeaning → ⊥
verificationCannotFactorCulturalMeaning =
  INF.witnessRulesOutEveryFlatFactorisation verificationMeaningDefect

------------------------------------------------------------------------
-- Reuse prior exact boundaries instead of forking their ontologies.
------------------------------------------------------------------------

symbolicBoundary : Symbolic.QiHexagramWitchDivinationBoundary
symbolicBoundary = Symbolic.canonicalQiHexagramWitchDivinationBoundary

verificationBoundary : Verification.FactCheckingVerificationMediaLiteracyCorrectionBoundary
verificationBoundary = Verification.canonicalFactCheckingVerificationMediaLiteracyCorrectionBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints back into Ibrahim/Dewey parent nodes.
------------------------------------------------------------------------

record DeweySnowballReverseConstraint : Set where
  constructor dewey-snowball-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open DeweySnowballReverseConstraint public

religionCultureConstraint : DeweySnowballReverseConstraint
religionCultureConstraint = dewey-snowball-reverse-constraint
  "Religion / culture / anthropology"
  "ritual practice, received text, symbolic interpretation, self-description, historical source role and empirical prediction remain separate"
  false

knowledgeScienceConstraint : DeweySnowballReverseConstraint
knowledgeScienceConstraint = dewey-snowball-reverse-constraint
  "Knowledge / science"
  "meaning, proposition identity, evidence, verification method, uncertainty and correction history remain separate"
  false

libraryInformationConstraint : DeweySnowballReverseConstraint
libraryInformationConstraint = dewey-snowball-reverse-constraint
  "Library and information science"
  "Dewey shelf/classification, QID identity, DOI source identity, source criticism, media literacy and truth status remain different coordinates"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data DeweyCreatesSemanticParent : Set where
data DeweyCreatesTruth : Set where
data QidCreatesDewey : Set where
data DOIIdentifiesConcept : Set where
data SymbolicMeaningCreatesPrediction : Set where
data VerificationErasesCulturalMeaning : Set where

deweyDoesNotCreateSemanticParent : DeweyCreatesSemanticParent → ⊥
deweyDoesNotCreateSemanticParent ()

deweyDoesNotCreateTruth : DeweyCreatesTruth → ⊥
deweyDoesNotCreateTruth ()

qidDoesNotCreateDewey : QidCreatesDewey → ⊥
qidDoesNotCreateDewey ()

doiDoesNotIdentifyConcept : DOIIdentifiesConcept → ⊥
doiDoesNotIdentifyConcept ()

symbolicMeaningDoesNotCreatePrediction : SymbolicMeaningCreatesPrediction → ⊥
symbolicMeaningDoesNotCreatePrediction ()

verificationDoesNotEraseCulturalMeaning : VerificationErasesCulturalMeaning → ⊥
verificationDoesNotEraseCulturalMeaning ()

record SymbolicVerificationDeweyQidDoiBoundary : Set where
  constructor symbolic-verification-dewey-qid-doi-boundary
  field
    deweyTravelsAsClassificationCoordinate : Bool
    doiTravelsAsSourceIdentity : Bool
    qidTravelsAsEntityIdentity : Bool
    unresolvedDeweyRetainedExplicitly : Bool
    deweyDoesNotCreateSemanticParent : Bool
    symbolicMeaningSeparatedFromEmpiricalPrediction : Bool
    verificationSeparatedFromCulturalMeaning : Bool
    sourceRoleAndAttributionTravel : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SymbolicVerificationDeweyQidDoiBoundary public

canonicalSymbolicVerificationDeweyQidDoiBoundary :
  SymbolicVerificationDeweyQidDoiBoundary
canonicalSymbolicVerificationDeweyQidDoiBoundary =
  symbolic-verification-dewey-qid-doi-boundary
    true true true true true true true true true false
